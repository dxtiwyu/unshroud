"""gen_mba.py: the mba suite, MBA-obfuscated functions with a simple ground truth.

usage: python -I suites/mba/gen_mba.py [--seed 7] [--no-validate] [--show NAME,NAME]
                                       [--only-gen] [--mem-mb 3072]
  runs selftest_mba.py (every rewrite rule on random inputs), writes suites/mba/mba.c,
  mba.dll, mba.map, mba.json, checks the code, then runs gen/validate.py --n 2000.
Reproducible: the same seed gives byte-identical mba.c, mba.json, mba.dll and mba.map (no
set iteration, no hash order; the linker's time stamp is pinned to 0 in the DLL and map).
Memory: the run and its children (clang, lld, validate.py) are capped by a Windows job
object (--mem-mb, commit charge); numpy is limited to one BLAS thread.

Each function computes one obfuscated expression (a tree; identical subtrees are computed
once, every operation gets its own BAR so clang cannot fold the identities back).
Checks: every tree against its truth on 256 inputs (numpy) and its printed form (truth);
no operation clang folds (on constants only, x & 0, x * 1, a ^ a after CSE, ...); in the
DLL no jcc / jmp / cmov / call, at least one instruction per compiled operation, and
instructions >= obf_nodes / 3 (a tree whose copies stay identical is retried, then
regenerated after the build, else dropped); llvm-objdump agrees with capstone on every
function (count, no branch), common.crosscheck_sizes on every export.
Categories (field "category"; the rewriting class is re-derived from the tree, "mba_class"):
  linear   linear MBA: + - and constant * over uniform bitwise terms of the variables
           (identities, null-space zeros, re-synthesis as sum a_i*e_i over unitriangular
           truth-table bases); no product of variables, no bitwise op over arithmetic.
  poly     polynomial MBA: also products of bitwise terms (x*y = (x&y)*(x|y) + (x&~y)*(~x&y),
           distribution, a*(b+k) - a*k, polynomial zeros) and invertible affine maps
           g(f(e)) = ainv*(a*e + b) - ainv*b (a odd) around subterms.
  nonpoly  simple truths, non-polynomial MBA: identities applied to arithmetic operands,
           masks e = (e&m)|(e&~m), splits e = (e-s)+s with s like ((y*k)&z), synthesis over
           arithmetic atoms; bitwise-over-arithmetic nesting >= 2 (field "mba_nesting").
  mixed    the truth itself mixes bitwise and arithmetic (2-3 levels), all rewrites.
  const    the output is a constant hidden by MBA (null-space zeros + K, or K synthesized
           as sum a_i*e_i(vars)); half with linear rewrites only, half with all rewrites.
difficulty = number of rewriting layers (1-4). Layer L rewrites only code that existed
before it (the code layer L-1 made first), each position at most once by an identity /
product rule / re-synthesis and at most once by a wrapper (zero insertion Z, affine AF,
mask MK, split SP: the wrapped code stays verbatim inside); code made by layer L is left
to layer L+1, so rewrites nest at most d deep. After the last layer, a poly tree without
a product gets a polynomial zero and a nonpoly tree with nesting < 2 a nesting wrapper.
Suite-specific json fields: obf = the obfuscated expression in the bench language (the
tree that was compiled); obf_nodes = its AST nodes (truth.nodes(obf)); obf_ops = distinct
operations compiled (the DAG: identical subtrees once); obf_depth = tree depth;
mba_class = linear / poly / nonpoly re-derived from the tree; mba_nesting = the most
bitwise-over-arithmetic edges on one root-to-leaf path (0 for linear and poly).
Linear and poly functions take >= 2 arguments (one-variable linear MBA is only x + ~x = -1).
"""
import argparse
import ast
import math
import os
import random
import statistics
import subprocess
import sys
import time
from collections import Counter
from fractions import Fraction

os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')    # numpy's BLAS commits ~35 MB per thread
import numpy as np                              # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
BENCH = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(BENCH, 'gen'))
import common                                   # noqa: E402
import truth                                    # noqa: E402

# ---------------------------------------------------------------- memory guard
# The machine is shared (16 GB, other heavy jobs). memory_guard puts this process in a
# Windows job object with a commit limit; the children it starts (clang, lld, validate.py)
# inherit the job, so a runaway allocation fails with MemoryError / an out-of-memory exit
# instead of exhausting the machine.
_JOB = []


def _job_api():
    import ctypes
    from ctypes import wintypes

    class Basic(ctypes.Structure):
        _fields_ = [('PerProcessUserTimeLimit', ctypes.c_int64), ('PerJobUserTimeLimit', ctypes.c_int64),
                    ('LimitFlags', wintypes.DWORD), ('MinimumWorkingSetSize', ctypes.c_size_t),
                    ('MaximumWorkingSetSize', ctypes.c_size_t), ('ActiveProcessLimit', wintypes.DWORD),
                    ('Affinity', ctypes.c_size_t), ('PriorityClass', wintypes.DWORD),
                    ('SchedulingClass', wintypes.DWORD)]

    class Ext(ctypes.Structure):
        _fields_ = [('Basic', Basic), ('Io', ctypes.c_uint64 * 6), ('ProcessMemoryLimit', ctypes.c_size_t),
                    ('JobMemoryLimit', ctypes.c_size_t), ('PeakProcessMemoryUsed', ctypes.c_size_t),
                    ('PeakJobMemoryUsed', ctypes.c_size_t)]
    k = ctypes.WinDLL('kernel32', use_last_error=True)
    k.CreateJobObjectW.restype = wintypes.HANDLE
    k.CreateJobObjectW.argtypes = [ctypes.c_void_p, ctypes.c_wchar_p]
    k.SetInformationJobObject.argtypes = [wintypes.HANDLE, ctypes.c_int, ctypes.c_void_p, wintypes.DWORD]
    k.QueryInformationJobObject.argtypes = [wintypes.HANDLE, ctypes.c_int, ctypes.c_void_p, wintypes.DWORD,
                                            ctypes.c_void_p]
    k.AssignProcessToJobObject.argtypes = [wintypes.HANDLE, wintypes.HANDLE]
    k.GetCurrentProcess.restype = wintypes.HANDLE
    return ctypes, k, Ext


def memory_guard(job_mb=3072, proc_mb=2560):
    """Limit the committed memory of this process (proc_mb) and of it plus its children
    (job_mb). Returns False (and changes nothing) when the job cannot be set up."""
    if os.name != 'nt' or _JOB:
        return bool(_JOB)
    try:
        ctypes, k, Ext = _job_api()
        h = k.CreateJobObjectW(None, None)
        info = Ext()
        info.Basic.LimitFlags = 0x200 | 0x100        # JOB_OBJECT_LIMIT_JOB_MEMORY | _PROCESS_MEMORY
        info.JobMemoryLimit = job_mb << 20
        info.ProcessMemoryLimit = proc_mb << 20
        if not h or not k.SetInformationJobObject(h, 9, ctypes.byref(info), ctypes.sizeof(info)):
            return False
        if not k.AssignProcessToJobObject(h, k.GetCurrentProcess()):
            return False
        _JOB.append((h, k, Ext, ctypes))
        return True
    except (OSError, AttributeError):
        return False


def memory_peaks():
    """(peak MB of the whole job, peak MB of one process) or None without a guard."""
    if not _JOB:
        return None
    h, k, Ext, ctypes = _JOB[0]
    q = Ext()
    k.QueryInformationJobObject(h, 9, ctypes.byref(q), ctypes.sizeof(q), None)
    return q.PeakJobMemoryUsed >> 20, q.PeakProcessMemoryUsed >> 20


SUITE = 'mba'
NL = chr(10)
M64 = (1 << 64) - 1
BIT = frozenset(['&', '|', '^', '~'])
ARI = frozenset(['+', '-', '*', 'neg', '<<'])
GEN = [0]                                       # generation stamped on new nodes


class N:
    """Expression node: op in v (variable), c (constant), p (placeholder of a bitwise
    pattern), ~ neg + - * & | ^ <<. Trees only (no node has two parents).
    g: the layer that made the node (0: the seed; -1: discarded); dn: the layer in which
    this position was wrapped (Z / AF / MK / SP keep the old node as their operand); rw:
    the layer in which this position's old code was rewritten (it may still be wrapped);
    pk: the operation of the parent (None at the root)."""
    __slots__ = ('op', 'k', 'v', 'g', 'pk', 'dn', 'rw')

    def __init__(self, op, k=(), v=None):
        self.op, self.k, self.v, self.g, self.pk, self.dn, self.rw = op, list(k), v, GEN[0], None, 0, 0
        for c in self.k:
            c.pk = op


def V(name):
    return N('v', v=name)


def C(val):
    return N('c', v=val & M64)


def P(i):
    return N('p', v=i)


def U(op, a):
    return N(op, [a])


def B(op, a, b):
    return N(op, [a, b])


def cp(n):
    m = N.__new__(N)
    m.op, m.v, m.g, m.pk, m.dn, m.rw = n.op, n.v, n.g, n.pk, n.dn, 0
    m.k = [cp(c) for c in n.k]
    return m


def detach(n):
    """A new node holding n's operation and kids (n itself is about to be replaced by code
    that uses it): marked as transformed in the current layer."""
    m = N.__new__(N)
    m.op, m.k, m.v, m.g, m.pk, m.dn, m.rw = n.op, n.k, n.v, n.g, n.pk, GEN[0], n.rw
    return m


def install(n, new):
    n.op, n.k, n.v, n.g = new.op, new.k, new.v, new.g


DISCARD = []                                    # nodes a pending rewrite drops (see rewrite)


def nb(a):
    """~a without a double NOT and without an operation on a constant."""
    if a.op == 'c':
        return C(a.v ^ M64)
    if a.op == '~':
        DISCARD.append(a)
        return a.k[0]
    return U('~', a)


COMM = frozenset(['+', '*', '&', '|', '^'])


def same(a, b):
    """a and b are the same expression (structurally, operands of + * & | ^ in any order)."""
    if a is b:
        return True
    if a.op != b.op or a.v != b.v or len(a.k) != len(b.k):
        return False
    if all(same(x, y) for x, y in zip(a.k, b.k)):
        return True
    return a.op in COMM and same(a.k[0], b.k[1]) and same(a.k[1], b.k[0])


def canon(n):
    """Printed form with the operands of + * & | ^ sorted: equal for commutative variants."""
    if not n.k:
        return show(n)
    ks = [canon(c) for c in n.k]
    if n.op in COMM:
        ks.sort()
    return '(' + n.op + ' ' + ' '.join(ks) + ')'


def compl(a, b):
    """a is ~b or b is ~a (an identity over them would make ~b & ~b, ...)."""
    return (a.op == '~' and same(a.k[0], b)) or (b.op == '~' and same(b.k[0], a))


def self_op(e):
    """e has a binary operation whose two operands are the same expression (a & a, a - a)."""
    return any(len(m.k) == 2 and same(m.k[0], m.k[1]) for m in walk(e))


def ops(n):
    return 1 + sum(ops(c) for c in n.k) if n.k else 0


def depth(n):
    return 1 + max(depth(c) for c in n.k) if n.k else 1


def walk(n, out=None):
    out = [] if out is None else out
    out.append(n)
    for c in n.k:
        walk(c, out)
    return out


def sgn(v):
    v &= M64
    return v - (1 << 64) if v >> 63 else v


def lit(v):
    return str(v) if v < 65536 else hex(v)


def show(n):
    op = n.op
    if op == 'v':
        return n.v
    if op == 'c':
        return lit(n.v)
    if op == 'p':
        return 'p' + str(n.v)
    if op == '~':
        return '(~' + show(n.k[0]) + ')'
    if op == 'neg':
        return '(-' + show(n.k[0]) + ')'
    return '(' + show(n.k[0]) + ' ' + op + ' ' + show(n.k[1]) + ')'


_AST = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.BitAnd: '&', ast.BitOr: '|',
        ast.BitXor: '^', ast.LShift: '<<'}


def from_str(s):
    def g(a):
        t = type(a)
        if t is ast.Name:
            return V(a.id)
        if t is ast.Constant:
            return C(a.value)
        if t is ast.UnaryOp:
            return U('~' if type(a.op) is ast.Invert else 'neg', g(a.operand))
        return B(_AST[type(a.op)], g(a.left), g(a.right))
    return g(ast.parse(s, mode='eval').body)


def ev(n, env, ov=None):
    """numpy uint64 evaluation; env: name / placeholder index -> array; ov: id(node) -> array."""
    if ov is not None and id(n) in ov:
        return ov[id(n)]
    op = n.op
    if op == 'v' or op == 'p':
        return env[n.v]
    if op == 'c':
        return np.full(env['_n'], n.v, dtype=np.uint64)
    a = ev(n.k[0], env, ov)
    if op == '~':
        return ~a
    if op == 'neg':
        return np.uint64(0) - a
    b = ev(n.k[1], env, ov)
    if op == '+':
        return a + b
    if op == '-':
        return a - b
    if op == '*':
        return a * b
    if op == '&':
        return a & b
    if op == '|':
        return a | b
    if op == '^':
        return a ^ b
    return a << b                                   # '<<' by a constant below 64


# ---------------------------------------------------------------- bitwise patterns over p0..p(t-1)
_PM = {}
POOL = {}


def pmask(t, i):
    """Truth table bit c (corner c: p_j = bit j of c) of the placeholder p_i."""
    key = (t, i)
    if key not in _PM:
        _PM[key] = sum(1 << c for c in range(1 << t) if c >> i & 1)
    return _PM[key]


def full_tt(t):
    return (1 << (1 << t)) - 1


def tt_of(e, t):
    op = e.op
    if op == 'p':
        return pmask(t, e.v)
    if op == '~':
        return tt_of(e.k[0], t) ^ full_tt(t)
    a, b = tt_of(e.k[0], t), tt_of(e.k[1], t)
    return a & b if op == '&' else (a | b if op == '|' else a ^ b)


def rand_bexpr(r, t, d):
    if d == 0 or r.random() < 0.25:
        e = P(r.randrange(t))
        return U('~', e) if r.random() < 0.3 else e
    op = r.choice('&|^&|^~')
    if op == '~':
        return nb(rand_bexpr(r, t, d - 1))
    a, b = rand_bexpr(r, t, d - 1), rand_bexpr(r, t, d - 1)
    if show(a) == show(b):
        return a
    return B(op, a, b)


def pool(t):
    """([(tt, pattern)], {tt: [pattern]}) of small random bitwise patterns (fixed seed)."""
    if t not in POOL:
        r = random.Random(1000 + t)
        lst, by, seen = [], {}, set()
        for _ in range(300 if t == 1 else 5000):
            e = rand_bexpr(r, t, r.randint(1, 3))
            s = canon(e)
            if s in seen or ops(e) > 5 or self_op(e) or tautology(e, t):
                continue
            seen.add(s)
            tt = tt_of(e, t)
            if tt in (0, full_tt(t)):
                continue
            lst.append((tt, e))
            by.setdefault(tt, []).append(e)
        POOL[t] = (lst, by)
    return POOL[t]


def tautology(e, t):
    """e has a part with a constant truth table (x & ~x, x | ~x, ...): local rules fold it."""
    return any(m.k and tt_of(m, t) in (0, full_tt(t)) for m in walk(e))


def cof(tt, t, i, val):
    out = 0
    for c in range(1 << t):
        src = c | (1 << i) if val else c & ~(1 << i)
        if tt >> src & 1:
            out |= 1 << c
    return out


def bexpr(tt, t, r):
    """A random bitwise pattern with truth table tt (not constant): pool, else Shannon."""
    full = full_tt(t)
    cands = pool(t)[1].get(tt)
    if cands:
        return r.choice(cands)
    dep = [i for i in range(t) if cof(tt, t, i, 1) != cof(tt, t, i, 0)]
    i = r.choice(dep)
    g1, g0 = cof(tt, t, i, 1), cof(tt, t, i, 0)
    if g0 == 0:
        return P(i) if g1 == full else B('&', P(i), bexpr(g1, t, r))
    if g1 == 0:
        return U('~', P(i)) if g0 == full else B('&', U('~', P(i)), bexpr(g0, t, r))
    if g0 == full:
        return B('|', U('~', P(i)), bexpr(g1, t, r))
    if g1 == full:
        return B('|', P(i), bexpr(g0, t, r))
    if g1 ^ g0 == full:                             # g1 = ~g0
        return B('^', P(i), bexpr(g0, t, r))
    if r.random() < 0.5:
        return B('|', B('&', P(i), bexpr(g1, t, r)), B('&', U('~', P(i)), bexpr(g0, t, r)))
    return B('^', B('&', P(i), bexpr(g1 ^ g0, t, r)), bexpr(g0, t, r))


def nullspace(cols, m):
    """Integer basis of {a : sum_j a_j * bit_c(cols[j]) == 0 for every corner c < m}."""
    n = len(cols)
    A = [[Fraction(cols[j] >> c & 1) for j in range(n)] for c in range(m)]
    piv, row = [], 0
    for col in range(n):
        p = next((i for i in range(row, m) if A[i][col] != 0), None)
        if p is None:
            continue
        A[row], A[p] = A[p], A[row]
        pv = A[row][col]
        A[row] = [x / pv for x in A[row]]
        for i in range(m):
            if i != row and A[i][col] != 0:
                f = A[i][col]
                A[i] = [x - f * y for x, y in zip(A[i], A[row])]
        piv.append(col)
        row += 1
        if row == m:
            break
    basis = []
    for fj in [j for j in range(n) if j not in piv]:
        v = [Fraction(0)] * n
        v[fj] = Fraction(1)
        for i, pj in enumerate(piv):
            v[pj] = -A[i][fj]
        den = 1
        for x in v:
            den = den * x.denominator // math.gcd(den, x.denominator)
        iv = [int(x * den) for x in v]
        g = 0
        for x in iv:
            g = math.gcd(g, abs(x))
        basis.append([x // g for x in iv])
    return basis


def corner_sum(terms, t, c):
    return sum(k * (1 if e is None else tt_of(e, t) >> c & 1) for k, e in terms)


def zero_terms(t, r):
    """[(coef, pattern or None)] with sum coef * pattern == 0 at every corner (None is the
    all-ones function, i.e. the constant -1): an integer null-space vector."""
    lst = pool(t)[0]
    m = 1 << t
    for _ in range(200):
        if t <= 3 and r.random() < 0.5:
            es = [r.choice(lst)[1] for _ in range(m + r.randint(1, 2) if t > 1 else 3)]
        else:
            u, v = r.choice(lst)[1], r.choice(lst)[1]
            if tt_of(u, t) == tt_of(v, t):
                continue
            der = [B('|', u, v), B('&', u, v), B('^', u, v), B('&', u, nb(v)), B('&', nb(u), v),
                   nb(B('|', u, v)), nb(B('&', u, v)), nb(u), B('|', u, nb(v))]
            der = [e for e in der if not self_op(e) and not tautology(e, t)]  # v = ~u: u & u, u | ~u
            if len(der) < 2:
                continue
            es = [u, v] + r.sample(der, r.randint(2, min(4, len(der))))
        es = list({canon(e): e for e in es}.values())       # the same pattern twice gives e - e
        cols = [tt_of(e, t) for e in es]
        if r.random() < 0.35:
            es.append(None)
            cols.append(full_tt(t))
        basis = nullspace(cols, m)
        if not basis:
            continue
        coef = [0] * len(es)
        for b in basis:
            k = r.choice([-2, -1, 1, 1, 2])
            coef = [x + k * y for x, y in zip(coef, b)]
        g = 0
        for x in coef:
            g = math.gcd(g, abs(x))
        if g == 0:
            continue
        terms = [(x // g, e) for x, e in zip(coef, es) if x]
        if sum(1 for k, e in terms if e is not None) < 2 or max(abs(k) for k, e in terms) > 64:
            continue
        assert all(corner_sum(terms, t, c) == 0 for c in range(m))
        return terms
    raise RuntimeError('no zero found')


def synth_terms(F, t, r):
    """[(coef, pattern or None)] with sum coef * pattern(corner c) == F[c] mod 2**64: a random
    unitriangular basis of truth tables (det 1, so integer coefficients) plus 0-2 extra terms."""
    m = 1 << t
    perm = list(range(m))
    r.shuffle(perm)
    cols = []
    for j in range(m):
        tt = 1 << perm[j]
        for i in range(j + 1, m):
            if r.random() < 0.5:
                tt |= 1 << perm[i]
        cols.append(tt)
    extra = [(r.choice([-3, -2, -1, 1, 2, 3]), r.choice(pool(t)[0])[1]) for _ in range(r.randint(0, 2))]
    R = [F[c] - corner_sum(extra, t, c) for c in range(m)]
    a = []
    for j in range(m):
        c = perm[j]
        a.append(sgn(R[c] - sum(a[i] * (cols[i] >> c & 1) for i in range(j))))
    terms = [(a[j], None if cols[j] == full_tt(t) else bexpr(cols[j], t, r)) for j in range(m)] + extra
    terms = [(k, e) for k, e in terms if k]
    assert all((corner_sum(terms, t, c) - F[c]) % (1 << 64) == 0 for c in range(m))
    return terms


def inst(e, atoms):
    """A real tree from pattern e: placeholder i -> a fresh copy of atoms[i]."""
    if e.op == 'p':
        return cp(atoms[e.v])
    return N(e.op, [inst(c, atoms) for c in e.k], e.v)


def build_sum(terms, atoms, r):
    """sum coef * inst(pattern) (None: the constant -1); coefficients read as signed; the
    coefficients of a pattern that occurs twice are added (2*e - 2*e would be a - a)."""
    const, merged = 0, {}
    for k, e in terms:
        k = sgn(k)
        if e is None:
            const -= k
        elif k:
            merged.setdefault(canon(e), [0, e])[0] += k
    parts = [(sgn(k), e) for k, e in merged.values() if sgn(k)]
    r.shuffle(parts)
    parts.sort(key=lambda p: p[0] < 0)               # a positive term first when there is one
    acc = None
    for k, e in parts:
        x = inst(e, atoms)
        if abs(k) != 1:
            x = B('*', C(abs(k)), x) if r.random() < 0.6 else B('*', x, C(abs(k)))
        if acc is None:
            acc = x if k > 0 else U('neg', x)
        else:
            acc = B('+' if k > 0 else '-', acc, x)
    if acc is None:                                 # nothing but a constant: not an MBA
        return None
    const = sgn(const)
    if const:
        acc = B('+', acc, C(const)) if const > 0 else B('-', acc, C(-const))
    return acc


def rand_const(r, odd=False):
    while True:
        k = r.getrandbits(64) if r.random() < 0.5 else r.getrandbits(r.choice([8, 16, 32]))
        if odd:
            k |= 1
        if k not in (0, 1, M64):
            return k


def small_term(fv, r, deep):
    """A small variable-dependent term; deep: bitwise over arithmetic, e.g. ((y * k) & z)."""
    op = r.choice('+-*')
    a = B(op, V(r.choice(fv)), C(rand_const(r, op == '*')))
    if not deep:
        return a if r.random() < 0.7 else V(r.choice(fv))
    return B(r.choice('&|^'), a, V(r.choice(fv)))


def bw(n):
    return n.op == 'v' or n.op in BIT


def bit_pure(n):
    return n.op == 'v' or (n.op in BIT and all(bit_pure(c) for c in n.k))


def lin_uniform(n):
    """n is sum a_i * (uniform bitwise term of the variables) + constant."""
    op = n.op
    if op in ('v', 'c'):
        return True
    if op in BIT:
        return bit_pure(n)
    if op in ('+', '-'):
        return lin_uniform(n.k[0]) and lin_uniform(n.k[1])
    if op in ('neg', '<<'):
        return lin_uniform(n.k[0])
    a, b = n.k                                          # '*'
    return (a.op == 'c' and lin_uniform(b)) or (b.op == 'c' and lin_uniform(a))


# ---------------------------------------------------------------- identities on kids (a, b)
# flags: ax = the result is arithmetic (linear / poly: the node must not sit under a bitwise
# op), bwa / bwb = a bitwise op is applied to a / b (linear / poly: a / b bitwise-pure),
# np = bitwise over arithmetic by itself, dup = copies a / b.
def _r(flags, f):
    return (frozenset(flags.split()), f)


RW = {
    '+': {'A1': _r('bwa bwb dup', lambda a, b: B('+', B('^', a, b), B('*', C(2), B('&', cp(a), cp(b))))),
          'A2': _r('bwa bwb dup', lambda a, b: B('+', B('|', a, b), B('&', cp(a), cp(b)))),
          'A3': _r('bwa bwb dup', lambda a, b: B('-', B('*', C(2), B('|', a, b)), B('^', cp(a), cp(b)))),
          'A4': _r('bwb', lambda a, b: B('-', B('-', a, nb(b)), C(1))),
          'A5': _r('np', lambda a, b: U('~', B('-', nb(a), b))),
          'A6': _r('bwa bwb dup', lambda a, b: B('+', B('+', B('^', a, nb(b)), B('*', C(2), B('|', cp(a), cp(b)))), C(1))),
          'A7': _r('bwa bwb dup', lambda a, b: B('+', B('+', B('&', a, nb(b)), B('&', nb(cp(a)), cp(b))),
                                                B('*', C(2), B('&', cp(a), cp(b))))),
          'A8': _r('np dup', lambda a, b: B('+', B('^', a, b), B('<<', B('&', cp(a), cp(b)), C(1))))},
    '-': {'S1': _r('bwb', lambda a, b: B('+', B('+', a, nb(b)), C(1))),
          'S2': _r('bwa bwb dup', lambda a, b: B('-', B('^', a, b), B('*', C(2), B('&', nb(cp(a)), cp(b))))),
          'S3': _r('bwa bwb dup', lambda a, b: B('-', B('&', a, nb(b)), B('&', nb(cp(a)), cp(b)))),
          'S4': _r('np', lambda a, b: U('~', B('+', nb(a), b))),
          'S5': _r('bwa bwb dup', lambda a, b: B('-', B('*', C(2), B('&', a, nb(b))), B('^', cp(a), cp(b))))},
    '^': {'X1': _r('ax dup', lambda a, b: B('-', B('|', a, b), B('&', cp(a), cp(b)))),
          'X2': _r('dup', lambda a, b: B('|', B('&', a, nb(b)), B('&', nb(cp(a)), cp(b)))),
          'X3': _r('dup', lambda a, b: B('&', B('|', a, b), nb(B('&', cp(a), cp(b))))),
          'X4': _r('ax dup', lambda a, b: B('+', B('&', a, nb(b)), B('&', nb(cp(a)), cp(b)))),
          'X5': _r('ax dup', lambda a, b: B('-', B('+', a, b), B('*', C(2), B('&', cp(a), cp(b))))),
          'X6': _r('dup', lambda a, b: B('^', B('|', a, b), B('&', cp(a), cp(b))))},
}
RW.update({
    '&': {'N1': _r('ax dup', lambda a, b: B('-', B('+', a, b), B('|', cp(a), cp(b)))),
          'N2': _r('ax dup', lambda a, b: B('-', B('|', a, b), B('^', cp(a), cp(b)))),
          'N3': _r('', lambda a, b: nb(B('|', nb(a), nb(b)))),
          'N4': _r('ax dup', lambda a, b: B('-', B('|', nb(a), b), nb(cp(a)))),
          'N5': _r('dup', lambda a, b: B('^', B('|', a, b), B('^', cp(a), cp(b)))),
          'N6': _r('dup', lambda a, b: B('&', B('|', a, nb(b)), cp(b)))},
    '|': {'O1': _r('ax dup', lambda a, b: B('+', B('^', a, b), B('&', cp(a), cp(b)))),
          'O2': _r('ax dup', lambda a, b: B('+', B('&', a, nb(b)), cp(b))),
          'O3': _r('', lambda a, b: nb(B('&', nb(a), nb(b)))),
          'O4': _r('ax dup', lambda a, b: B('-', B('+', a, b), B('&', cp(a), cp(b)))),
          'O5': _r('dup', lambda a, b: B('^', B('&', a, nb(b)), cp(b))),
          'O6': _r('dup', lambda a, b: B('|', B('^', a, b), B('&', cp(a), cp(b))))},
    '~': {'T1': _r('ax', lambda a, b: B('-', U('neg', a), C(1))),
          'T2': _r('ax', lambda a, b: B('-', C(M64), a)),
          'T3': _r('np', lambda a, b: B('^', a, C(M64)))},          # T4: r_not_split
    'neg': {'G1': _r('bwa', lambda a, b: B('+', nb(a), C(1))),
            'G2': _r('np', lambda a, b: U('~', B('-', a, C(1)))),
            'G3': _r('bwa', lambda a, b: B('-', nb(a), C(M64)))},
    '*': {'M1': _r('bwa bwb dup poly', lambda a, b: B('+', B('*', B('&', a, b), B('|', cp(a), cp(b))),
                                                     B('*', B('&', cp(a), nb(cp(b))), B('&', nb(cp(a)), cp(b)))))},
})


def r_mul2(a, b, r):
    """a * b = a * (b + k) - a * k   (k a constant)."""
    k = rand_const(r)
    return B('-', B('*', a, B('+', b, C(k))), B('*', cp(a), C(k)))


def r_dist(a, b, r):
    """(a1 +- a2) * b = a1 * b +- a2 * b."""
    if a.op not in ('+', '-'):
        a, b = b, a
    DISCARD.append(a)
    return B(a.op, B('*', a.k[0], b), B('*', a.k[1], cp(b)))


def r_not_split(a, v, r):
    """~a = ~(a | v) + (~a & v) for a variable v (the two terms have disjoint bits)."""
    v = V(v)
    return B('+', nb(B('|', a, v)), B('&', nb(cp(a)), cp(v)))


def r_ksplit(a, b, r):
    """k * e = k1 * e + (k - k1) * e."""
    if a.op != 'c':
        a, b = b, a
    while True:
        k1 = rand_const(r) if r.random() < 0.4 else r.randint(2, 99)
        k2 = (a.v - k1) & M64
        if k2 not in (0, 1):
            return B('+', B('*', C(k1), b), B('*', C(k2), cp(b)))


# ---------------------------------------------------------------- rewrites of a whole node e
def r_affine(e, r):
    """g(f(e)) with f(v) = a*v + b (a odd), g(u) = ainv*u - ainv*b."""
    a = rand_const(r, odd=True)
    ai = pow(a, -1, 1 << 64)
    b = rand_const(r)
    inner = B('+', B('*', C(a), e), C(b)) if r.random() < 0.5 else B('+', C(b), B('*', e, C(a)))
    outer = B('*', C(ai), inner) if r.random() < 0.5 else B('*', inner, C(ai))
    return B('+', outer, C(-ai * b))


def r_mask(e, r):
    """(e & m) | (e & ~m), (e & m) + (e & ~m), (e | m) - (~e & m), ((e ^ m) + 2*(e & m)) - m."""
    m = rand_const(r)
    j = r.randrange(4)
    if j == 0:
        return B('|', B('&', e, C(m)), B('&', cp(e), C(~m)))
    if j == 1:
        return B('+', B('&', e, C(m)), B('&', cp(e), C(~m)))
    if j == 2:
        return B('-', B('|', e, C(m)), B('&', nb(cp(e)), C(m)))
    return B('-', B('+', B('^', e, C(m)), B('*', C(2), B('&', cp(e), C(m)))), C(m))


def r_split(e, r, fv):
    """e = (e - s) + s, (e + s) - s, (e ^ s) ^ s, (e | s) - (~e & s), (e & s) + (e & ~s)."""
    s = small_term(fv, r, r.random() < 0.6)
    if same(s, e) or compl(s, e):                   # s = e would give e & e, e - e
        s = small_term(fv, r, True)
    j = r.randrange(5)
    if j == 0:
        return B('+', B('-', e, s), cp(s))
    if j == 1:
        return B('-', B('+', e, s), cp(s))
    if j == 2:
        return B('^', B('^', e, s), cp(s))
    if j == 3:
        return B('-', B('|', e, s), B('&', nb(cp(e)), cp(s)))
    return B('+', B('&', e, s), B('&', cp(e), nb(cp(s))))


def r_nest(e, r, fv):
    """Kind-preserving wrapper adding one bitwise-over-arithmetic level above e:
    arithmetic e -> (((e ^ s) ^ s) + u) - u; bitwise e -> (((e + u) - u) ^ s) ^ s."""
    s, u = small_term(fv, r, True), small_term(fv, r, False)
    if e.op in BIT:
        return B('^', B('^', B('-', B('+', e, u), cp(u)), s), cp(s))
    return B('-', B('+', B('^', B('^', e, s), cp(s)), u), cp(u))


def poly_zero(fv, r):
    """u*v - ((u&v)*(u|v) + (u&~v)*(~u&v)) for two bitwise-pure terms u, v (== 0)."""
    t = min(len(fv), 3)
    atoms = [V(v) for v in r.sample(fv, t)]
    lst = pool(t)[0]
    while True:
        pu, pv = r.choice(lst)[1], r.choice(lst)[1]
        if tt_of(pu, t) != tt_of(pv, t):
            break
    u, v = inst(pu, atoms), inst(pv, atoms)
    return B('-', B('*', u, v), RW['*']['M1'][1](cp(u), cp(v)))


def corner_vals(t):
    return [np.array([M64 if c >> i & 1 else 0 for c in range(1 << t)], dtype=np.uint64) for i in range(t)]


def np_atoms(n, maxops=10):
    """(atoms, refs) of the maximal bitwise subtree at n: variables and arithmetic subterms,
    one atom per printed form; None with a constant, a big atom, or more than 3 atoms."""
    atoms, keys, refs = [], {}, []

    def g(m):
        if m.op in BIT:
            return all(g(c) for c in m.k)
        if m.op == 'c' or ops(m) > maxops:
            return False
        s = show(m)
        if s not in keys:
            keys[s] = len(atoms)
            atoms.append(m)
        refs.append((m, keys[s]))
        return True
    if n.op not in BIT or not g(n) or not 1 <= len(atoms) <= 3:
        return None
    return atoms, refs


def apply_sy(n, mode, r, fv):
    """n re-synthesized as sum a_i * e_i(atoms) with the same corner values (linear MBA)."""
    got = np_atoms(n) if mode == 'np' and n.op in BIT and not bit_pure(n) else None
    if got is not None:
        atoms, refs = got
        t = len(atoms)
        cv = corner_vals(t)
        G = ev(n, {'_n': 1 << t}, {id(m): cv[i] for m, i in refs})
    else:
        if not lin_uniform(n):
            return None
        names = sorted({m.v for m in walk(n) if m.op == 'v'})
        if not names or len(names) > 3:
            return None
        rest = [v for v in fv if v not in names]
        if rest and (len(names) == 1 or (len(names) == 2 and r.random() < 0.3)):
            names.append(r.choice(rest))            # over one variable only x + ~x = -1 exists
        t = len(names)
        env = dict(zip(names, corner_vals(t)))
        env['_n'] = 1 << t
        G = ev(n, env)
        atoms = [V(v) for v in names]
    F = [sgn(-int(g)) for g in G]
    if not any(F):
        return None
    terms = synth_terms(F, t, r)
    return build_sum(terms, atoms, r) if terms else None


def apply_zero(n, mode, r, fv, big=False):
    """n + Z, n - Z (np also n ^ Z, n | Z) with Z an integer null-space zero over 2-3
    variables (1 when the function has one argument; 3 more often when big)."""
    t = min(len(fv), r.choice([2, 3, 3] if big else [2, 2, 3]))     # t = 1 only with one argument
    atoms = [V(v) for v in r.sample(fv, t)]
    if mode == 'np' and r.random() < 0.5:
        alt = [small_term(fv, r, r.random() < 0.4) if r.random() < 0.5 else a for a in atoms]
        if len({canon(a) for a in alt}) == len(alt):      # two equal atoms: x & x, z ^ z
            atoms = alt
    z = build_sum(zero_terms(t, r), atoms, r)
    if z is None:
        return None
    op = r.choice('+-') if mode != 'np' or r.random() < 0.6 else r.choice('^|')
    e = detach(n)
    return B(op, z, e) if op != '-' and r.random() < 0.3 else B(op, e, z)


DUP = 40
STATS = Counter()


def candidates(n, mode, fv, r, expand, budget=0):
    """[(weight, name, thunk)] of the rewrites allowed at n: an operation (identities,
    product rules, re-synthesis, wrappers) or a variable (re-synthesis, wrappers). A node
    gets at most one wrapper (Z / AF / MK / SP) per layer."""
    lp = mode != 'np'
    ax = n.pk not in BIT
    ident = can_rewrite(n, GEN[0])
    wrap = can_wrap(n, GEN[0])
    kids = n.k
    out = []
    if kids and ident:
        a = kids[0]
        b = kids[1] if len(kids) > 1 else None
        dup_ok = sum(ops(c) for c in kids) <= DUP
        const_kid = any(c.op == 'c' for c in kids)
        # an identity over the constant 0 or -1 makes operations clang folds (a & 0, a | -1, ...),
        # one over two equal operands makes a & a, a ^ a, ...
        if any(c.op == 'c' and c.v in (0, M64) for c in kids) or (b is not None and (same(a, b) or compl(a, b))):
            rules = {}
        else:
            rules = RW.get(n.op, {})
        for name, (fl, f) in rules.items():
            if lp and ('np' in fl or ('ax' in fl and not ax) or ('bwa' in fl and not bw(a))
                       or ('bwb' in fl and not bw(b)) or ('poly' in fl and mode == 'lin')):
                continue
            if ('dup' in fl and not dup_ok) or (n.op == '*' and const_kid):
                continue
            out.append((1 if expand else 4, name, lambda f=f: f(a, b)))
        if n.op == '~' and dup_ok and (not lp or (ax and bw(a))):
            vs = [v for v in fv if not same(V(v), a) and not compl(V(v), a)]
            if vs:
                out.append((1 if expand else 4, 'T4', lambda: r_not_split(a, r.choice(vs), r)))
        if n.op == '*' and dup_ok:
            if const_kid:
                out.append((2, 'K', lambda: r_ksplit(a, b, r)))
            elif mode != 'lin':
                out.append((3, 'M2', lambda: r_mul2(a, b, r)))
                if a.op in ('+', '-') or b.op in ('+', '-'):
                    out.append((3, 'MD', lambda: r_dist(a, b, r)))
    if ax or not lp:
        if wrap:
            out.append((3 if expand else 1, 'Z', lambda: apply_zero(n, mode, r, fv, budget >= 40)))
            if mode != 'lin':
                out.append((1, 'AF', lambda: r_affine(detach(n), r)))
        if ident and ops(n) <= 10 and all(0 <= m.g < GEN[0] for m in walk(n)):     # old code only
            out.append((2 if expand else 1, 'SY', lambda: apply_sy(n, mode, r, fv)))
    if mode == 'np' and wrap and ops(n) <= DUP:
        out.append((2, 'MK', lambda: r_mask(detach(n), r)))
        out.append((2, 'SP', lambda: r_split(detach(n), r, fv)))
    return out


def fix_pk(n):
    """Parent operations of n's kids and grandkids (a rejected rewrite may have changed them)."""
    for c in n.k:
        c.pk = n.op
        for g in c.k:
            g.pk = c.op


def kill(n):
    for m in walk(n):
        m.g = -1


def rewrite(n, mode, fv, r, budget, expand=False):
    """Apply one random allowed rewrite at n whose growth (tree ops) is <= budget, in place.
    Returns the growth, or None."""
    cands = candidates(n, mode, fv, r, expand, budget)
    before = None
    for _ in range(3):
        if not cands:
            return None
        x = r.random() * sum(c[0] for c in cands)
        i = 0
        while i < len(cands) - 1 and x >= cands[i][0]:
            x -= cands[i][0]
            i += 1
        _, name, th = cands.pop(i)
        DISCARD.clear()
        new = th()
        if new is None:
            fix_pk(n)
            continue
        if before is None:
            before = ops(n)
        g = ops(new) - before
        if g > budget or (new.op == n.pk and new.op in ('~', 'neg')):      # no ~~e, -(-e)
            fix_pk(n)
            continue
        if name == 'SY':
            for c in n.k:
                kill(c)
        for m in DISCARD:
            m.g = -1
        install(n, new)
        if name in WRAPPERS:
            n.dn, n.rw = GEN[0], 0
        else:
            n.rw = GEN[0]
        STATS[name] += 1
        return g
    return None


WRAPPERS = frozenset(['Z', 'AF', 'MK', 'SP'])


def can_rewrite(m, L):
    """Layer L may rewrite m's code (identity, product rule, re-synthesis): code made
    before layer L and not discarded."""
    return 0 <= m.g < L


def can_wrap(m, L):
    """Layer L may wrap m's position: not wrapped yet in layer L, and its code is old or
    was rewritten in place by layer L (a wrapper does not transform its operand)."""
    return m.dn != L and m.g >= 0 and (m.g < L or m.rw == L) and m.op not in ('c', 'p')


def eligible(m, L):
    return (can_rewrite(m, L) and (bool(m.k) or m.op == 'v')) or can_wrap(m, L)


def obfuscate(root, mode, d, target, fv, r):
    """d layers. Layer L rewrites only operations that existed before it, each at most
    once (a wrapper keeps the old node as its operand, marked done), never code made by
    layer L itself: rewrites nest at most d deep. The frontier (the nodes layer L-1 made)
    comes first, then other old nodes until the layer's goal (geometric toward target)."""
    base = max(ops(root), 1)
    cur = ops(root)
    ratio = (max(target, base + 1) / base) ** (1.0 / d)
    for L in range(1, d + 1):
        GEN[0] = L
        goal = target if L == d else int(base * ratio ** L)
        slack = max(4, goal // 10)
        front = [m for m in walk(root) if m.k and m.g == L - 1]
        r.shuffle(front)
        for m in front:
            if cur >= goal:
                break
            if eligible(m, L):
                g = rewrite(m, mode, fv, r, goal - cur + slack)
                if g is not None:
                    cur += g
        tries = 0
        while cur < goal - slack and tries < 300:
            tries += 1
            allm = [m for m in walk(root) if eligible(m, L)]
            if not allm:
                break
            g = rewrite(r.choice(allm), mode, fv, r, goal - cur + slack, expand=True)
            if g is not None:
                cur += g
    return cur


def nest_map(root):
    """id(node) -> most bitwise-over-arithmetic edges on a path below it."""
    out = {}

    def g(n):
        best = 0
        for c in n.k:
            best = max(best, g(c) + (1 if n.op in BIT and c.op in ARI else 0))
        out[id(n)] = best
        return best
    g(root)
    return out


def has_product(root):
    return any(m.op == '*' and all(c.op != 'c' for c in m.k) for m in walk(root))


def classify(root):
    npoly = any(m.op in BIT and any(c.op in ARI or c.op == 'c' for c in m.k) for m in walk(root))
    return 'nonpoly' if npoly else ('poly' if has_product(root) else 'linear')


def finish(root, mode, fv, r):
    """poly: make sure a product of non-constants is there; np: nesting >= 2."""
    if mode == 'poly' and not has_product(root):
        install(root, B(r.choice('+-'), detach(root), poly_zero(fv, r)))
        STATS['PZ'] += 1
    if mode == 'np':
        for _ in range(4):
            nm = nest_map(root)
            top = nm[id(root)]
            if top >= 2:
                break
            m = r.choice([m for m in walk(root) if m.k and nm[id(m)] == top])
            install(m, r_nest(detach(m), r, fv))
            STATS['NEST'] += 1


def defects(root):
    """Operations clang would fold: on constants only, or trivial (x*1, x+0, x&-1, ...)."""
    bad = []

    def g(n):
        if n.op == 'v':
            return True
        if n.op == 'c':
            return False
        dep = [g(c) for c in n.k]
        if not any(dep):
            bad.append('constant-only ' + show(n)[:40])
        for c in n.k:
            if c.op == 'c' and (c.v in (0,) or (c.v == 1 and n.op == '*')
                                or (c.v == M64 and n.op in ('&', '|'))):
                bad.append('trivial ' + n.op + ' ' + lit(c.v))
        if n.op in ('&', '|', '^', '-') and same(n.k[0], n.k[1]):
            bad.append('self ' + n.op)
        return any(dep)
    g(root)
    return bad


# ---------------------------------------------------------------- ground truths
VARS = ('x', 'y', 'z', 'w')
LIN_T = ['(~x)', '(-x)', '((3 * x) + 7)', '(x + y)', '(x - y)', '(x ^ y)', '(x & y)', '(x | y)',
         '(x & (~y))', '(~(x | y))', '(~(x ^ y))', '((2 * x) + (3 * y))', '((x | y) + 0x5a)',
         '((x + y) + z)', '((x & y) | z)', '((x ^ y) ^ z)', '((x + y) - z)', '((x & y) + z)',
         '((x | y) & z)', '(((2 * x) - y) + (3 * z))', '(((x + y) + z) + w)', '((x ^ y) + (z & w))',
         '((x & y) | (z & w))', '(((x - y) + z) - w)', '((x ^ y) + ((x & y) * 2))', '((x | y) - (x & y))']
POLY_T = ['(x * y)', '(x * x)', '((x * y) + z)', '((x * y) - z)', '(x * (y + z))',
          '((x * y) + (z * w))', '((x * y) * z)', '((3 * (x * y)) + 5)', '((x & y) * z)',
          '((x | y) * (x & y))', '((x ^ y) * z)', '((x + y) * (x - y))']
MIX_T = ['((x + y) ^ z)', '((x * y) & z)', '((x - y) | (z + w))', '(((x ^ y) + z) & w)',
         '(((x + y) ^ z) - w)', '((((x + y) ^ z) * w) | x)', '(((x & y) + (z | w)) ^ x)',
         '((((x * 3) ^ y) + z) & (w - x))', '((x + (y ^ z)) & (w - y))', '((x + y) ^ (x - y))',
         '(((x - y) ^ (y + z)) & ((x * z) | w))', '(((((x ^ y) - z) | w) + x) ^ y)',
         '(((x + y) & (z ^ w)) - ((x | z) * y))', '((x * y) | (x + y))', '(((x & y) * 3) ^ (x + y))',
         '(((x | 0xff) + y) ^ z)', '((x ^ (x + y)) & 0xffff)', '(((x + 1) * (y ^ z)) | (x - z))']
CONSTS = [0x1337, 0xdeadbeef, 0, 1, M64, 0x8000000000000000, 0x123456789abcdef0, 42, 0xcafebabe,
          0x7fffffff, 0x5555555555555555, 0xffff0000, 0xdead0001, 7, 0x0123456789abcdef]
CATS = (('linear', 90, 'lin'), ('poly', 60, 'poly'), ('nonpoly', 60, 'np'), ('mixed', 60, 'np'),
        ('const', 30, None))


def tvars(s):
    return sorted(truth.variables(s), key=VARS.index)


def target_ops(d, r):
    """Tree operations to aim for (the compiled DAG keeps about 55-65% of them, ~1.4
    instructions each): about 20 compiled operations at difficulty 1-2, most functions
    with 50-300, 500+ at difficulty 3-4. A layer can only rewrite what exists before it,
    so a small seed caps what difficulty 1 reaches."""
    u = r.random()

    def lg(a, b):
        return int(round(math.exp(r.uniform(math.log(a), math.log(b)))))
    if d == 1:
        return r.randint(22, 45) if u < 0.4 else lg(60, 200)
    if d == 2:
        return r.randint(25, 50) if u < 0.15 else lg(90, 480)
    if d == 3:
        return lg(110, 520) if u < 0.85 else r.randint(1050, 1500)
    return lg(160, 520) if u < 0.65 else r.randint(1050, 1600)


def make_specs(seed):
    """The 300 function specs (category, difficulty, size target, truth, nargs, mode).
    Linear and polynomial MBA over one variable has nothing but x + ~x = -1, so their
    functions (and the linear const ones) take at least 2 arguments; the truth may still
    use one (the other arguments are mixed in and cancel)."""
    r = random.Random(f'mba-specs:{seed}')
    specs = []
    for cat, count, mode in CATS:
        diffs = [1 + i % 4 for i in range(count)]
        r.shuffle(diffs)
        src = {'linear': LIN_T, 'poly': POLY_T * 3 + LIN_T[3:9], 'nonpoly': LIN_T + POLY_T,
               'mixed': MIX_T}.get(cat, [])
        src = list(src)
        r.shuffle(src)
        for i in range(count):
            s = {'cat': cat, 'd': diffs[i], 'target': target_ops(diffs[i], r)}
            if cat == 'const':
                k = CONSTS[i % len(CONSTS)]
                n = r.randint(1, 4)
                s.update(mode='lin' if i % 2 == 0 else 'np', K=k, truth=lit(k), nargs=max(n, 2) if i % 2 == 0 else n)
            else:
                base = src[i % len(src)]
                tv = tvars(base)
                nargs = len(tv) + (1 if len(tv) < 4 and r.random() < 0.25 else 0)
                if mode in ('lin', 'poly'):
                    nargs = max(nargs, 2)
                fv = list(VARS[:nargs])
                to = r.sample(fv, len(tv)) if r.random() < 0.35 else fv[:len(tv)]
                tree = from_str(base)
                for m in walk(tree):
                    if m.op == 'v':
                        m.v = to[tv.index(m.v)]
                s.update(mode=mode, truth=show(tree), nargs=nargs)
            specs.append(s)
    r.shuffle(specs)
    for i, s in enumerate(specs):
        s['name'] = f'mba_{i:04d}'
    return specs


def const_seed(K, fv, r):
    """K hidden as (null-space zero) + K, or as sum a_i * e_i(vars) with no constant left."""
    t = min(len(fv), 3)
    while True:
        atoms = [V(v) for v in r.sample(fv, t)]
        if r.random() < 0.5:
            z = build_sum(zero_terms(t, r), atoms, r)
            if z is None:
                continue
            if K == 0:
                return z
            return B('+', z, C(K)) if r.random() < 0.7 else B('-', z, C(-K))
        terms = synth_terms([sgn(-K)] * (1 << t), t, r)
        if terms and sum(1 for k, e in terms if e is not None) >= 2:
            z = build_sum(terms, atoms, r)
            if z is not None and z.op != 'c':
                return z


# ---------------------------------------------------------------- one function
EDGE = [0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x7fffffff, 0x80000000, 0xffffffff, 2**63 - 1, 2**63, M64 - 1, M64]
RETRY = Counter()
SHARE = 3.6        # a tree is kept when SHARE * compiled operations >= obf_nodes (gen_function)
ATTEMPTS = 12      # random streams per round of a function (bump selects the round)
MIN_OPS = 16       # smallest tree kept (operations); a smaller one is retried


def verify(root, spec, r, S=256):
    """The tree against the truth on S inputs (numpy), and the printed tree (truth.compile)."""
    nargs = spec['nargs']
    rows = [[r.getrandbits(64) if r.random() < 0.5 else
             (r.choice(EDGE) if r.random() < 0.5 else r.getrandbits(r.randint(1, 64)))
             for _ in range(nargs)] for _ in range(S)]
    env = {v: np.array([row[j] for row in rows], dtype=np.uint64) for j, v in enumerate(VARS[:nargs])}
    env['_n'] = S
    got = [int(v) for v in ev(root, env)]
    f = truth.compile(spec['truth'])
    for row, g in zip(rows, got):
        if g != f(*row):
            raise AssertionError(f'{spec["name"]}: tree {g:#x} != truth {f(*row):#x} on {row}')
    obf = show(root)
    fo = truth.compile(obf)
    for row, g in list(zip(rows, got))[::16]:
        if fo(*row) != g:
            raise AssertionError(f'{spec["name"]}: printed tree differs on {row}')
    return obf


def gen_function(spec, seed, bump=0):
    """One function: {root, obf, text, ops, nodes}. Each attempt has its own random stream
    (bump > 0 moves to a later block of streams). An attempt is rejected when the tree has
    the wrong class, an operation clang would fold, depth > 150, or too much sharing: the
    C code computes each distinct operation once, so a tree whose copies stay identical
    compiles to fewer instructions than its size suggests; SHARE * operations >= obf_nodes
    keeps the instructions (1.2-1.6 per operation) above the collapse check obf_nodes / 3.
    When every attempt shares too much the least shared one is returned."""
    want = {'lin': 'linear', 'poly': 'poly'}.get(spec['mode'], 'nonpoly')
    best, why = None, []
    for attempt in range(ATTEMPTS * bump, ATTEMPTS * (bump + 1)):
        r = random.Random(f'mba:{seed}:{spec["name"]}:{attempt}')
        GEN[0] = 0
        STATS.clear()
        fv = list(VARS[:spec['nargs']])
        root = const_seed(spec['K'], fv, r) if spec['cat'] == 'const' else from_str(spec['truth'])
        root.pk = None
        obfuscate(root, spec['mode'], spec['d'], spec['target'], fv, r)
        finish(root, spec['mode'], fv, r)
        why = []
        if classify(root) != want:
            why.append(f'class {classify(root)} != {want}')
        why += defects(root)
        if depth(root) > 150:
            why.append('depth')
        if ops(root) < MIN_OPS:
            why.append('small')
        if why:
            RETRY[why[0].split()[0]] += 1
            continue
        text, nops, nself = emit_c(spec['name'], spec['nargs'], root)
        if nself:                                   # e.g. (x + y) - (y + x): t5 - t5 in C
            RETRY['self'] += 1
            continue
        obf = verify(root, spec, r)
        got = {'root': root, 'obf': obf, 'text': text, 'ops': nops, 'nodes': truth.nodes(obf),
               'rewrites': Counter(STATS)}
        if SHARE * nops >= got['nodes']:
            return got
        RETRY['shared'] += 1
        if best is None or nops * best['nodes'] > best['ops'] * got['nodes']:
            best = got
    if best is not None:
        return best
    raise RuntimeError(f'{spec["name"]}: no acceptable tree ({why})')


def emit_c(name, nargs, root):
    """C source of the function: one statement + BAR per distinct operation (commutative
    operands in canonical order). Returns (text, operations, operations whose two operands
    are the same value: clang would fold t ^ t, t - t, t & t, t | t)."""
    names, lines, nself = {}, [], [0]

    def go(n):
        if n.op == 'v':
            return n.v
        if n.op == 'c':
            return hex(n.v) + 'ULL'
        ks = [go(c) for c in n.k]
        key = (n.op,) + (tuple(sorted(ks)) if n.op in ('+', '*', '&', '|', '^') else tuple(ks))
        t = names.get(key)
        if t is None:
            if len(ks) == 2 and ks[0] == ks[1] and n.op in ('&', '|', '^', '-'):
                nself[0] += 1
            t = 't' + str(len(names))
            names[key] = t
            if n.op == '~':
                ex = '~' + ks[0]
            elif n.op == 'neg':
                ex = '-' + ks[0]
            else:
                ex = ks[0] + ' ' + n.op + ' ' + ks[1]
            lines.append('    u64 ' + t + ' = ' + ex + '; BAR(' + t + ');')
        return t
    res = go(root)
    params = ', '.join('u64 ' + v for v in VARS[:nargs])
    text = NL.join(['EXPORT u64 ' + name + '(' + params + ')', '{'] + lines + ['    return ' + res + ';', '}', ''])
    return text, len(names), nself[0]


# ---------------------------------------------------------------- code checks
def check_code(dll, written):
    """(problems, low): problems are a branch / cmov / call / undecodable byte in a function,
    or fewer instructions than compiled operations (clang folded something); low lists the
    functions with instructions < obf_nodes / 3 (the collapse check of the suite spec)."""
    problems, low = [], []
    for g in written:
        st = common.insn_stats(dll, int(g['rva'], 16), g['size'])
        if st['jcc'] or st['cmov'] or st['call'] or st['jmp'] or st['data'] or st['ret'] != 1:
            problems.append(f'{g["name"]}: jcc {st["jcc"]} cmov {st["cmov"]} call {st["call"]} '
                            f'jmp {st["jmp"]} ret {st["ret"]} data {st["data"]}')
        if g['insns'] < g['obf_ops']:
            problems.append(f'{g["name"]}: {g["insns"]} insns < {g["obf_ops"]} compiled operations')
        if 3 * g['insns'] < g['obf_nodes']:
            low.append(g['name'])
    return problems, low


def objdump_check(dll, written):
    """llvm-objdump on every function: same instruction count as capstone (insns), no
    jcc / jmp / cmov / call. Returns (problems, number of functions checked)."""
    od = common.objdump_functions(dll)
    problems = []
    for g in written:
        rva = int(g['rva'], 16)
        mine = [i for i in od.get(g['name'], []) if rva <= i[0] < rva + g['size']]
        bad = sorted({m for _, _, m in mine if m.startswith(('j', 'cmov', 'call', 'loop'))})
        if len(mine) != g['insns'] or bad:
            problems.append(f'{g["name"]}: llvm-objdump {len(mine)} insns (json {g["insns"]}) {bad}')
    return problems, len(written)


def objdump_excerpt(dll, g, lines=14):
    """The first lines of the llvm-objdump listing of function g (Intel syntax)."""
    rva = int(g['rva'], 16)
    base = common.image_base(dll)
    cmd = [common.OBJDUMP, '-d', '--no-show-raw-insn', '--x86-asm-syntax=intel',
           f'--start-address={base + rva:#x}', f'--stop-address={base + rva + g["size"]:#x}', dll]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout.splitlines()
    body = [ln.rstrip() for ln in out if ln.strip().split(':')[0].strip().isalnum() and chr(9) in ln]
    return body[:lines] + ([f'   ... ({len(body) - lines} more)'] if len(body) > lines else [])


# ---------------------------------------------------------------- report
def report(written):
    cats = Counter(g['category'] for g in written)
    print('functions per category: ' + ', '.join(f'{c} {cats[c]}' for c, _, _ in CATS) + f' (total {len(written)})')
    for c, _, _ in CATS:
        gs = [g for g in written if g['category'] == c]
        dif = Counter(g['difficulty'] for g in gs)
        cls = Counter(g['mba_class'] for g in gs)
        nest = Counter(g['mba_nesting'] for g in gs)
        ins = sorted(g['insns'] for g in gs)
        print(f'  {c:<8} difficulty {dict(sorted(dif.items()))} class {dict(sorted(cls.items()))} '
              f'insns {ins[0]}/{statistics.median(ins)}/{ins[-1]}')
        if c in ('nonpoly', 'mixed', 'const'):
            print(f'           nesting {dict(sorted(nest.items()))}')
    for key in ('insns', 'obf_ops', 'obf_nodes', 'obf_depth', 'size'):
        v = sorted(g[key] for g in written)
        print(f'{key:<9} min {v[0]:>5}  median {statistics.median(v):>7}  max {v[-1]:>6}')
    bins = Counter()
    for g in written:
        o = g['obf_ops']
        bins['<35' if o < 35 else '35-49' if o < 50 else '50-300' if o <= 300 else '301-499' if o < 500 else '>=500'] += 1
    print('compiled operations: ' + ', '.join(f'{k}: {bins[k]}' for k in ('<35', '35-49', '50-300', '301-499', '>=500')))
    r1 = sorted(g['insns'] / g['obf_ops'] for g in written)
    r3 = sorted(3 * g['insns'] / g['obf_nodes'] for g in written)
    print(f'insns / obf_ops min {r1[0]:.2f} median {statistics.median(r1):.2f}; '
          f'insns / (obf_nodes/3) min {r3[0]:.2f} median {statistics.median(r3):.2f}')


def show_functions(dll, written, names):
    for g in written:
        if g['name'] in names:
            print(f'--- {g["name"]} {g["category"]} d{g["difficulty"]} truth {g["truth"]} '
                  f'nodes {g["obf_nodes"]} ops {g["obf_ops"]} insns {g["insns"]}')
            print('obf: ' + g['obf'][:600] + (' ...' if len(g['obf']) > 600 else ''))
            print(NL.join(objdump_excerpt(dll, g, 24)))


# ---------------------------------------------------------------- main
def pin_timestamp(dll, stamp=0):
    """lld writes the link time into the PE file header and the map; a fixed value makes
    the DLL and the map byte-for-byte reproducible (nothing else depends on the time)."""
    with open(dll, 'rb') as fh:
        data = bytearray(fh.read())
    off = int.from_bytes(data[0x3c:0x40], 'little') + 4 + 4     # 'PE' + Machine, NumberOfSections
    if data[off - 8:off - 4] != bytes([0x50, 0x45, 0, 0]):
        raise ValueError(f'{dll}: no PE signature')
    data[off:off + 4] = stamp.to_bytes(4, 'little')
    with open(dll, 'wb') as fh:
        fh.write(data)
    mapf = common.map_path(dll)                 # the map repeats it: ' Timestamp is 6afacc53 (...)'
    with open(mapf, encoding='utf-8', errors='replace', newline='') as fh:
        lines = fh.read().split(NL)
    for i, ln in enumerate(lines[:8]):
        if ln.startswith(' Timestamp is '):
            lines[i] = f' Timestamp is {stamp:08x} (pinned by gen_mba.py)' + (chr(13) if ln.endswith(chr(13)) else '')
    write_text(mapf, NL.join(lines))


def write_text(path, text, tries=8):
    """Write a text file, retrying while another process (a scanner, an indexer) holds it."""
    for i in range(tries):
        try:
            with open(path, 'w', encoding='utf-8', newline=NL) as fh:
                fh.write(text)
            return
        except OSError as e:
            if i == tries - 1:
                raise
            print(f'retrying the write of {os.path.basename(path)}: {e}')
            time.sleep(0.25 * 2 ** i)


def generate(specs, seed, bump, drop, cache):
    """(function dicts for write_suite_json, C text, rewrite counts of the kept trees) of
    every spec not in drop; cache: (name, bump) -> gen_function result."""
    funcs, parts, rewrites = [], [common.C_PRELUDE.rstrip()], Counter()
    for spec in specs:
        if spec['name'] in drop:
            continue
        key = (spec['name'], bump.get(spec['name'], 0))
        if key not in cache:
            cache[key] = gen_function(spec, seed, key[1])
        got = cache[key]
        rewrites.update(got['rewrites'])
        parts.append(got['text'])
        wr = random.Random(f'mba-w:{seed}:{spec["name"]}')
        w = [wr.getrandbits(64) for _ in range(spec['nargs'])]
        root = got['root']
        funcs.append({'name': spec['name'], 'nargs': spec['nargs'], 'category': spec['cat'],
                      'difficulty': spec['d'], 'paths': [{'cond': 'True', 'out': spec['truth'], 'witness': [w]}],
                      'mba_class': classify(root), 'mba_nesting': nest_map(root)[id(root)],
                      'obf_nodes': got['nodes'], 'obf_ops': got['ops'], 'obf_depth': depth(root),
                      'obf': got['obf']})
    return funcs, NL.join(parts), rewrites


def main():
    ap = argparse.ArgumentParser(description='Build the mba suite (suites/mba).')
    ap.add_argument('--seed', type=int, default=7)
    ap.add_argument('--no-validate', action='store_true')
    ap.add_argument('--only-gen', action='store_true', help='generate and verify the trees only')
    ap.add_argument('--show', help='comma-separated function names to print')
    ap.add_argument('--mem-mb', type=int, default=3072, help='commit limit of this run and its children')
    a = ap.parse_args()
    if not memory_guard(a.mem_mb, min(a.mem_mb, 2560)):
        print('warning: no memory guard (job object refused)')
    t0 = time.perf_counter()
    p = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'selftest_mba.py')],
                       capture_output=True, text=True)
    print('selftest_mba: ' + (p.stdout + p.stderr).strip().splitlines()[-1])
    if p.returncode != 0:
        print((p.stdout + p.stderr).strip())
        return 1
    specs = make_specs(a.seed)
    d = common.suite_dir(SUITE)
    src = os.path.join(d, SUITE + '.c')
    dll = os.path.join(d, SUITE + '.dll')
    jpath = os.path.join(d, SUITE + '.json')
    if a.only_gen:
        funcs, _, _ = generate(specs, a.seed, {}, [], {})
        print(f'generated and verified {len(funcs)} trees in {time.perf_counter() - t0:.1f} s; '
              f'retries {dict(RETRY)}; memory peak (MB, job / one process) {memory_peaks()}')
        v = sorted(f['obf_ops'] for f in funcs)
        print(f'obf_ops min {v[0]} median {statistics.median(v)} max {v[-1]} total {sum(v)}')
        return 0
    # Rounds: build, then regenerate (later random streams) the functions whose instructions
    # fall under obf_nodes / 3; after 3 such rounds the remaining ones are dropped.
    bump, drop, rounds, cache = {}, [], [], {}
    for rnd in range(5):
        t1 = time.perf_counter()
        RETRY.clear()
        funcs, text, rewrites = generate(specs, a.seed, bump, drop, cache)
        write_text(src, text + NL)
        t2 = time.perf_counter()
        common.build_dll([src], dll)
        pin_timestamp(dll)
        written = common.write_suite_json(jpath, SUITE, SUITE + '.dll', funcs)
        problems, low = check_code(dll, written)
        print(f'round {rnd}: {len(funcs)} functions generated in {t2 - t1:.1f} s, built in '
              f'{time.perf_counter() - t2:.1f} s; retries {dict(RETRY)}; insns < obf_nodes/3: {low}')
        rounds.append(low)
        if not low:
            break
        if rnd < 3:
            for n in low:
                bump[n] = bump.get(n, 0) + 1
        else:
            drop += low
    else:
        raise RuntimeError(f'functions under obf_nodes/3 after dropping: {low}')
    print('rewrites in the kept trees: ' + ' '.join(f'{k}:{v}' for k, v in sorted(rewrites.items())))
    print(f'regenerated: {sorted(bump)}; dropped: {drop}')
    problems += common.crosscheck_sizes(dll)
    od_problems, n_od = objdump_check(dll, written)
    problems += od_problems
    print(f'llvm-objdump: {n_od} functions checked, {len(od_problems)} problem(s)')
    for p in problems:
        print('PROBLEM', p)
    report(written)
    if a.show:
        show_functions(dll, written, set(a.show.split(',')))
    print(f'memory peak (MB, job / one process): {memory_peaks()}')
    if problems:
        return 1
    if a.no_validate:
        return 0
    code, out = common.validate(jpath, n=2000)
    print(out.strip())
    print(f'total {time.perf_counter() - t0:.1f} s; memory peak (MB, job / one process): {memory_peaks()}')
    return code


if __name__ == '__main__':
    sys.exit(main())
