"""gen_opaque.py: the "opaque" bench suite (opaque predicates, real, MBA and narrow conditions).

usage: python -I suites/opaque/gen_opaque.py [--seed N] [--show NAME] [--no-validate]
                                             [--mem MB]
Writes suites/opaque/opaque.c, opaque.dll (+ .map), opaque.json, then runs
gen/validate.py on the json (--n 2000). Everything is derived from --seed (default
20261116): the same seed rebuilds the same sources, json and DLL (z3 decides under
deterministic rlimits, not wall-clock timeouts; the PE time stamps are fixed).
The run and its children (clang, lld, validate) live in a job object limited to
--mem MB of memory together (opq_mem.py, default 3072); z3 has its own limits.
Helpers: opq_expr.py (expression trees, C emission, MBA rewriting), opq_mem.py.

Each function is a tree of 1..4 if/else statements (one conditional jump each, checked
on the disassembly: jcc == branches, no cmov / setcc / call). Branch kinds:
  opaque_true / opaque_false  an opaque predicate (always true / always false); its dead
                arm returns 0xDEAD0000 + k (k unique in the suite) and stays real code
  real          a plain condition, both outcomes reachable
  real_mba      a real condition computed through linear MBA rewrites (both sides)
  real_narrow   a hash chain equal to a constant, reachable by one input (or one per
                value of another argument / of the high half)
Opaque families: x*(x+1) even, x*x+x even, x*x*(x+1)*(x+1) & 3 == 0, 7*y*y-1 != x*x
(low 32 bits), x*x & 3 in {0,1}, (x|~x) == 2**64-1, (x^y)+2*(x&y) == x+y,
(x & ~x) == 0, MBA versions of all of these, and predicates over a constant global
table or a local array. Every intermediate value carries BAR (common.C_PRELUDE), so
clang keeps the predicates, the MBA forms and the jumps as written; each arm puts BAR
on its own result. Every opaque predicate is proven with z3: the instance as compiled
(tables included), or, when z3 cannot decide an MBA-rewritten instance within its
budget, its plain form plus the rewrite rules (each rule is a z3-proven identity, so
the rewrite keeps the predicate); branches[].proof says which. Path conds use the simplified conditions (an MBA condition by its
plain form, a bijective hash chain by its preimage: x == x0); each branch record keeps
the condition as the code computes it ("pred", null for table predicates).
"""
import argparse
import os
import random
import statistics
import sys
import time

sys.dont_write_bytecode = True                  # no __pycache__ in the suite directory
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), 'gen'))
import common                                   # noqa: E402
import truth                                    # noqa: E402
import opq_mem                                  # noqa: E402
from opq_expr import (V, K, MASK, NL, Cnd, CBlock, Names, rol, lo32, tload, aload,  # noqa: E402
                      lang, ev, mba, obf_cnd, has_load, prove_rules)

SUITE = 'opaque'
SEED = 20261116
CATEGORIES = [('arith', 24), ('bitwise', 12), ('mba_opaque', 22), ('table', 14),
              ('real_mba', 16), ('narrow', 18), ('mixed', 14)]
ARITH = ['x*(x+1) even', 'x*x+x even', 'x*x*(x+1)*(x+1) & 3 == 0',
         '7*y*y-1 != x*x (low 32 bits)', 'x*x & 3 in {0,1}']
BITWISE = ['(x|~x) == 2**64-1', '(x^y)+2*(x&y) == x+y', '(x & ~x) == 0']
FAMILIES = ARITH + BITWISE
TABLES = ['tbl[i] even (const global table)', 'tbl[i] % 4 == 1 (const global table)',
          'tbl[i] has bit 63 set (const global table)', 'tbl[i] < 2**40 (const global table)',
          'a[i] even (local array)', 'a[i] odd (local array)', 'a[i] % 8 == 0 (local array)']
NARROW = ['splitmix64 chain', 'murmur3 fmix64', 'lcg (x ^ 0x5DEECE66D)', 'xorshift-multiply',
          'two-round lcg', '32-bit fnv-like (low 32 bits)', 'absorb two args + splitmix64',
          'fmix64(x) ^ splitmix64(y) (two args, raw)']


class Regen(Exception):
    """This draw cannot be used (an infeasible path, no witness): draw the function again."""


def two_ops(rng, args):
    """Two operands for a two-input family: two arguments, or one argument and a mix of it."""
    if len(args) > 1 and rng.random() < 0.8:
        a, b = rng.sample(args, 2)
        return a, b
    a = rng.choice(args)
    return a, rng.choice([a >> 32, rol(a, rng.randrange(7, 57)), a ^ rng.getrandbits(48)])


def operand(rng, args):
    """The value an opaque predicate is built on: an argument or a simple mix."""
    a = rng.choice(args)
    if len(args) > 1 and rng.random() < 0.45:
        b = rng.choice([v for v in args if v is not a])
        return rng.choice([lambda: a + b, lambda: a ^ b, lambda: a - b,
                           lambda: a * (2 * rng.randrange(1, 4096) + 1) + b])()
    return rng.choice([lambda: a, lambda: a, lambda: a + rng.randrange(1, 1 << 16),
                       lambda: rol(a, rng.randrange(1, 64)), lambda: a ^ rng.getrandbits(32)])()


def family_true(fam, rng, args):
    """An always-true condition of family fam (a random way of writing it)."""
    def low(t, m, forms):
        op, c = rng.choice(forms)
        return Cnd(op, t & m, c)
    if fam == 'x*(x+1) even':
        v = operand(rng, args)
        return low(v * (v + 1), 1, [('==', 0), ('!=', 1), ('<', 1)])
    if fam == 'x*x+x even':
        v = operand(rng, args)
        return low((v * v) + v, 1, [('==', 0), ('!=', 1), ('<', 1)])
    if fam == 'x*x*(x+1)*(x+1) & 3 == 0':
        v = operand(rng, args)
        if rng.random() < 0.5:
            t = (v * v) * ((v + 1) * (v + 1))
        else:
            u = v * (v + 1)
            t = u * u
        return low(t, 3, [('==', 0), ('<', 1)])
    if fam == '7*y*y-1 != x*x (low 32 bits)':
        a, b = two_ops(rng, args)
        a, b = lo32(a), lo32(b)
        lhs, rhs = (K(7) * (b * b)) - 1, a * a
        return rng.choice([lambda: Cnd('!=', lhs, rhs), lambda: Cnd('!=', lhs ^ rhs, 0),
                           lambda: Cnd('!=', lhs - rhs, 0)])()
    if fam == 'x*x & 3 in {0,1}':
        v = operand(rng, args)
        s = v * v
        if rng.random() < 0.3:
            return Cnd('==', s & 2, 0)
        return low(s, 3, [('<', 2), ('<=', 1), ('!=', 2), ('!=', 3)])
    if fam == '(x|~x) == 2**64-1':
        v = operand(rng, args)
        t = v | ~v
        return rng.choice([lambda: Cnd('==', t, MASK), lambda: Cnd('==', t + 1, 0),
                           lambda: Cnd('==', ~t, 0)])()
    if fam == '(x^y)+2*(x&y) == x+y':
        a, b = two_ops(rng, args)
        lhs = (a ^ b) + ((a & b) << 1 if rng.random() < 0.5 else K(2) * (a & b))
        return rng.choice([lambda: Cnd('==', lhs, a + b), lambda: Cnd('==', lhs - (a + b), 0)])()
    if fam == '(x & ~x) == 0':
        v = operand(rng, args)
        t = v & ~v
        return rng.choice([lambda: Cnd('==', t, 0), lambda: Cnd('<', t, 1)])()
    raise ValueError(fam)


def table_true(fam, rng, args, name):
    """An always-true condition over a constant global table (name) or a local array."""
    v = operand(rng, args)
    sh = rng.randrange(0, 58)
    if 'global' in fam:
        n = rng.choice([8, 16])
        idx = ((v >> sh) if sh else v) & (n - 1)
        if fam.startswith('tbl[i] even'):
            e = tload(name, [rng.getrandbits(64) & (MASK - 1) for _ in range(n)], idx)
            t = e if rng.random() < 0.6 else e * operand(rng, args)
            op, c = rng.choice([('==', 0), ('<', 1), ('!=', 1)])
            return Cnd(op, t & 1, c)
        if fam.startswith('tbl[i] % 4'):
            e = tload(name, [(rng.getrandbits(64) & (MASK - 3)) | 1 for _ in range(n)], idx)
            return Cnd('==', (e if rng.random() < 0.6 else e * e) & 3, 1)
        if fam.startswith('tbl[i] has bit 63'):
            e = tload(name, [rng.getrandbits(64) | (1 << 63) for _ in range(n)], idx)
            return rng.choice([lambda: Cnd('<', e, 0, True), lambda: Cnd('>=', e, 1 << 63),
                               lambda: Cnd('!=', e >> 63, 0)])()
        e = tload(name, [rng.getrandbits(40) for _ in range(n)], idx)
        return rng.choice([lambda: Cnd('==', e >> 40, 0), lambda: Cnd('<', e, 1 << 40)])()
    idx = ((v >> sh) if sh else v) & 7

    def src():
        a = rng.choice(args)
        b = rng.choice(args)
        return rng.choice([lambda: a, lambda: a + rng.getrandbits(32), lambda: a ^ b,
                           lambda: a * b, lambda: rol(a, rng.randrange(1, 64))])()
    if fam.startswith('a[i] even'):
        elems = [rng.choice([lambda s: s << 1, lambda s: K(2) * s, lambda s: (s + s)])(src()) for _ in range(8)]
        op, c = rng.choice([('==', 0), ('<', 1), ('!=', 1)])
        return Cnd(op, aload(name, elems, idx) & 1, c)
    if fam.startswith('a[i] odd'):
        elems = [rng.choice([lambda s: s | 1, lambda s: (s << 1) + 1, lambda s: (s << 1) | 1])(src()) for _ in range(8)]
        op, c = rng.choice([('!=', 0), ('==', 1)])
        return Cnd(op, aload(name, elems, idx) & 1, c)
    elems = [rng.choice([lambda s: s << 3, lambda s: K(8) * s, lambda s: (s << 4) + (s << 3)])(src()) for _ in range(8)]
    return Cnd('==', aload(name, elems, idx) & 7, 0)


# ---------------------------------------------------------------- narrow conditions
def splitmix(v):
    h = v * K(0x9E3779B97F4A7C15)
    h = h ^ (h >> 29)
    h = h * K(0xBF58476D1CE4E5B9)
    return h ^ (h >> 32)


def fmix64(v):
    h = v ^ (v >> 33)
    h = h * K(0xff51afd7ed558ccd)
    h = h ^ (h >> 33)
    h = h * K(0xc4ceb9fe1a85ec53)
    return h ^ (h >> 33)


def lcg(v):
    return ((v ^ K(0x5DEECE66D)) * K(0x5851F42D4C957F2D)) + K(0x14057B7EF767814F)


def xmx(v, rng):
    h = rol(v ^ K(rng.getrandbits(64)), rng.randrange(5, 60)) * K(rng.getrandbits(64) | 1)
    return h ^ (h >> rng.randrange(17, 40))


def lcg2(v, rng):
    h = (v * K(rng.getrandbits(64) | 1)) + K(rng.getrandbits(64))
    h = h ^ (h >> 31)
    return (h * K(rng.getrandbits(64) | 1)) + K(rng.getrandbits(64))


def fnv32(v):
    h = (lo32(v) * K(0x01000193)) & 0xffffffff
    h = h ^ (h >> 15)
    h = (h * K(0x2c1b3c6d)) & 0xffffffff
    return h ^ (h >> 12)


def narrow_pred(fam, rng, args, wit):
    """(condition as compiled, simplified condition): true exactly where the chain value
    of wit is reached. Every chain is a bijection of its input (odd multipliers,
    xorshifts, xor / add of constants), so chain(v) == chain(v0) iff v == v0."""
    env = dict(zip('xyzw', wit))
    if fam.startswith('absorb'):
        a, b = rng.sample(args, 2)
        v = rng.choice([lambda: (a * K(rng.getrandbits(64) | 1)) ^ b, lambda: a + rol(b, rng.randrange(3, 61)),
                        lambda: a ^ (b * K(rng.getrandbits(64) | 1)), lambda: a - b])()
        h = rng.choice([splitmix, fmix64, lcg])(v)
        return Cnd('==', h, ev(h, env)), Cnd('==', v, ev(v, env))
    if fam.startswith('fmix64(x) ^ splitmix64(y)'):
        a, b = rng.sample(args, 2)
        h = fmix64(a) ^ splitmix(b)
        c = Cnd('==', h, ev(h, env))
        return c, c
    a = rng.choice(args)
    if fam.startswith('32-bit'):
        h = fnv32(a)
        return Cnd('==', h, ev(h, env)), Cnd('==', lo32(a), ev(lo32(a), env))
    h = {'splitmix64 chain': splitmix, 'murmur3 fmix64': fmix64, 'lcg (x ^ 0x5DEECE66D)': lcg,
         'xorshift-multiply': lambda t: xmx(t, rng), 'two-round lcg': lambda t: lcg2(t, rng)}[fam](a)
    return Cnd('==', h, ev(h, env)), Cnd('==', a, ev(a, env))


# ---------------------------------------------------------------- real conditions, outputs
def other(rng, args, a):
    """A second argument (or, with one argument, a value derived from it)."""
    rest = [v for v in args if v is not a]
    if rest:
        return rng.choice(rest)
    return rng.choice([a >> 32, rol(a, rng.randrange(9, 55))])


def real_plain(rng, args):
    a = rng.choice(args)
    opts = [lambda: Cnd('<', a, 0, True),
            lambda: Cnd('==', a & (m := rng.choice([0xf, 0xff, 0xfff, 0xffff, 0xff00])), rng.getrandbits(64) & m),
            lambda: Cnd('==', a >> 32, 0),
            lambda: Cnd('<=', a, rng.randrange(2, 1000)),
            lambda: Cnd('!=', a & (1 << rng.randrange(64)), 0),
            lambda: Cnd('>', a, rng.getrandbits(64), True)]
    if len(args) > 1:
        b = other(rng, args, a)
        opts += [lambda: Cnd('<', a, b), lambda: Cnd('<', a, b, True), lambda: Cnd('==', a, b),
                 lambda: Cnd('>', a ^ b, rng.getrandbits(64)), lambda: Cnd('<', a + b, rng.getrandbits(64)),
                 lambda: Cnd('!=', a, b)]
    return rng.choice(opts)()


def real_mba(rng, args, pool, budget):
    """(MBA condition as compiled, its plain form)."""
    a = rng.choice(args)
    b = other(rng, args, a)
    opts = [lambda: Cnd('==', a + b, rng.getrandbits(16)),
            lambda: Cnd('==', a ^ b, rng.getrandbits(32)),
            lambda: Cnd('<', a - b, 1 << rng.randrange(40, 64)),
            lambda: Cnd('<', a ^ b, 0, True),
            lambda: Cnd('==', (a | b) & 0xff, rng.getrandbits(8)),
            lambda: Cnd('!=', a & b, 0),
            lambda: Cnd('>', a + b, rng.getrandbits(64))]
    if len(args) > 2:
        c = rng.choice([v for v in args if v is not a and v is not b] or [a])
        opts.append(lambda: Cnd('==', a + b, c ^ rng.getrandbits(64)))
    base = rng.choice(opts)()
    return obf_cnd(base, rng, pool, budget=budget), base


def leaf_out(rng, args, unused=()):
    a = rng.choice([v for v in args if v.val in unused] or args)
    b = other(rng, [v for v in args if v.val in unused or v is a] if len(unused) > 1 else args, a)
    k = rng.getrandbits(rng.choice([16, 24, 32])) | 1
    return rng.choice([
        lambda: (a + b) ^ K(k),
        lambda: (a ^ rol(b, rng.randrange(1, 64))) + K(k),
        lambda: ((a - b) * K(rng.randrange(3, 64) | 1)) + K(k),
        lambda: ((a & b) | K(k)) + (a >> rng.randrange(1, 63)),
        lambda: ((a * K(rng.getrandbits(32) | 1)) ^ (b >> rng.randrange(1, 63))) ^ K(k),
        lambda: (~a + b) ^ K(k),
        lambda: (a | (b << rng.randrange(1, 32))) - K(k),
        lambda: rol(a ^ K(k), rng.randrange(1, 64)) - b])()


def make_pool(rng, args):
    """Terms the MBA rewrites draw from (the extra term of both sides, MBA zeros)."""
    pool = list(args)
    a = rng.choice(args)
    b = other(rng, args, a)
    pool += [a ^ b, rol(a, rng.randrange(5, 60)), b + rng.getrandbits(32)]
    return pool


# ---------------------------------------------------------------- function trees
class Pred:
    def __init__(self, kind, cnd, simple, family, always=None, mba_=False):
        self.kind, self.cnd, self.simple, self.family = kind, cnd, simple, family
        self.always, self.mba, self.witness, self.proved, self.dead_out = always, mba_, None, None, None


class Leaf:
    def __init__(self, out, out_c):
        self.out, self.out_c = out, out_c


class Dead:
    def __init__(self):
        self.value = None                  # 0xDEAD0000 + k, numbered in source order


class Branch:
    def __init__(self, pred, then, els):
        self.pred, self.then, self.els = pred, then, els


def recipe(cat, i, rng):
    """(nargs, branch specs in source order) of the i-th function of category cat."""
    def opq(fams, m=False):
        return ('opq', rng.choice(fams), m)
    if cat == 'arith':
        nb = rng.choice([1, 1, 2, 2, 2, 3, 3, 4])
        specs = [('opq', ARITH[i % len(ARITH)], False)]
        specs += [opq(ARITH) if rng.random() < 0.6 else ('real',) for _ in range(nb - 1)]
        nargs = rng.choice([1, 2, 2, 3, 4])
    elif cat == 'bitwise':
        nb = rng.choice([1, 1, 2, 2, 3, 4])
        specs = [('opq', BITWISE[i % len(BITWISE)], False)]
        specs += [opq(BITWISE) if rng.random() < 0.6 else ('real',) for _ in range(nb - 1)]
        nargs = rng.choice([1, 2, 2, 3, 4])
    elif cat == 'mba_opaque':
        nb = rng.choice([1, 1, 2, 2, 3, 3, 4])
        specs = [('opq', FAMILIES[i % len(FAMILIES)], True)]
        specs += [opq(FAMILIES, rng.random() < 0.6) if rng.random() < 0.7 else ('real',) for _ in range(nb - 1)]
        nargs = rng.choice([1, 2, 2, 3, 4])
    elif cat == 'table':
        nb = rng.choice([1, 1, 2, 2, 3, 3])
        specs = [('tbl', TABLES[i % len(TABLES)])]
        specs += [rng.choice([('tbl', rng.choice(TABLES)), opq(ARITH), ('real',)]) for _ in range(nb - 1)]
        nargs = rng.choice([1, 2, 2, 3])
    elif cat == 'real_mba':
        nb = rng.choice([2, 2, 3, 3, 4])
        specs = [('rmba',), opq(FAMILIES, rng.random() < 0.5)]
        specs += [rng.choice([('rmba',), opq(FAMILIES, rng.random() < 0.5), ('real',)]) for _ in range(nb - 2)]
        nargs = rng.choice([1, 2, 2, 3, 4])
    elif cat == 'narrow':
        nb = rng.choice([2, 2, 3, 3, 4])
        specs = [('narrow', NARROW[i % len(NARROW)]), opq(FAMILIES, rng.random() < 0.3)]
        specs += [rng.choice([opq(FAMILIES), ('real',), ('narrow', rng.choice(NARROW[:6]))]) for _ in range(nb - 2)]
        nargs = rng.choice([2, 2, 3, 4])
    else:                                       # mixed
        nb = rng.choice([3, 4, 4])
        specs = [opq(FAMILIES, rng.random() < 0.5)]
        specs += [rng.choice([opq(FAMILIES, rng.random() < 0.5), ('tbl', rng.choice(TABLES)), ('real',),
                              ('rmba',), ('narrow', rng.choice(NARROW))]) for _ in range(nb - 1)]
        nargs = rng.choice([2, 3, 4])
    rng.shuffle(specs)
    return nargs, specs


def variables(e, out):
    if e.op == 'var':
        out.add(e.val)
    for c in e.kids:
        variables(c, out)
    return out


def conj(conds):
    return ' and '.join(c.lang() for c in conds) or 'True'


class Ctx:
    """The state of one function draw."""
    def __init__(self, name, cat, rng, nargs):
        self.name, self.cat, self.rng, self.nargs = name, cat, rng, nargs
        self.args = [V(n) for n in 'xyzw'[:nargs]]
        self.pool = make_pool(rng, self.args)
        self.ntab = 0
        self.outs = set()
        self.used = set()
        self.mba_leaves = cat in ('mba_opaque', 'real_mba', 'mixed') and rng.random() < 0.6

    def use(self, *trees):
        for t in trees:
            variables(t, self.used)


# z3 decides under deterministic resource limits (rlimit), never under a wall-clock
# timeout alone: the same seed must give the same suite on a loaded machine. (About
# 2.5M rlimit units per second here; the timeouts are only a safety net.)
WITNESS_RLIMIT = 2_000_000          # witness queries need at most ~6k units
DIRECT_RLIMIT = 4_000_000           # an opaque predicate as compiled
PLAIN_RLIMIT = 20_000_000           # its plain form (before the MBA rewrite): <= 300k seen
SAFETY_MS = 120_000


def z3_solver(rlimit):
    import z3
    s = z3.Solver()
    s.set('rlimit', rlimit)
    s.set('timeout', SAFETY_MS)
    return s


def witness(cond, nargs, seed=0):
    """An input on which cond holds: common.find_witness's random search, then z3
    under WITNESS_RLIMIT. None when unsat, undecided or out of memory."""
    w = common.find_witness(cond, nargs, seed=seed, use_z3=False)
    if w is not None:
        return w
    import z3
    xs = [z3.BitVec(v, 64) for v in truth.VARS]
    s = z3_solver(WITNESS_RLIMIT)
    s.add(truth.to_z3(cond, xs))
    s.add(*[v == 0 for v in xs[nargs:]])
    try:
        if s.check() != z3.sat:
            return None
    except z3.Z3Exception:                      # memory limit (opq_mem.z3_limits)
        return None
    m = s.model()
    a = [m.eval(v, model_completion=True).as_long() for v in xs]
    return a if truth.compile(cond)(*a) else None


def prefix_witness(ctx, prefix):
    """An input on which every condition of prefix holds: random 64-bit values first
    (a narrow constant then comes from a full-width input), then witness()."""
    cond = conj(prefix)
    f = truth.compile(cond)
    for _ in range(3000):
        w = [ctx.rng.getrandbits(64) for _ in range(ctx.nargs)] + [0] * (4 - ctx.nargs)
        if f(*w):
            return w
    w = witness(cond, ctx.nargs)
    if w is None:
        raise Regen
    return w


def make_pred(spec, prefix, ctx):
    rng, args = ctx.rng, ctx.args
    if spec[0] in ('opq', 'tbl'):
        if spec[0] == 'opq':
            fam, use_mba = spec[1], spec[2]
            c = plain = family_true(fam, rng, args)
            if use_mba:
                c = obf_cnd(c, rng, ctx.pool, budget=28)
            family = ('mba: ' if use_mba else '') + fam
        else:
            fam, use_mba, family = spec[1], False, spec[1]
            ctx.ntab += 1
            c = plain = table_true(fam, rng, args, f'{ctx.name}_t{ctx.ntab}')
        always = rng.random() < 0.5
        ctx.use(c.l, c.r)
        p = Pred('opaque_true' if always else 'opaque_false', c if always else c.neg(),
                 None, family, always, use_mba)
        p.plain = plain if always else plain.neg()       # the predicate before the MBA rewrite
        return p
    if spec[0] == 'real':
        c = real_plain(rng, args)
        ctx.use(c.l, c.r)
        return Pred('real', c, c, 'plain')
    if spec[0] == 'rmba':
        c, base = real_mba(rng, args, ctx.pool, budget=32)
        ctx.use(base.l, base.r)
        return Pred('real_mba', c, base, 'mba', mba_=True)
    w = prefix_witness(ctx, prefix)
    c, simple = narrow_pred(spec[1], rng, args, w)
    ctx.use(simple.l, c.l)
    p = Pred('real_narrow', c, simple, spec[1])
    p.witness = w
    return p


def make_leaf(ctx):
    unused = {a.val for a in ctx.args} - ctx.used
    for _ in range(50):
        out = leaf_out(ctx.rng, ctx.args, unused)
        s = lang(out)
        if s not in ctx.outs:
            break
    ctx.outs.add(s)
    ctx.use(out)
    out_c = mba(out, ctx.rng, budget=24) if ctx.mba_leaves and ctx.rng.random() < 0.7 else out
    return Leaf(out, out_c)


def build(specs, prefix, ctx):
    """The tree of specs (pre-order = source order); prefix: the real conditions above."""
    if not specs:
        return make_leaf(ctx)
    p = make_pred(specs[0], prefix, ctx)
    rest = specs[1:]
    if p.kind == 'opaque_true':
        return Branch(p, build(rest, prefix, ctx), Dead())
    if p.kind == 'opaque_false':
        return Branch(p, Dead(), build(rest, prefix, ctx))
    if p.kind == 'real_narrow':                 # only opaque branches below a narrow match
        lead = 0
        while lead < len(rest) and rest[lead][0] in ('opq', 'tbl'):
            lead += 1
        j = ctx.rng.randint(0, lead)
    else:
        j = ctx.rng.randint(0, len(rest))
    then = build(rest[:j], prefix + [p.simple], ctx)
    return Branch(p, then, build(rest[j:], prefix + [p.simple.neg()], ctx))


def walk(node, conds, wit, out):
    """Live leaves with their real conditions (opaque ones dropped) and a known witness."""
    if isinstance(node, Leaf):
        out.append((node, conds, wit))
    elif isinstance(node, Branch):
        p = node.pred
        if p.kind.startswith('opaque'):
            walk(node.then, conds, wit, out)
            walk(node.els, conds, wit, out)
        else:
            walk(node.then, conds + [p.simple], p.witness if p.kind == 'real_narrow' else wit, out)
            walk(node.els, conds + [p.simple.neg()], wit, out)
    return out


def preorder(node, out):
    if isinstance(node, Branch):
        out.append(node)
        preorder(node.then, out)
        preorder(node.els, out)
    return out


EDGES = [0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x7fffffff, 0x80000000, 0xffffffff,
         2**63 - 1, 2**63, 2**64 - 2, 2**64 - 1]


def samples(rng, nargs, n=96):
    out = [[rng.choice(EDGES) for _ in range(nargs)] for _ in range(n // 3)]
    out += [[rng.getrandbits(64) for _ in range(nargs)] for _ in range(n - n // 3)]
    return [a + [0] * (4 - nargs) for a in out]


def check_preds(fn, rng):
    """Every branch condition on sample inputs: an opaque one is constant, an MBA / narrow
    one equals its simplified form, and the language rendering agrees with the tree."""
    for node in fn.nodes:
        p = node.pred
        s = p.cnd.lang()
        f = truth.compile(s) if s is not None else None
        ins = samples(rng, fn.nargs) + ([p.witness] if p.witness else [])
        for a in ins:
            env = dict(zip('xyzw', a))
            got = p.cnd.ev(env)
            want = p.always if p.kind.startswith('opaque') else p.simple.ev(env)
            if got != want or (f is not None and f(*a) != got):
                raise RuntimeError(f'{fn.name}: {p.kind} {p.family} wrong on {a}')
        if p.witness and not p.cnd.ev(dict(zip('xyzw', p.witness))):
            raise RuntimeError(f'{fn.name}: narrow witness misses')


class Fn:
    pass


def gen_function(name, cat, i, rng):
    for _ in range(60):
        try:
            return _gen_function(name, cat, i, rng)
        except Regen:
            continue
    raise RuntimeError(f'{name}: no usable draw in 60 attempts')


def _gen_function(name, cat, i, rng):
    nargs, specs = recipe(cat, i, rng)
    ctx = Ctx(name, cat, rng, nargs)
    root = build(specs, [], ctx)
    if {a.val for a in ctx.args} - ctx.used:
        raise Regen                              # an argument nothing reads
    paths = []
    for leaf, conds, wit in walk(root, [], None, []):
        cond = conj(conds)
        f = truth.compile(cond)
        ws = []
        if wit is not None:
            if not f(*wit):
                raise RuntimeError(f'{name}: the narrow witness misses its path {cond}')
            ws.append(wit)                       # a narrow match: its constructed input
        else:
            for seed in (0, 1):
                w = witness(cond, nargs, seed=seed)
                if w is not None and w not in ws:
                    ws.append(w)
        if not ws:
            raise Regen                          # infeasible (or too hard) path
        paths.append({'cond': cond, 'out': lang(leaf.out), 'witness': ws})
    fn = Fn()
    fn.name, fn.cat, fn.nargs, fn.root, fn.paths = name, cat, nargs, root, paths
    fn.nodes = preorder(root, [])
    fn.mba_leaves = any(leaf.out_c is not leaf.out for leaf, _, _ in walk(root, [], None, []))
    check_preds(fn, rng)
    kinds = [n.pred.kind for n in fn.nodes]
    d = len(kinds) + (1 if fn.mba_leaves or any(n.pred.mba for n in fn.nodes) else 0)
    d += 1 if 'real_narrow' in kinds else 0
    fn.difficulty = max(1, min(5, d))
    return fn


def number_dead(fns):
    """Dead arms get 0xDEAD0000 + k, k = 1, 2, ... over the suite in source order."""
    k = 0
    for fn in fns:
        for node in fn.nodes:
            p = node.pred
            if p.kind.startswith('opaque'):
                k += 1
                dead = node.els if p.kind == 'opaque_true' else node.then
                dead.value = p.dead_out = 0xDEAD0000 + k
    return k


def prove_opaque(fns):
    """z3: each opaque condition has its constant value. First the condition as compiled
    (tables included, DIRECT_RLIMIT); when z3 cannot decide an MBA-rewritten one within
    that, its plain form (before the rewrite, PLAIN_RLIMIT): the rewrite keeps the condition
    because every rule it applies is an identity (opq_expr.prove_rules, run before).
    p.proof: 'z3', 'z3 plain form + MBA rules', or None (not proven; sampled only)."""
    import z3
    xs = {n: z3.BitVec(n, 64) for n in 'xyzw'}
    stats = {'z3': 0, 'z3 plain form + MBA rules': 0, None: 0}

    def check(fn, cnd, always, rlimit):
        s = z3_solver(rlimit)
        t = cnd.z3(xs)
        s.add(z3.Not(t) if always else t)
        s.add(*[xs[n] == 0 for n in 'xyzw'[fn.nargs:]])
        try:
            r = s.check()
        except z3.Z3Exception:                  # memory limit (opq_mem.z3_limits)
            return z3.unknown
        if r == z3.sat:
            m = s.model()
            raise RuntimeError(f'{fn.name}: opaque {p.family} fails on '
                               f'{[m.eval(xs[n], model_completion=True) for n in "xyzw"]}')
        return r

    for fn in fns:
        for node in fn.nodes:
            p = node.pred
            if not p.kind.startswith('opaque'):
                continue
            p.proof = None
            if check(fn, p.cnd, p.always, DIRECT_RLIMIT) == z3.unsat:
                p.proof = 'z3'
            elif p.mba and check(fn, p.plain, p.always, PLAIN_RLIMIT) == z3.unsat:
                p.proof = 'z3 plain form + MBA rules'
            stats[p.proof] += 1
    return stats


# ---------------------------------------------------------------- C source
def tables(e, out):
    if e.op == 'tload':
        out[e.val[0]] = e.val[1]
    for c in e.kids:
        tables(c, out)
    return out


def emit(node, names, depth, lines):
    pad = '    ' * depth
    if isinstance(node, Leaf):
        b = CBlock(names, depth)
        v = b.val(node.out_c)
        lines += b.lines + [f'{pad}r = {v}; BAR(r);']
    elif isinstance(node, Dead):
        lines.append(f'{pad}r = {node.value:#x}ULL; BAR(r);')
    else:
        b = CBlock(names, depth)
        cc = node.pred.cnd.c(b)
        lines += b.lines + [f'{pad}if ({cc}) {{']
        emit(node.then, names, depth + 1, lines)
        lines.append(f'{pad}}} else {{')
        emit(node.els, names, depth + 1, lines)
        lines.append(f'{pad}}}')


def c_function(fn):
    tabs = {}
    for node in fn.nodes:
        tables(node.pred.cnd.l, tabs)
        tables(node.pred.cnd.r, tabs)
    lines = ['static const u64 ' + name + '[' + str(len(vals)) + '] = {' +
             ', '.join(f'{v:#x}ULL' for v in vals) + '};' for name, vals in tabs.items()]
    kinds = ', '.join(n.pred.kind for n in fn.nodes)
    lines.append(f'/* {fn.name}: {fn.cat}; branches in source order: {kinds} */')
    params = ', '.join(f'u64 {v}' for v in 'xyzw'[:fn.nargs])
    lines += [f'EXPORT u64 {fn.name}({params})', '{', '    u64 r;']
    emit(fn.root, Names(), 1, lines)
    lines += ['    return r;', '}', '']
    fn.tables = tabs
    return lines


def c_source(fns, seed):
    head = [f'/* opaque suite: generated by gen_opaque.py --seed {seed}; do not edit */']
    body = []
    for fn in fns:
        body += c_function(fn)
    return NL.join(head + [common.C_PRELUDE] + body)


def fix_timestamp(dll):
    """lld-link writes the build time into the COFF header and the map: replace it with
    a hash of the image (what /Brepro does; common.build_dll takes no linker flags), so
    the same seed gives a byte-identical DLL and map."""
    import hashlib
    import struct
    with open(dll, 'rb') as fh:
        data = bytearray(fh.read())
    at = struct.unpack_from('<I', data, 0x3c)[0] + 8      # 'PE' 0 0, Machine, NumberOfSections
    old = struct.unpack_from('<I', data, at)[0]
    struct.pack_into('<I', data, at, 0)
    stamp = int.from_bytes(hashlib.sha256(data).digest()[:4], 'little')
    struct.pack_into('<I', data, at, stamp)
    with open(dll, 'wb') as fh:
        fh.write(data)
    mapf = common.map_path(dll)
    with open(mapf, encoding='utf-8', errors='replace') as fh:
        text = fh.read()
    lines = text.split(NL)
    for i, line in enumerate(lines):
        if line.strip().startswith('Timestamp is') and f'{old:08x}' in line:
            lines[i] = f' Timestamp is {stamp:08x} (reproducible build: a hash of the image, not a date)'
            break
    else:
        raise RuntimeError(f'{mapf}: no "Timestamp is {old:08x}" line')
    with open(mapf, 'w', encoding='utf-8', newline='') as fh:
        fh.write(NL.join(lines))
    return stamp


# ---------------------------------------------------------------- code checks
def check_code(dll, fns):
    """Each function: one jcc per source branch (counted with capstone and again in the
    llvm-objdump listing), no cmov / setcc / call; every dead constant is materialized
    in the function, and not before its first jump."""
    exp = common.exports(dll)
    sizes = common.func_sizes(dll)
    od = common.objdump_functions(dll)
    problems = []
    for fn in fns:
        rva, size = exp[fn.name], sizes[fn.name]
        ins = common.disasm(dll, rva, size)
        st = common.insn_stats(dll, rva, size)
        fn.stats = st
        od_jcc = sum(1 for a, _, m in od.get(fn.name, []) if rva <= a < rva + size
                     and m.startswith('j') and m != 'jmp')
        if od_jcc != len(fn.nodes):
            problems.append(f'{fn.name}: llvm-objdump shows {od_jcc} jcc, the source has {len(fn.nodes)} branches')
        if st['jcc'] != len(fn.nodes) or st['cmov'] or st['setcc'] or st['call'] or st['data']:
            problems.append(f'{fn.name}: jcc={st["jcc"]} (branches {len(fn.nodes)}) cmov={st["cmov"]} '
                            f'setcc={st["setcc"]} call={st["call"]} data={st["data"]}')
        first = next((k for k, i in enumerate(ins) if i.mnemonic.startswith('j') or i.mnemonic == 'ret'), len(ins))
        for node in fn.nodes:
            p = node.pred
            if not p.kind.startswith('opaque'):
                continue
            h = f'{p.dead_out:#x}'
            at = [k for k, i in enumerate(ins) if h in [o.strip() for o in i.op_str.split(',')]]
            if not at:
                problems.append(f'{fn.name}: dead constant {h} is not in the code')
            elif min(at) <= first:
                problems.append(f'{fn.name}: dead constant {h} is loaded before the first jump')
        if fn.tables or any(has_load(n.pred.cnd.l) for n in fn.nodes):
            if not any('*8]' in i.op_str for i in ins):
                problems.append(f'{fn.name}: no indexed table / array load')
    return problems


def branch_record(p):
    r = {'kind': p.kind}
    if p.kind.startswith('opaque'):
        r.update(family=p.family, always=p.always, dead_out=hex(p.dead_out), cond=str(p.always),
                 pred=p.cnd.lang(), mba=p.mba, proof=p.proof)
    else:
        r.update(family=p.family, cond=p.simple.lang(), pred=p.cnd.lang())
        if p.witness:
            r['witness'] = p.witness
    return r


def json_function(fn):
    return {'name': fn.name, 'nargs': fn.nargs, 'category': fn.cat, 'difficulty': fn.difficulty,
            'paths': fn.paths,
            'opaque': [{'kind': n.pred.family, 'always': n.pred.always, 'dead_out': hex(n.pred.dead_out)}
                       for n in fn.nodes if n.pred.kind.startswith('opaque')],
            'branches': [branch_record(n.pred) for n in fn.nodes],
            'mba_outputs': fn.mba_leaves}


# ---------------------------------------------------------------- main
def summary(out, fns):
    from collections import Counter
    cats = Counter(g['category'] for g in out)
    insns = sorted(g['insns'] for g in out)
    print('categories: ' + ', '.join(f'{c} {cats[c]}' for c, _ in CATEGORIES))
    print(f'insns per function: min {insns[0]} median {statistics.median(insns)} max {insns[-1]}')
    kinds = Counter(b['kind'] for g in out for b in g['branches'])
    print('branch kinds: ' + ', '.join(f'{k} {v}' for k, v in sorted(kinds.items())))
    nb = Counter(len(g['branches']) for g in out)
    print('branches per function: ' + ', '.join(f'{k}: {nb[k]}' for k in sorted(nb)))
    npaths = Counter(len(g['paths']) for g in out)
    print('paths per function: ' + ', '.join(f'{k}: {npaths[k]}' for k in sorted(npaths)))
    fam = Counter(o['kind'] for g in out for o in g['opaque'])
    print('opaque families: ' + '; '.join(f'{k} {v}' for k, v in sorted(fam.items())))
    nar = Counter(b['family'] for g in out for b in g['branches'] if b['kind'] == 'real_narrow')
    print('narrow families: ' + '; '.join(f'{k} {v}' for k, v in sorted(nar.items())))


def main():
    ap = argparse.ArgumentParser(description='Build the opaque bench suite.')
    ap.add_argument('--seed', type=int, default=SEED)
    ap.add_argument('--show', help='comma-separated names: print their C source and disassembly')
    ap.add_argument('--no-validate', action='store_true')
    ap.add_argument('--mem', type=int, default=3072,
                    help='MB of memory for this run and its children together (job object)')
    a = ap.parse_args()
    if not opq_mem.cap(a.mem):
        print('warning: could not put the run into a memory-limited job object')
    opq_mem.z3_limits(min(1024, a.mem // 3))
    t0 = time.perf_counter()
    rng = random.Random(a.seed)
    fns, i = [], 0
    for cat, count in CATEGORIES:
        for j in range(count):
            fns.append(gen_function(f'opq_{i:04d}', cat, j, rng))
            i += 1
    ndead = number_dead(fns)
    t1 = time.perf_counter()
    print(f'{len(fns)} functions drawn, {ndead} dead arms ({t1 - t0:.1f} s)')
    nrules = prove_rules()
    st = prove_opaque(fns)
    t2 = time.perf_counter()
    print(f'z3: {nrules} MBA rule identities proven; opaque predicates proven directly {st["z3"]}, '
          f'by their plain form {st["z3 plain form + MBA rules"]}, not proven {st[None]} ({t2 - t1:.1f} s)')
    d = common.suite_dir(SUITE)
    src = os.path.join(d, f'{SUITE}.c')
    with open(src, 'w', encoding='utf-8', newline=NL) as fh:
        fh.write(c_source(fns, a.seed))
    dll = os.path.join(d, f'{SUITE}.dll')
    common.build_dll([src], dll)
    fix_timestamp(dll)
    t3 = time.perf_counter()
    print(f'built {os.path.basename(dll)} ({t3 - t2:.1f} s)')
    problems = check_code(dll, fns) + common.crosscheck_sizes(dll)
    for p in problems:
        print('PROBLEM', p)
    if problems:
        return 1
    jpath = os.path.join(d, f'{SUITE}.json')
    out = common.write_suite_json(jpath, SUITE, f'{SUITE}.dll', [json_function(fn) for fn in fns])
    print(f'code checks passed; wrote {os.path.basename(jpath)}')
    summary(out, fns)
    if a.show:
        by = {g['name']: g for g in out}
        for name in a.show.split(','):
            fn = next(f for f in fns if f.name == name)
            print(NL.join(c_function(fn)))
            print(common.listing(dll, int(by[name]['rva'], 16), by[name]['size']))
    if a.no_validate:
        print(f'total {time.perf_counter() - t0:.1f} s, peak memory {opq_mem.peak_mb()} MB')
        return 0
    code, text = common.validate(jpath)
    print(text.strip())
    print(f'total {time.perf_counter() - t0:.1f} s, peak memory {opq_mem.peak_mb()} MB')
    return code


if __name__ == '__main__':
    sys.exit(main())
