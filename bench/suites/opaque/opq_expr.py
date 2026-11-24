"""opq_expr.py: expression trees for gen_opaque.py.

A tree (E) is evaluated in Python (ev), rendered in the bench expression language
(lang), compiled to C with a barrier on every intermediate value (CBlock), turned into
z3 terms (to_z3) and rewritten with linear MBA identities (mba / obf_const).
Shared subtrees (the same E object used twice) are computed once in C and in z3.
Node ops: var, const, + - * & | ^, ~ neg, shl shr sar rol ror (count in val),
tload (constant global table: val = (name, values), kids = (index,)),
aload (local array: val = name, kids = (index, element0, element1, ...)).
"""
MASK = (1 << 64) - 1
NL = chr(10)
BINOPS = ('+', '-', '*', '&', '|', '^')
SHIFTS = ('shl', 'shr', 'sar', 'rol', 'ror')


def lift(v):
    return v if isinstance(v, E) else E('const', (), int(v) & MASK)


class E:
    __slots__ = ('op', 'kids', 'val')

    def __init__(self, op, kids=(), val=None):
        self.op, self.kids, self.val = op, tuple(kids), val

    def __add__(a, b): return E('+', (a, lift(b)))
    def __radd__(a, b): return E('+', (lift(b), a))
    def __sub__(a, b): return E('-', (a, lift(b)))
    def __rsub__(a, b): return E('-', (lift(b), a))
    def __mul__(a, b): return E('*', (a, lift(b)))
    def __rmul__(a, b): return E('*', (lift(b), a))
    def __and__(a, b): return E('&', (a, lift(b)))
    def __rand__(a, b): return E('&', (lift(b), a))
    def __or__(a, b): return E('|', (a, lift(b)))
    def __ror__(a, b): return E('|', (lift(b), a))
    def __xor__(a, b): return E('^', (a, lift(b)))
    def __rxor__(a, b): return E('^', (lift(b), a))
    def __invert__(a): return E('~', (a,))
    def __neg__(a): return E('neg', (a,))
    def __lshift__(a, k): return E('shl', (a,), k)
    def __rshift__(a, k): return E('shr', (a,), k)


def V(name): return E('var', (), name)
def K(v): return lift(v)
def rol(a, k): return E('rol', (a,), k)
def ror(a, k): return E('ror', (a,), k)
def sar(a, k): return E('sar', (a,), k)
def lo32(a): return a & 0xffffffff


def tload(name, values, idx): return E('tload', (idx,), (name, tuple(values)))
def aload(name, elems, idx): return E('aload', (idx,) + tuple(elems), name)


def ev(e, env, memo=None):
    """Value of e (int) for env {var name: int}."""
    if memo is None:
        memo = {}
    k = id(e)
    if k in memo:
        return memo[k]
    op = e.op
    if op == 'var':
        r = env[e.val] & MASK
    elif op == 'const':
        r = e.val
    elif op == 'tload':
        r = e.val[1][ev(e.kids[0], env, memo)]
    elif op == 'aload':
        r = ev(e.kids[1 + ev(e.kids[0], env, memo)], env, memo)
    else:
        a = ev(e.kids[0], env, memo)
        if op in BINOPS:
            b = ev(e.kids[1], env, memo)
            r = {'+': a + b, '-': a - b, '*': a * b, '&': a & b, '|': a | b, '^': a ^ b}[op]
        elif op == '~':
            r = ~a
        elif op == 'neg':
            r = -a
        else:
            k_ = e.val
            if op == 'shl':
                r = a << k_
            elif op == 'shr':
                r = a >> k_
            elif op == 'sar':
                r = (a - (1 << 64) if a >> 63 else a) >> k_
            elif op == 'rol':
                r = (a << k_) | (a >> (64 - k_))
            else:
                r = (a >> k_) | (a << (64 - k_))
        r &= MASK
    memo[k] = r
    return r


def lit(v):
    return str(v) if v < 10 else hex(v)


def lang(e, memo=None):
    """e in the bench expression language (None when it holds a table load)."""
    if memo is None:
        memo = {}
    k = id(e)
    if k in memo:
        return memo[k]
    op = e.op
    if op == 'var':
        s = e.val
    elif op == 'const':
        s = lit(e.val)
    elif op in ('tload', 'aload'):
        s = None
    else:
        ks = [lang(c, memo) for c in e.kids]
        if None in ks:
            s = None
        elif op in BINOPS:
            s = f'({ks[0]} {op} {ks[1]})'
        elif op == '~':
            s = f'(~{ks[0]})'
        elif op == 'neg':
            s = f'(-{ks[0]})'
        elif op == 'shl':
            s = f'({ks[0]} << {e.val})'
        elif op == 'shr':
            s = f'({ks[0]} >> {e.val})'
        else:
            s = f'{op}({ks[0]}, {e.val})'
    memo[k] = s
    return s


class Names:
    """Function-wide fresh C names (t1, t2, ... / a1, a2, ...)."""
    def __init__(self):
        self.n = 0

    def new(self, prefix='t'):
        self.n += 1
        return f'{prefix}{self.n}'


class CBlock:
    """C statements computing trees inside one C block: every intermediate value gets
    its own variable and a barrier BAR(v), so clang cannot fold the identities."""
    def __init__(self, names, indent):
        self.names, self.pad, self.lines, self.memo = names, '    ' * indent, [], {}

    def emit(self, s):
        self.lines.append(self.pad + s)

    def val(self, e):
        """A C operand holding the value of e (a variable, an argument or a literal)."""
        k = id(e)
        if k in self.memo:
            return self.memo[k]
        op = e.op
        if op == 'var':
            s = e.val
        elif op == 'const':
            s = f'{e.val:#x}ULL'
        else:
            if op == 'tload':
                expr = f'{e.val[0]}[{self.val(e.kids[0])}]'
            elif op == 'aload':
                elems = [self.val(c) for c in e.kids[1:]]
                arr = self.names.new('a')
                self.emit(f'u64 {arr}[{len(elems)}];')
                for j, v in enumerate(elems):
                    self.emit(f'{arr}[{j}] = {v};')
                expr = f'{arr}[{self.val(e.kids[0])}]'
            else:
                ks = [self.val(c) for c in e.kids]
                n = e.val
                if op in BINOPS:
                    expr = f'{ks[0]} {op} {ks[1]}'
                elif op == '~':
                    expr = f'~{ks[0]}'
                elif op == 'neg':
                    expr = f'0ULL - {ks[0]}'
                elif op == 'shl':
                    expr = f'{ks[0]} << {n}'
                elif op == 'shr':
                    expr = f'{ks[0]} >> {n}'
                elif op == 'sar':
                    expr = f'(u64)((s64){ks[0]} >> {n})'
                elif op == 'rol':
                    expr = f'({ks[0]} << {n}) | ({ks[0]} >> {64 - n})'
                else:
                    expr = f'({ks[0]} >> {n}) | ({ks[0]} << {64 - n})'
            s = self.names.new('t')
            self.emit(f'u64 {s} = {expr}; BAR({s});')
        self.memo[k] = s
        return s


def to_z3(e, xs, memo=None):
    """z3 bit-vector term of e; xs: {var name: z3 BitVec 64}."""
    import z3
    if memo is None:
        memo = {}
    k = id(e)
    if k in memo:
        return memo[k]
    op = e.op
    if op == 'var':
        r = xs[e.val]
    elif op == 'const':
        r = z3.BitVecVal(e.val, 64)
    elif op in ('tload', 'aload'):
        i = to_z3(e.kids[0], xs, memo)
        vals = ([z3.BitVecVal(v, 64) for v in e.val[1]] if op == 'tload'
                else [to_z3(c, xs, memo) for c in e.kids[1:]])
        r = vals[-1]                      # the index is masked: always in range
        for j in range(len(vals) - 2, -1, -1):
            r = z3.If(i == j, vals[j], r)
    else:
        a = to_z3(e.kids[0], xs, memo)
        if op in BINOPS:
            b = to_z3(e.kids[1], xs, memo)
            r = {'+': lambda: a + b, '-': lambda: a - b, '*': lambda: a * b,
                 '&': lambda: a & b, '|': lambda: a | b, '^': lambda: a ^ b}[op]()
        elif op == '~':
            r = ~a
        elif op == 'neg':
            r = -a
        elif op == 'shl':
            r = a << e.val
        elif op == 'shr':
            r = z3.LShR(a, e.val)
        elif op == 'sar':
            r = a >> e.val
        elif op == 'rol':
            r = z3.RotateLeft(a, e.val)
        else:
            r = z3.RotateRight(a, e.val)
    memo[k] = r
    return r


def dag_size(e, seen=None):
    """Number of distinct operation nodes (shared subtrees counted once)."""
    if seen is None:
        seen = set()
    if e.op in ('var', 'const') or id(e) in seen:
        return 0
    seen.add(id(e))
    return 1 + sum(dag_size(c, seen) for c in e.kids)


def has_load(e):
    return e.op in ('tload', 'aload') or any(has_load(c) for c in e.kids)


# ---------------------------------------------------------------- conditions
NEG_OP = {'==': '!=', '!=': '==', '<': '>=', '>=': '<', '>': '<=', '<=': '>'}


class Cnd:
    """l op r; unsigned unless signed (then both sides are read as s64)."""
    __slots__ = ('op', 'l', 'r', 'signed')

    def __init__(self, op, l, r, signed=False):
        self.op, self.l, self.r, self.signed = op, lift(l), lift(r), signed

    def neg(self):
        return Cnd(NEG_OP[self.op], self.l, self.r, self.signed)

    def lang(self):
        a, b = lang(self.l), lang(self.r)
        if a is None or b is None:
            return None
        if self.signed:
            a, b = f's64({a})', f's64({b})'
        return f'({a} {self.op} {b})'

    def ev(self, env):
        memo = {}
        a, b = ev(self.l, env, memo), ev(self.r, env, memo)
        if self.signed:
            a, b = a - ((a >> 63) << 64), b - ((b >> 63) << 64)
        return {'==': a == b, '!=': a != b, '<': a < b, '<=': a <= b, '>': a > b, '>=': a >= b}[self.op]

    def c(self, blk):
        a, b = blk.val(self.l), blk.val(self.r)
        if self.signed:
            a, b = f'(s64){a}', f'(s64){b}'
        return f'{a} {self.op} {b}'

    def z3(self, xs):
        import z3
        memo = {}
        a, b = to_z3(self.l, xs, memo), to_z3(self.r, xs, memo)
        op = self.op
        if op == '==':
            return a == b
        if op == '!=':
            return a != b
        if self.signed:
            return {'<': lambda: a < b, '<=': lambda: a <= b, '>': lambda: a > b, '>=': lambda: a >= b}[op]()
        return {'<': z3.ULT, '<=': z3.ULE, '>': z3.UGT, '>=': z3.UGE}[op](a, b)


# ---------------------------------------------------------------- linear MBA identities
# each rule: f(a, b, two) == a OP b for all 64-bit a, b; two(v) is 2*v (as v << 1 or 2 * v)
ADD = [lambda a, b, t: (a ^ b) + t(a & b),
       lambda a, b, t: (a | b) + (a & b),
       lambda a, b, t: t(a | b) - (a ^ b),
       lambda a, b, t: (a - ~b) - 1,
       lambda a, b, t: ((a & ~b) + (~a & b)) + t(a & b)]
SUB = [lambda a, b, t: (a ^ b) - t(~a & b),
       lambda a, b, t: (a & ~b) - (~a & b),
       lambda a, b, t: (a + ~b) + 1,
       lambda a, b, t: (a | ~b) - (~a | b)]
XOR = [lambda a, b, t: (a | b) - (a & b),
       lambda a, b, t: (a + b) - t(a & b),
       lambda a, b, t: (a & ~b) | (~a & b),
       lambda a, b, t: (a & ~b) + (~a & b)]
AND = [lambda a, b, t: (a | b) - (a ^ b),
       lambda a, b, t: (a + b) - (a | b),
       lambda a, b, t: ~(~a | ~b),
       lambda a, b, t: (~a | b) - ~a]
OR = [lambda a, b, t: (a ^ b) + (a & b),
      lambda a, b, t: (a & ~b) + b,
      lambda a, b, t: (a + b) - (a & b),
      lambda a, b, t: ~(~a & ~b)]
NOT = [lambda a, t: (-a) - 1, lambda a, t: a ^ K(MASK)]
NEG = [lambda a, t: ~a + 1, lambda a, t: ~(a - 1)]
ZERO = [lambda p, q, t: ((p | q) - (p & q)) - (p ^ q),
        lambda p, q, t: ((p ^ q) + t(p & q)) - (p + q),
        lambda p, q, t: ((p & ~q) + q) - (p | q),
        lambda p, q, t: ((~p | q) - ~p) - (p & q)]
RULES = {'+': ADD, '-': SUB, '^': XOR, '&': AND, '|': OR}


def _two(rng):
    if rng.random() < 0.5:
        return lambda v: v << 1
    return lambda v: K(2) * v


def _rewrite(e, rng, p, memo):
    k = id(e)
    if k in memo:
        return memo[k]
    op = e.op
    if op in ('var', 'const'):
        r = e
    else:
        kids = tuple(_rewrite(c, rng, p, memo) for c in e.kids)
        if op in RULES and rng.random() < p:
            r = rng.choice(RULES[op])(kids[0], kids[1], _two(rng))
        elif op == '~' and rng.random() < p:
            r = rng.choice(NOT)(kids[0], _two(rng))
        elif op == 'neg' and rng.random() < p:
            r = rng.choice(NEG)(kids[0], _two(rng))
        else:
            r = E(op, kids, e.val)
    memo[k] = r
    return r


def mba(e, rng, p=0.75, rounds=2, budget=40):
    """An equivalent tree: up to `rounds` passes of linear MBA rewriting (+ - ^ & | ~ neg),
    stopping before the tree grows past `budget` operation nodes."""
    for _ in range(rounds):
        e2 = _rewrite(e, rng, p, {})
        if dag_size(e2) > budget:
            break
        e = e2
    return e


def zero(rng, pool):
    """An MBA expression equal to 0 for every input, over two trees of pool."""
    p, q = rng.sample(pool, 2) if len(pool) > 1 else (pool[0], pool[0] ^ 0x5bd1e995)
    return rng.choice(ZERO)(p, q, _two(rng))


def obf_const(c, rng, pool):
    """The constant c as c combined with an MBA zero."""
    z = zero(rng, pool)
    return rng.choice([lambda: z + c, lambda: K(c) + z, lambda: K(c) - z, lambda: z ^ c])()


def obf_cnd(cnd, rng, pool, p_both=0.6, budget=40):
    """An equivalent condition whose sides are MBA-rewritten; for == / != the same random
    term is first added to (or xored into, subtracted from) both sides."""
    l, r = cnd.l, cnd.r
    if r.op == 'const':
        r = obf_const(r.val, rng, pool)
    if cnd.op in ('==', '!=') and rng.random() < p_both:
        m = rng.choice(pool)
        how = rng.choice(('+', '^', '-'))
        l, r = E(how, (l, m)), E(how, (r, m))
    return Cnd(cnd.op, mba(l, rng, budget=budget), mba(r, rng, budget=budget), cnd.signed)


def prove_rules(timeout_ms=20000):
    """z3: every rewrite rule above is an identity (both ways of writing 2*v), and the
    steps obf_cnd applies to both sides of == / != keep the condition. Then an MBA
    rewrite (mba, obf_const, obf_cnd) of a tree is equivalent to it by induction over
    the tree. Returns the number of identities proven; raises when one is not."""
    import z3
    a, b = V('x'), V('y')
    xs = {n: z3.BitVec(n, 64) for n in 'xyzw'}
    X, Y, Z = xs['x'], xs['y'], xs['z']
    want = {'+': X + Y, '-': X - Y, '^': X ^ Y, '&': X & Y, '|': X | Y}
    twos = (lambda v: v << 1, lambda v: K(2) * v)
    goals = []
    for op, rules in RULES.items():
        for i, f in enumerate(rules):
            for t in twos:
                goals.append((f'{op} rule {i}', to_z3(f(a, b, t), xs) == want[op]))
    goals += [(f'~ rule {i}', to_z3(f(a, None), xs) == ~X) for i, f in enumerate(NOT)]
    goals += [(f'neg rule {i}', to_z3(f(a, None), xs) == -X) for i, f in enumerate(NEG)]
    for i, f in enumerate(ZERO):
        for t in twos:
            goals.append((f'zero rule {i}', to_z3(f(a, b, t), xs) == 0))
    goals += [('both sides +', (X + Z == Y + Z) == (X == Y)),
              ('both sides ^', (X ^ Z == Y ^ Z) == (X == Y)),
              ('both sides -', (X - Z == Y - Z) == (X == Y))]
    for name, g in goals:
        s = z3.Solver()
        s.set('timeout', timeout_ms)
        s.add(z3.Not(g))
        r = s.check()
        if r != z3.unsat:
            raise RuntimeError(f'MBA rule not proven ({r}): {name}')
    return len(goals)
