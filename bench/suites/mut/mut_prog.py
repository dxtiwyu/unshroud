"""mut_prog.py: the source programs of the mut suite and their ground truth.

A program is a list of statements over the arguments x, y, z, w and temporaries t1, t2..:
  ('op', dst, kind, a, b)   dst = kind(a, b); a a variable (None for 'const'), b a
                            variable, an int (a 64-bit constant, or a shift count) or None
  ('if', id, pred, a, b, then, else)   then / else are statement lists; a a variable,
                            b a variable or an int; both arms end by defining the same
                            join variable, the only one of the arms used after the if
  ('ret', a)                the last statement of the top-level list
kinds: add sub xor and or mul (b a variable or a constant that fits a sign-extended
imm32), shl shr sar rol ror (b a count 1..63), vshl vshr vsar vrol vror (b a variable,
the count is b & 63), not neg, const (b any 64-bit value).
preds: ult ule ugt uge slt sle sgt sge eq ne, tz / tnz ((a & b) == 0 / != 0).
"""
MASK = (1 << 64) - 1
SIGN = 1 << 63
ARGS = ('x', 'y', 'z', 'w')
ALU = ('add', 'sub', 'xor', 'and', 'or', 'mul')
SHIFTS = ('shl', 'shr', 'sar', 'rol', 'ror')
VSHIFTS = ('vshl', 'vshr', 'vsar', 'vrol', 'vror')
UNARY = ('not', 'neg')
COMMUTATIVE = ('add', 'xor', 'and', 'or', 'mul')
CMP = {'eq': '==', 'ne': '!=', 'ult': '<', 'ule': '<=', 'ugt': '>', 'uge': '>=',
       'slt': '<', 'sle': '<=', 'sgt': '>', 'sge': '>='}
NEG = {'eq': 'ne', 'ne': 'eq', 'ult': 'uge', 'uge': 'ult', 'ule': 'ugt', 'ugt': 'ule',
       'slt': 'sge', 'sge': 'slt', 'sle': 'sgt', 'sgt': 'sle', 'tz': 'tnz', 'tnz': 'tz'}


def s64(v):
    return v - (1 << 64) if v & SIGN else v


def ev_op(kind, a, b):
    """Value of one operation on 64-bit ints (b: the operand value, or the count)."""
    if kind == 'add':
        return (a + b) & MASK
    if kind == 'sub':
        return (a - b) & MASK
    if kind == 'xor':
        return a ^ b
    if kind == 'and':
        return a & b
    if kind == 'or':
        return a | b
    if kind == 'mul':
        return (a * b) & MASK
    if kind in ('shl', 'vshl'):
        return (a << (b & 63)) & MASK
    if kind in ('shr', 'vshr'):
        return a >> (b & 63)
    if kind in ('sar', 'vsar'):
        return (s64(a) >> (b & 63)) & MASK
    if kind in ('rol', 'vrol'):
        k = b & 63
        return ((a << k) | (a >> (64 - k))) & MASK
    if kind in ('ror', 'vror'):
        k = b & 63
        return ((a >> k) | (a << (64 - k))) & MASK
    if kind == 'not':
        return a ^ MASK
    if kind == 'neg':
        return (-a) & MASK
    if kind == 'const':
        return b & MASK
    raise ValueError(kind)


def ev_pred(pred, a, b):
    if pred == 'tz':
        return (a & b) == 0
    if pred == 'tnz':
        return (a & b) != 0
    if pred[0] == 's':
        a, b = s64(a), s64(b)
    return {'eq': a == b, 'ne': a != b, 'ult': a < b, 'ule': a <= b, 'ugt': a > b,
            'uge': a >= b, 'slt': a < b, 'sle': a <= b, 'sgt': a > b, 'sge': a >= b}[pred]


def lit(v):
    v &= MASK
    return str(v) if v < 10 else hex(v)


def fmt_op(kind, A, B, b):
    """Expression of one operation: A, B the operand expressions, b the raw operand."""
    if kind in ('add', 'sub') and type(b) is int and b & SIGN:
        return f'({A} {"-" if kind == "add" else "+"} {lit(-b)})'
    sym = {'add': '+', 'sub': '-', 'xor': '^', 'and': '&', 'or': '|', 'mul': '*'}
    if kind in sym:
        return f'({A} {sym[kind]} {B})'
    if kind == 'shl':
        return f'({A} << {b})'
    if kind == 'shr':
        return f'({A} >> {b})'
    if kind in ('sar', 'rol', 'ror'):
        return f'{kind}({A}, {b})'
    if kind == 'vshl':
        return f'({A} << ({B} & 63))'
    if kind == 'vshr':
        return f'({A} >> ({B} & 63))'
    if kind in ('vsar', 'vrol', 'vror'):
        return f'{kind[1:]}({A}, ({B} & 63))'
    if kind == 'not':
        return f'(~{A})'
    if kind == 'neg':
        return f'(-{A})'
    if kind == 'const':
        return lit(b)
    raise ValueError(kind)


def fmt_pred(pred, A, B):
    if pred in ('tz', 'tnz'):
        rel = '==' if pred == 'tz' else '!='
        return f'(({A} & {B}) {rel} 0)'
    if pred[0] == 's':
        return f'(s64({A}) {CMP[pred]} s64({B}))'
    return f'({A} {CMP[pred]} {B})'


def operand(env, b):
    """Expression of operand b: a variable's expression or a literal."""
    return env[b] if type(b) is str else lit(b)


def value(env, b):
    return env[b] if type(b) is str else b


def execute(body, args):
    """(result, path key) of the program on args (x, y, z, w order); the key is the
    tuple of (if id, taken) in execution order."""
    env = dict(zip(ARGS, args))
    key = []

    def ex(stmts):
        for st in stmts:
            if st[0] == 'op':
                _, dst, kind, a, b = st
                env[dst] = ev_op(kind, env[a] if a else 0, value(env, b) if b is not None else 0)
            elif st[0] == 'if':
                t = ev_pred(st[2], env[st[3]], value(env, st[4]))
                key.append((st[1], t))
                ex(st[5] if t else st[6])
            else:
                return env[st[1]]
        return None

    return ex(body), tuple(key)


def enumerate_paths(body, nargs):
    """[(key, [cond expressions], out expression)] for every path of the if tree
    (feasible or not), in a fixed order."""
    out = []

    def run(stmts, k, env, conds):
        if not stmts:
            k(env, conds)
            return
        st = stmts[0]
        if st[0] == 'op':
            _, dst, kind, a, b = st
            env = dict(env)
            env[dst] = fmt_op(kind, env[a] if a else None,
                              operand(env, b) if b is not None else None, b)
            run(stmts[1:], k, env, conds)
        elif st[0] == 'if':
            A, B = env[st[3]], operand(env, st[4])
            for taken, arm in ((True, st[5]), (False, st[6])):
                c = fmt_pred(st[2] if taken else NEG[st[2]], A, B)
                run(arm, lambda e, cs: run(stmts[1:], k, e, cs), env,
                    conds + [((st[1], taken), c)])
        else:
            out.append((tuple(kk for kk, _ in conds), [c for _, c in conds], env[st[1]]))

    run(body, lambda e, c: None, {a: a for a in ARGS[:nargs]}, [])
    return out


def walk(body):
    """Every statement, arms included, in linear order."""
    for st in body:
        yield st
        if st[0] == 'if':
            yield from walk(st[5])
            yield from walk(st[6])


def count_ops(body):
    return sum(1 for st in walk(body) if st[0] == 'op')


def count_ifs(body):
    return sum(1 for st in walk(body) if st[0] == 'if')


def is_nested(body):
    """True when an if sits inside an arm of another if."""
    for st in body:
        if st[0] == 'if' and (count_ifs(st[5]) or count_ifs(st[6])):
            return True
    return False


def uses_vshift(body):
    return any(st[0] == 'op' and st[2] in VSHIFTS for st in walk(body))


def show(body, ind=''):
    """Readable listing of a program (for the generated sources)."""
    lines = []
    for st in body:
        if st[0] == 'op':
            _, dst, kind, a, b = st
            lines.append(f'{ind}{dst} = {fmt_op(kind, a, b if type(b) is str else lit(b) if b is not None else None, b)}')
        elif st[0] == 'if':
            b = st[4] if type(st[4]) is str else lit(st[4])
            lines.append(f'{ind}if {fmt_pred(st[2], st[3], b)}:  # if {st[1]}')
            lines += show(st[5], ind + '    ')
            lines.append(f'{ind}else:')
            lines += show(st[6], ind + '    ')
        else:
            lines.append(f'{ind}return {st[1]}')
    return lines


# ---------------------------------------------------------------- random programs
KIND_W = [('add', 3.0), ('sub', 3.0), ('xor', 3.0), ('and', 2.0), ('or', 2.0), ('mul', 1.3),
          ('not', 0.5), ('neg', 0.5), ('shl', 0.8), ('shr', 0.8), ('sar', 0.5),
          ('rol', 0.7), ('ror', 0.7)]
VS_W = [('vshl', 0.35), ('vshr', 0.35), ('vsar', 0.2), ('vrol', 0.35), ('vror', 0.25)]


class Gen:
    """Random straight-line code with if / else; every value ends up used."""

    def __init__(self, rng, nargs, vshift):
        self.r = rng
        self.args = list(ARGS[:nargs])
        self.vshift = vshift
        self.nt = 0
        self.nif = 0
        self.uses = {a: 0 for a in self.args}
        self.size = {a: 1 for a in self.args}
        self.age = {a: 0 for a in self.args}
        self.clock = 1

    def new(self, size):
        self.nt += 1
        v = f't{self.nt}'
        self.uses[v] = 0
        self.size[v] = size
        self.age[v] = self.clock
        self.clock += 1
        return v

    def pick(self, pool, avoid=()):
        cands = [v for v in pool if v not in avoid]
        if not cands:
            return None
        ws = []
        for v in cands:
            w = 4.0 if self.uses[v] == 0 else (1.0 if self.uses[v] == 1 else 0.3)
            w *= 1.0 + 2.0 * self.age[v] / self.clock
            if self.size[v] > 60:
                w *= 0.3
            if self.size[v] > 150:
                w *= 0.05
            ws.append(w)
        return self.r.choices(cands, ws)[0]

    def imm(self, kind):
        r = self.r
        c = r.random()
        if kind == 'mul':
            v = r.choice([3, 5, 7, 9, 13, 31, 0x101, 0x9e37, -3, -7, -0x61c9]) if c < 0.6 \
                else (r.getrandbits(31) | 1)
        elif kind == 'and':
            v = r.choice([0xff, 0xffff, 0xfff0, 0x7fffffff, -256, -16, 0x0f0f0f0f]) if c < 0.5 \
                else r.randrange(-2**31, 2**31)
        else:
            v = r.randrange(1, 256) if c < 0.4 else r.randrange(-2**31, 2**31)
        return v & MASK

    def const(self, stmts):
        """A 64-bit constant that does not fit an imm32, in its own temporary."""
        t = self.new(1)
        stmts.append(('op', t, 'const', None, self.r.getrandbits(64) | (1 << 40)))
        return t

    def op(self, stmts, pool, dst=None, a=None):
        r = self.r
        table = KIND_W + (VS_W if self.vshift else [])
        kind = r.choices([k for k, _ in table], [w for _, w in table])[0]
        if a is None:
            a = self.pick(pool)
        b = None
        if kind in ALU:
            if r.random() < 0.28:
                b = self.imm(kind)
            elif r.random() < 0.06:
                b = self.const(stmts)
            else:
                b = self.pick(pool, avoid=(a,))
                if b is None:
                    b = self.imm(kind)
        elif kind in SHIFTS:
            b = r.randrange(1, 64)
        elif kind in VSHIFTS:
            b = self.pick(pool, avoid=(a,))
            if b is None:
                kind, b = kind[1:], r.randrange(1, 64)
        size = 1 + self.size[a] + (self.size[b] if type(b) is str else 1)
        self.uses[a] += 1
        if type(b) is str:
            self.uses[b] += 1
        if dst is None:
            dst = self.new(size)
        else:
            self.size[dst] = max(self.size[dst], size)
        stmts.append(('op', dst, kind, a, b))
        return dst

    def cond(self, stmts, pool):
        """(pred, a, b) of a new if; may first append a helper operation."""
        r = self.r
        a = self.pick(pool)
        c = r.random()
        if c < 0.35:
            b = self.pick(pool, avoid=(a,))
            if b is not None:
                return r.choice(['ult', 'ule', 'ugt', 'uge', 'slt', 'sle', 'sgt', 'sge']), a, b
        if c < 0.6:
            bits = r.sample(range(31), r.randint(1, 2))
            return r.choice(['tz', 'tnz']), a, sum(1 << k for k in bits)
        if c < 0.8:
            return r.choice(['slt', 'sle', 'sgt', 'sge']), a, r.randrange(-100, 101) & MASK
        if r.random() < 0.5:
            m = r.choice([3, 7, 15])
            t = self.new(self.size[a] + 2)
            stmts.append(('op', t, 'and', a, m))
            self.uses[a] += 1
            return r.choice(['eq', 'ne']), t, r.randrange(0, m + 1)
        k = r.choice([60, 61, 62])
        t = self.new(self.size[a] + 2)
        stmts.append(('op', t, 'shr', a, k))
        self.uses[a] += 1
        return r.choice(['eq', 'ne']), t, r.randrange(0, 1 << (64 - k))

    def make_if(self, stmts, pool, inner=False):
        """Append an if / else whose arms both define a new join variable; return it.
        inner: one arm holds a nested if."""
        r = self.r
        pred, a, b = self.cond(stmts, pool)
        self.uses[a] += 1
        if type(b) is str:
            self.uses[b] += 1
        self.nif += 1
        iid = self.nif
        j = self.new(0)
        inner_arm = r.randrange(2) if inner else -1
        arms = []
        for k in range(2):
            n = r.randint(1, 4)
            if k == inner_arm:
                n = max(n, 2)
            arms.append(self.arm(pool, j, n, k == inner_arm))
        stmts.append(('if', iid, pred, a, b, arms[0], arms[1]))
        self.age[j] = self.clock
        self.clock += 1
        return j

    def arm(self, pool, j, n, inner):
        """A chain of n operations (each uses the previous result), the last one
        defining j; inner: one step of the chain is a nested if."""
        stmts = []
        local = []
        prev = None
        at = self.r.randrange(n - 1) if inner else -1
        for i in range(n):
            if i == at:
                prev = self.make_if(stmts, pool + local)
                local.append(prev)
                continue
            d = self.op(stmts, pool + local, dst=j if i == n - 1 else None, a=prev)
            local.append(d)
            prev = d
        return stmts

    def program(self, n_ops, n_ifs, nested):
        r = self.r
        body = []
        pool = list(self.args)
        n_top = n_ifs - (1 if nested else 0)
        budget = max(n_top + 1, n_ops - 5 * n_ifs - 1)
        parts = [1] * (n_top + 1)
        for _ in range(budget - n_top - 1):
            parts[r.randrange(n_top + 1)] += 1
        for k, m in enumerate(parts):
            for _ in range(m):
                pool.append(self.op(body, pool))
            if k < n_top:
                pool.append(self.make_if(body, pool, inner=nested and k == 0))
        rest = [v for v in pool if self.uses[v] == 0]
        if pool[-1] not in rest:
            rest.insert(0, pool[-1])
        acc = rest[0]
        for v in rest[1:]:
            kind = r.choice(['add', 'xor', 'sub', 'add', 'xor', 'or', 'mul'])
            t = self.new(1 + self.size[acc] + self.size[v])
            body.append(('op', t, kind, acc, v))
            self.uses[acc] += 1
            self.uses[v] += 1
            acc = t
        body.append(('ret', acc))
        return body


# ---------------------------------------------------------------- paths and witnesses
EDGE = [0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x7fffffff, 0x80000000, 0xffffffff,
        2**63 - 1, 2**63, 2**64 - 2, 2**64 - 1]


def sample(r, nargs):
    """A random input [x, y, z, w] (zeros beyond nargs) mixing the usual distributions."""
    c = r.random()
    if c < 0.5:
        a = [r.getrandbits(64) for _ in range(nargs)]
    elif c < 0.65:
        a = [r.randrange(-8, 33) & MASK for _ in range(nargs)]
    elif c < 0.8:
        a = [r.choice(EDGE) for _ in range(nargs)]
    else:
        a = [r.getrandbits(r.randint(1, 64)) for _ in range(nargs)]
    return a + [0] * (4 - nargs)


Z3_RLIMIT = 30_000_000                          # z3 operation budget per query (deterministic)
Z3_MB = 1500                                    # z3 memory cap (MB)


def z3_witness(cond, nargs, rlimit=Z3_RLIMIT):
    """('sat', input) / ('unsat', None) / ('unknown', None) for cond, bounded by z3's
    deterministic resource limit (not by time) and a memory cap."""
    import z3
    import truth
    z3.set_param('memory_max_size', Z3_MB)
    xs = [z3.BitVec(v, 64) for v in ARGS]
    s = z3.Solver()
    s.set('rlimit', rlimit)
    s.add(truth.to_z3(cond, xs))
    s.add(*[v == 0 for v in xs[nargs:]])
    try:
        res = s.check()
    except z3.Z3Exception:
        return 'unknown', None
    if res == z3.sat:
        m = s.model()
        return 'sat', [m.eval(v, model_completion=True).as_long() for v in xs]
    return ('unsat' if res == z3.unsat else 'unknown'), None


def analyze(body, nargs, rng, samples=3000, node_cap=2500, allow_sat=True):
    """(paths, None) or (None, reason). paths: [{key, cond, out, witness}] of the
    feasible paths; infeasible combinations (z3 unsat) are dropped. The program is
    refused when a path is unknown to z3, an arm of an if is never feasible, an
    expression is too large, or the expressions disagree with the interpreter."""
    import truth
    plist = enumerate_paths(body, nargs)
    hits = {p[0]: [] for p in plist}
    for _ in range(samples):
        a = sample(rng, nargs)
        _, key = execute(body, a)
        if key not in hits:
            return None, f'path {key} not enumerated'
        if len(hits[key]) < 3 and a not in hits[key]:
            hits[key].append(a)
    paths = []
    for key, conds, out in plist:
        cond = ' and '.join(conds) if conds else 'True'
        if truth.nodes(cond) > node_cap or truth.nodes(out) > node_cap:
            return None, 'expression too large'
        ws = hits[key]
        if not ws:
            st, w = z3_witness(cond, nargs)
            if st == 'unsat':
                continue
            if st == 'sat' and not allow_sat:
                return None, f'path {key} feasible but missed by the sampling'
            if st != 'sat':
                return None, f'z3 {st} on path {key}'
            ws = [w]
        paths.append({'key': key, 'cond': cond, 'out': out, 'witness': ws})
    taken = {kk for p in paths for kk in p['key']}
    for st in walk(body):
        if st[0] == 'if' and not {(st[1], True), (st[1], False)} <= taken:
            return None, f'if {st[1]} has an arm that is never taken'
    return paths, None


def crosscheck(body, nargs, paths, rng, n=300):
    """None when, on the witnesses and n random inputs, exactly one path cond holds
    and its out equals the interpreter's result; else a message."""
    import truth
    cf = [(truth.compile(p['cond']), truth.compile(p['out'])) for p in paths]
    inputs = [w for p in paths for w in p['witness']] + [sample(rng, nargs) for _ in range(n)]
    for a in inputs:
        v, key = execute(body, a)
        hold = [k for k, (c, _) in enumerate(cf) if c(*a)]
        if len(hold) != 1:
            return f'{a}: {len(hold)} path conds hold'
        if paths[hold[0]]['key'] != key or cf[hold[0]][1](*a) != v:
            return f'{a}: expression and interpreter disagree'
    return None


# ---------------------------------------------------------------- degeneracy
def op_values(body, args):
    """(values, result): the value of every operation on args, in walk order, with the
    arms of every if evaluated whatever the branch (each one from the environment
    before the if; after the if the join variable takes the taken arm's value)."""
    vals = []

    def ex(stmts, env):
        for st in stmts:
            if st[0] == 'op':
                _, dst, kind, a, b = st
                env[dst] = ev_op(kind, env[a] if a else 0, value(env, b) if b is not None else 0)
                vals.append(env[dst])
            elif st[0] == 'if':
                taken = ev_pred(st[2], env[st[3]], value(env, st[4]))
                arms = (dict(env), dict(env))
                ex(st[5], arms[0])
                ex(st[6], arms[1])
                env.update(arms[0] if taken else arms[1])
            else:
                return env[st[1]]
        return None

    res = ex(body, dict(zip(ARGS, args)))
    return vals, res


def degenerate(body, nargs, paths, rng, n=300):
    """None, or why the program is degenerate, on n seeded random inputs:
      * an operation (other than a constant load) whose value never changes (the arms
        of every if evaluated whatever the branch), e.g. t2 = (x ^ k) ^ x;
      * a result that hardly depends on one of the arguments: re-drawing that argument
        (a new random value, or one bit flipped) changes it in fewer than 5% of cases;
      * a path out that is constant (over all inputs, or over the inputs of its own
        path when at least 10 of them were drawn);
      * two paths whose outs are the same function (the ifs between them are moot).
    paths: analyze's paths (key, out)."""
    import truth
    inputs = [sample(rng, nargs) for _ in range(n)]
    ops = [st for st in walk(body) if st[0] == 'op']
    seen = [set() for _ in ops]
    for a in inputs:
        vals, res = op_values(body, a)
        if res != execute(body, a)[0]:
            raise RuntimeError('op_values and execute disagree')
        for s, v in zip(seen, vals):
            s.add(v)
    for st, s in zip(ops, seen):
        if st[2] != 'const' and len(s) < 2:
            return f'{st[1]} = {st[2]}({st[3]}, {st[4]}) is always {lit(next(iter(s)))}'
    base = [execute(body, a) for a in inputs]
    for i in range(nargs):
        changed = 0
        for a, (v, _) in zip(inputs, base):
            b = list(a)
            b[i] = rng.getrandbits(64) if rng.random() < 0.5 else a[i] ^ (1 << rng.randrange(64))
            changed += execute(body, b)[0] != v
        if changed * 20 < n:
            return f'the result hardly depends on {ARGS[i]} ({changed} changes in {n})'
    table = []
    for k, p in enumerate(paths):
        f = truth.compile(p['out'])
        col = [f(*a) for a in inputs]
        if len(set(col)) < 2:
            return f'path {k} returns a constant'
        own = [v for v, key in base if key == p['key']]
        if len(own) >= 10 and len(set(own)) < 2:
            return f'path {k} returns a constant on its own inputs ({len(own)} drawn)'
        table.append(col)
    for j in range(len(paths)):
        for k in range(j):
            if table[j] == table[k]:
                return f'paths {k} and {j} return the same value'
    return None
