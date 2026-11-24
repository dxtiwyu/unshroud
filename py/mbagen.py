"""Generator of MBA expressions harder than the public sets (lines "obfuscated,groundtruth", the syntax unshroud_mbaset reads).
Every line is an identity by construction (linear MBA identities from exact integer linear algebra on truth tables,
substitution, distribution, null polynomials modulo 2^64) and is checked on 64-bit test values before it is written.
usage: python -I mbagen.py <out dir> [lines per tier] [seed]
Tiers: h_vars (linear, 5-8 variables), h_deep (identities substituted into identities, 3 levels, affine wrappers
distributed), h_poly (products of linear MBAs multiplied out, null polynomials added), h_width (8/16/32-bit results
computed in 64 bits: masks, junk above the mask, identities which hold modulo the width only)."""
import sys, random, itertools
M = (1 << 64) - 1

# expressions: ("v", name) ("c", value) ("~", a) ("neg", a) (op, a, b) with op in + - * & | ^
def V(n): return ("v", n)
def C(c): return ("c", c & M)
def ev(e, env):
    k = e[0]
    if k == "v": return env[e[1]]
    if k == "c": return e[1]
    if k == "~": return ~ev(e[1], env) & M
    if k == "neg": return -ev(e[1], env) & M
    a, b = ev(e[1], env), ev(e[2], env)
    if k == "+": return (a + b) & M
    if k == "-": return (a - b) & M
    if k == "*": return (a * b) & M
    if k == "&": return a & b
    if k == "|": return a | b
    if k == "^": return a ^ b
    raise ValueError(k)
def size(e):
    return 1 if e[0] in "vc" else 1 + sum(size(x) for x in e[1:])
def show(e):
    k = e[0]
    if k == "v": return e[1]
    if k == "c": return str(e[1])
    if k == "~": return "~" + atom(e[1])
    if k == "neg": return "-" + atom(e[1])
    return atom(e[1]) + k + atom(e[2])
def atom(e):
    return show(e) if e[0] in "vc" else "(" + show(e) + ")"
def variables(e, acc=None):
    acc = set() if acc is None else acc
    if e[0] == "v": acc.add(e[1])
    elif e[0] != "c":
        for x in e[1:]: variables(x, acc)
    return acc
def subst(e, m):
    if e[0] == "v": return m.get(e[1], e)
    if e[0] == "c": return e
    return (e[0],) + tuple(subst(x, m) for x in e[1:])

def tests(names, rng, n=40):
    out = []
    special = [0, 1, M, 1 << 63, (1 << 63) - 1, 0xff, 0x100, 0xffff, 0x10000, 0xffffffff, 1 << 32, 0x5555555555555555, 0xaaaaaaaaaaaaaaaa]
    for i in range(n):
        env = {}
        for v in names:
            r = rng.random()
            env[v] = rng.choice(special) if r < 0.3 else rng.getrandbits(64) if r < 0.8 else rng.getrandbits(8)
        out.append(env)
    return out
def same(a, b, rng):
    names = sorted(variables(a) | variables(b))
    return all(ev(a, env) == ev(b, env) for env in tests(names, rng))

# ---- bitwise formulas and their truth tables (bit r of the table: the value on row r, variable i being bit i of r)
def rand_bitwise(names, rng, depth):
    if depth == 0 or rng.random() < 0.25:
        v = V(rng.choice(names))
        return ("~", v) if rng.random() < 0.3 else v
    op = rng.choice("&|^")
    e = (op, rand_bitwise(names, rng, depth - 1), rand_bitwise(names, rng, depth - 1))
    return ("~", e) if rng.random() < 0.25 else e
def table(e, names):
    t = len(names); rows = 1 << t; full = (1 << rows) - 1
    env = {}
    for i, v in enumerate(names):
        env[v] = sum(1 << r for r in range(rows) if (r >> i) & 1)
    def go(x):
        k = x[0]
        if k == "v": return env[x[1]]
        if k == "~": return ~go(x[1]) & full
        a, b = go(x[1]), go(x[2])
        return a & b if k == "&" else a | b if k == "|" else a ^ b
    return go(e)

# ---- linear MBA identities. A sum of bitwise formulas with integer coefficients (and a constant) is determined by its
# values on the corners (every variable 0 or all ones): two such sums are equal for every input iff they are equal there.
def corners(names):
    out = []
    for r in range(1 << len(names)):
        out.append({v: (M if (r >> i) & 1 else 0) for i, v in enumerate(names)})
    return out
def signed(x): return x - (1 << 64) if x >> 63 else x
def vector(e, names): return [signed(ev(e, env)) for env in corners(names)]

class Pool:
    """Small bitwise formulas over `names`, the smallest one found per truth table (the all-ones table is the constant -1)."""
    def __init__(self, names, rng, tries=4000):
        self.names = names; self.rows = 1 << len(names); self.full = (1 << self.rows) - 1
        self.f = {}
        def add(e):
            t = table(e, names)
            if t == 0 or t == self.full: return
            if t not in self.f or size(e) < size(self.f[t]): self.f[t] = e
        for k in range(1, len(names) + 1):                # the conjunctions (a basis by themselves)
            for sub in itertools.combinations(names, k):
                e = V(sub[0])
                for v in sub[1:]: e = ("&", e, V(v))
                add(e)
        for _ in range(tries): add(rand_bitwise(names, rng, 3 if len(names) > 2 else 2))
        self.tables = sorted(self.f)
    def formula(self, t): return self.f[t]
    def conj_basis(self):
        out = [self.full]
        for k in range(1, len(self.names) + 1):
            for sub in itertools.combinations(self.names, k):
                e = V(sub[0])
                for v in sub[1:]: e = ("&", e, V(v))
                out.append(table(e, self.names))
        return out
    def random_basis(self, rng, steps=300):
        """2^t truth tables whose 0/1 matrix has determinant +-1: from the conjunction basis by steps which keep it
        (a column plus a disjoint one, a column minus one it contains)."""
        b = self.conj_basis()
        for _ in range(steps):
            i, j = rng.randrange(len(b)), rng.randrange(len(b))
            if i == j: continue
            if b[i] & b[j] == 0: n = b[i] | b[j]
            elif b[j] & ~b[i] == 0: n = b[i] & ~b[j]
            else: continue
            if n == 0 or n in b or (n != self.full and n not in self.f): continue
            b[i] = n
        return b

def solve_unimodular(cols, rhs, rows):
    """y with sum_k y[k] * bit(cols[k], row) = rhs[row] for every row (integers; the matrix has determinant +-1)."""
    from fractions import Fraction
    n = len(cols)
    A = [[Fraction((cols[k] >> r) & 1) for k in range(n)] + [Fraction(rhs[r])] for r in range(rows)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        inv = 1 / A[c][c]
        A[c] = [x * inv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]; A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    y = [A[r][n] for r in range(n)]
    assert all(v.denominator == 1 for v in y)
    return [int(v) for v in y]

def identity_terms(target, pool, rng, extra, coef=7):
    """Terms [(coefficient, formula or None for the constant)] whose sum equals the linear MBA `target` (an expression
    over the pool's variables, or a list of corner values): `extra` random terms, the rest solved for on a random basis."""
    names = pool.names; rows = pool.rows
    w = target if isinstance(target, list) else vector(target, names)
    acc = {}                                              # table -> coefficient
    for _ in range(extra):
        t = rng.choice(pool.tables); a = rng.choice([c for c in range(-coef, coef + 1) if c])
        acc[t] = acc.get(t, 0) + a
    # corner value of a formula with table t on row r: -bit(t, r)
    res = [w[r] + sum(a * ((t >> r) & 1) for t, a in acc.items()) for r in range(rows)]
    basis = pool.random_basis(rng)
    y = solve_unimodular(basis, [-x for x in res], rows)
    for t, c in zip(basis, y): acc[t] = acc.get(t, 0) + c
    terms = []
    for t, c in acc.items():
        if c == 0: continue
        if t == pool.full: terms.append((-c, None))       # c * (-1)
        else: terms.append((c, pool.formula(t)))
    rng.shuffle(terms)
    return terms

def term_expr(c, f):
    """|c| * f as an expression (f None: the constant), and whether it is subtracted."""
    neg = c < 0; a = -c if neg else c
    if f is None: return C(a), neg
    return (f if a == 1 else ("*", C(a), f)), neg
def sum_expr(terms):
    if not terms: return C(0)
    e = None
    for c, f in terms:
        t, neg = term_expr(c, f)
        if e is None: e = ("neg", t) if neg else t
        else: e = ("-", e, t) if neg else ("+", e, t)
    return e

# ---- the tiers
_pools = {}
def pool_for(names, rng):
    key = tuple(names)
    if key not in _pools: _pools[key] = Pool(list(key), random.Random(sum(ord(ch) * (i + 7) for i, ch in enumerate("".join(key)))), 1500)
    return _pools[key]

def linear_truth(vs, rng):
    x, y, z = (V(v) for v in vs)
    return rng.choice([("+", x, y), ("-", x, y), ("^", x, y), ("|", x, y), ("&", x, y), ("+", ("^", x, y), z), ("-", ("&", x, y), z),
                       ("+", ("|", x, y), ("&", y, z)), ("-", ("+", x, y), z), ("+", ("*", C(2), ("|", x, y)), z), ("-", ("~", x), y),
                       ("+", ("^", x, z), ("*", C(3), y)), ("-", ("|", x, z), ("&", x, y)), ("+", ("+", x, y), C(1))])

def tier_vars(rng):
    """Linear MBA in 5-8 variables: the truth (three of them) plus zero identities over other triples."""
    n = rng.randint(5, 8); names = list("abcdefgh")[:n]
    tv = sorted(rng.sample(names, 3)); truth = linear_truth(rng.sample(tv, 3), rng)
    other = rng.choice([v for v in names if v not in tv])
    terms = identity_terms(truth, pool_for(sorted(tv + [other]), rng), rng, rng.randint(3, 5))
    for _ in range(rng.randint(3, 5)):
        sub = sorted(rng.sample(names, 3)); p = pool_for(sub, rng)
        terms += identity_terms([0] * p.rows, p, rng, rng.randint(3, 5))
    rng.shuffle(terms)
    return sum_expr(terms), truth

def affine(terms, rng):
    """a^-1 * (sum of a * terms + b) - a^-1 * b with the outer multiplication left to the reader (a odd)."""
    a = rng.getrandbits(64) | 1; b = rng.getrandbits(64); ai = pow(a, -1, 1 << 64)
    inner = None
    for c, f in terms:
        t = C(c * a) if f is None else ("*", C(c * a), f)
        inner = t if inner is None else ("+", inner, t)
    inner = ("+", inner, C(b))
    return ("-", ("*", C(ai), inner), C(ai * b))

def deepen(e, rng):
    """Every + - & | ^ of e replaced by a linear identity in its two operands (themselves replaced first)."""
    if e[0] in "vc": return e
    if e[0] in ("~", "neg"): return (e[0], deepen(e[1], rng))
    A, B = deepen(e[1], rng), deepen(e[2], rng)
    if e[0] == "*": return ("*", A, B)
    p = pool_for(["p", "q"], rng)
    terms = identity_terms((e[0], V("p"), V("q")), p, rng, rng.randint(1, 2), coef=4)
    body = affine(terms, rng) if rng.random() < 0.35 else sum_expr(terms)
    return subst(body, {"p": A, "q": B})

def tier_deep(rng):
    x, y, z = (V(v) for v in rng.sample(["x", "y", "z"], 3))
    truth = rng.choice([("^", ("+", x, y), z), ("+", ("&", x, y), ("|", x, z)), ("&", ("-", x, y), ("+", y, z)), ("|", ("~", ("+", x, y)), z),
                        ("+", ("-", ("^", x, y), ("&", y, z)), x), ("^", ("|", x, y), ("-", z, x)), ("-", ("&", ("+", x, z), y), ("^", x, y)),
                        ("&", ("^", ("+", x, y), z), ("|", x, ("-", y, z))), ("+", ("^", ("&", x, y), ("+", y, z)), ("|", z, x))])
    for _ in range(20):
        e = deepen(truth, rng)
        if len(show(e)) <= 30000: return e, truth
    return None

def product_terms(t1, t2):
    out = []
    for c1, f1 in t1:
        for c2, f2 in t2:
            f = None if f1 is None and f2 is None else f2 if f1 is None else f1 if f2 is None else ("*", f1, f2)
            out.append((c1 * c2, f))
    return out

def tier_poly(rng):
    """Products of linear MBAs, multiplied out term by term, with terms which are zero for every input added."""
    names = ["x", "y", "z"]; x, y, z = (V(v) for v in rng.sample(names, 3)); p = pool_for(names, rng)
    lin = [x, y, ("&", x, y), ("|", x, y), ("^", x, y), ("+", x, y), ("-", x, y), ("~", x), ("+", x, C(1)), ("|", x, z), ("^", y, z)]
    f1, f2 = rng.choice(lin), rng.choice(lin)
    truth = ("*", f1, f2); terms = product_terms(identity_terms(f1, p, rng, 2, coef=3), identity_terms(f2, p, rng, 2, coef=3))
    r = rng.random()
    if r < 0.4:
        f3 = rng.choice(lin[:7] + [z]); truth = (rng.choice("+-"), truth, f3)
        terms += [(c if truth[0] == "+" else -c, f) for c, f in identity_terms(f3, p, rng, 2, coef=3)]
    elif r < 0.55:
        truth = ("*", truth, z); terms = product_terms(terms, [(1, z)])
    g = p.formula(rng.choice(p.tables))
    if rng.random() < 0.6:                                 # (a zero identity) * g
        terms += product_terms(identity_terms([0] * p.rows, p, rng, 2, coef=3), [(rng.choice([1, -1, 2]), g)])
    if rng.random() < 0.6:                                 # 2^63 * g * (g + 1): g * (g + 1) is even
        h = p.formula(rng.choice(p.tables)); terms += [(1 << 63, ("*", h, h)), (1 << 63, h)]
    rng.shuffle(terms)
    return sum_expr(terms), truth

def tier_width(rng):
    """An 8/16/32-bit result computed in 64 bits: the sum only has to be right below the mask (coefficients off by
    multiples of 2^W, operands masked wider than the result, terms which vanish modulo 2^W), the mask comes last."""
    W = rng.choice([8, 16, 32]); m = (1 << W) - 1
    names = ["x", "y", "z"]; p = pool_for(names, rng)
    if rng.random() < 0.3:
        x, y, z = (V(v) for v in rng.sample(names, 3))
        f1, f2 = rng.choice([x, ("&", x, y), ("|", x, z), ("+", x, y)]), rng.choice([y, z, ("^", y, z), ("-", y, C(1))])
        inner = ("*", f1, f2); terms = product_terms(identity_terms(f1, p, rng, 2, coef=3), identity_terms(f2, p, rng, 2, coef=3))
    else:
        inner = linear_truth(rng.sample(names, 3), rng); terms = identity_terms(inner, p, rng, rng.randint(3, 5))
    def masked(f):                                         # an operand masked at least as wide as the result
        if f is None or rng.random() > 0.4: return f
        w2 = rng.choice([w for w in (8, 16, 32, 48) if w >= W])
        if f[0] == "*": return ("*", ("&", f[1], C((1 << w2) - 1)), f[2]) if rng.random() < 0.5 else ("&", f, C((1 << w2) - 1))
        return ("&", f, C((1 << w2) - 1))
    out = []
    for c, f in terms: out.append((c + (rng.randint(-3, 3) << W), masked(f)))
    for _ in range(rng.randint(1, 3)): out.append((rng.choice([1, -1, 3, 5]) << W, p.formula(rng.choice(p.tables))))
    if rng.random() < 0.5:
        h = p.formula(rng.choice(p.tables)); out += [(1 << (W - 1), ("*", h, h)), (1 << (W - 1), h)]
    rng.shuffle(out)
    obf = ("&", sum_expr(out), C(m)); truth = ("&", inner, C(m))
    if rng.random() < 0.3:                                 # sign extension of the W-bit result
        s = 1 << (W - 1); obf = ("-", ("^", obf, C(s)), C(s)); truth = ("-", ("^", truth, C(s)), C(s))
    return obf, truth

TIERS = [("h_vars", tier_vars, "linear MBA, 5-8 variables (the truth uses 3): identities over overlapping triples of variables"),
         ("h_deep", tier_deep, "every operation of a nested expression replaced by a linear identity in its operands, some inside a*x+b wrappers with a 64-bit a"),
         ("h_poly", tier_poly, "products of linear MBAs multiplied out, zero identities times a term and 2^63*t*(t+1) added"),
         ("h_width", tier_width, "8/16/32-bit results computed in 64 bits: junk above the mask, operands masked wider, terms zero modulo 2^W")]

def main():
    out = sys.argv[1]; n = int(sys.argv[2]) if len(sys.argv) > 2 else 250; seed = int(sys.argv[3]) if len(sys.argv) > 3 else 20261117
    for name, fn, what in TIERS:
        rng = random.Random(seed ^ sum(ord(ch) * (i + 3) for i, ch in enumerate(name))); chk = random.Random(seed + 1)
        lines = []; tries = 0; sizes = []; tsizes = []
        while len(lines) < n and tries < 20 * n:
            tries += 1
            r = fn(rng)
            if r is None: continue
            e, truth = r
            if not same(e, truth, chk): raise SystemExit("%s: a generated line is not an identity: %s" % (name, show(truth)))
            lines.append(show(e) + "," + show(truth)); sizes.append(size(e)); tsizes.append(size(truth))
        with open("%s/%s.txt" % (out, name), "w", newline="\n") as f:
            f.write("# %s: %s\n# obfuscated,groundtruth (64-bit; generated by mbagen.py, seed %d; every line checked on test values)\n" % (name, what, seed))
            for l in lines: f.write(l + "\n")
        print("%-8s %d lines, tree size of the expressions: mean %.0f, max %d; of the truths: mean %.1f; longest line %d characters" % (
            name, len(lines), sum(sizes) / max(1, len(sizes)), max(sizes), sum(tsizes) / max(1, len(tsizes)), max(len(l) for l in lines)))

if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] != "x": main()
