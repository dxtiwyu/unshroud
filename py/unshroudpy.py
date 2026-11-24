"""Exact semantics of the unshroud expression operations (mirrors evalOp in src/expr.cpp): op(code, w, lo, a, b, c)."""
OPS = ["none", "const", "var", "add", "mul", "udiv", "urem", "sdiv", "srem", "mulhu", "mulhs", "neg", "and", "or", "xor", "not",
       "shl", "lshr", "ashr", "rol", "ror", "extract", "zext", "sext", "concat", "ite", "eq", "ult", "ule", "slt", "sle", "popcnt", "clz", "ctz"]
C = {name: i for i, name in enumerate(OPS)}

def M(w): return (1 << w) - 1
def sx(v, w): v &= M(w); return v - (1 << w) if v >> (w - 1) else v

def op(code, w, lo, a, b, c):
    n = OPS[code]; m = M(w)
    if n == "add": return (a + b) & m
    if n == "mul": return (a * b) & m
    if n == "udiv": return m if b == 0 else a // b
    if n == "urem": return a if b == 0 else a % b
    if n in ("sdiv", "srem"):
        sa, sb = sx(a, w), sx(b, w)
        if sb == 0: return m if (n == "sdiv" and sa >= 0) else (1 if n == "sdiv" else a)
        q = abs(sa) // abs(sb)
        if n == "sdiv": return (-q if (sa < 0) != (sb < 0) else q) & m
        r = abs(sa) - q * abs(sb)
        return (-r if sa < 0 else r) & m
    if n == "mulhu": return ((a * b) >> w) & m
    if n == "mulhs": return ((sx(a, w) * sx(b, w)) >> w) & m
    if n == "neg": return (-a) & m
    if n == "and": return a & b
    if n == "or": return a | b
    if n == "xor": return a ^ b
    if n == "not": return (~a) & m
    if n == "shl": return 0 if b >= w else (a << b) & m
    if n == "lshr": return 0 if b >= w else a >> b
    if n == "ashr": return (sx(a, w) >> min(b, w - 1)) & m
    if n in ("rol", "ror"):
        r = b % w
        if n == "ror": r = (w - r) % w
        return ((a << r) | (a >> (w - r))) & m if r else a
    if n == "extract": return (a >> lo) & m
    if n == "zext": return a
    if n == "sext": return sx(a, lo) & m
    if n == "concat": return ((a << lo) | b) & m
    if n == "ite": return b if a & 1 else c
    if n == "eq": return int(a == b)
    if n == "ult": return int(a < b)
    if n == "ule": return int(a <= b)
    if n == "slt": return int(sx(a, lo) < sx(b, lo))
    if n == "sle": return int(sx(a, lo) <= sx(b, lo))
    if n == "popcnt": return bin(a).count("1")
    if n == "clz": return lo if a == 0 else lo - a.bit_length()
    if n == "ctz": return lo if a == 0 else (a & -a).bit_length() - 1
    raise ValueError(n)
