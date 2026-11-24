"""truth.py: exact evaluator of the bench expression language.

The full reference (language and JSON format) is the docstring of validate.py.
The language: Python syntax over x, y, z, w (arguments 1..4 = rcx, rdx, r8, r9,
unsigned 64-bit); operators + - * & | ^ ~ << >> and unary - (every result taken
mod 2**64, >> is logical, ~ is the 64-bit NOT); integer literals (decimal or 0x,
below 2**64); helpers s64(e) (signed view, only as an operand of a comparison),
sar(a, k), rol(a, k), ror(a, k), udiv(a, b), urem(a, b), mulhu(a, b);
comparisons == != < <= > >= (unsigned unless an operand is s64(...)); and, or,
not, True (False is accepted too).

Exact rules where Python syntax alone does not say:
  * a << k and a >> k with k >= 64 give 0; sar(a, k) with k >= 64 gives 0 or
    2**64-1 (the sign of a); rol / ror rotate by k mod 64.
  * udiv(a, 0) = 2**64-1, urem(a, 0) = a. Suites must not divide by zero: this
    only keeps the evaluator total. mulhu(a, b) = (a * b) >> 64.
    These choices agree with SMT-LIB (bvshl, bvlshr, bvashr, bvudiv, bvurem).
  * A comparison is signed when either of its two operands is s64(...): both
    64-bit values are then read as two's complement (s64(x) < 0: x negative).
    A chain a < b < c means (a < b) and (b < c), pair by pair.
  * Precedence is Python's: x & y == 0 is (x & y) == 0, x + y << 2 is
    (x + y) << 2, x ^ y & z is x ^ (y & z), not a == b is not (a == b).
  * Values and conditions do not mix: no arithmetic on a comparison, no value
    used as a condition. cond is a condition; out / truth / dead_out are values.

API
  parse(expr, kind=None) -> 'val' | 'bool'   raises ExprError with the reason
  parse_ok(expr, kind=None) -> bool          kind: None, 'val' or 'bool'
  ev(expr, args) -> int | bool               reference evaluator (U64 wrapper class),
                                             args padded with zeros to (x, y, z, w)
  compile(expr) -> f(x=0, y=0, z=0, w=0)     fast callable (generated straight-line
                                             Python on ints, cached); same results as ev
  nodes(expr) -> int                         AST size: leaves + operator applications
                                             (a chain of n operands counts n - 1)
  variables(expr) -> set of x / y / z / w used
  to_z3(expr, xs=None) -> z3 term over 64-bit bit-vectors (z3 imported on demand)
"""
import ast
import builtins
import functools
import re
import sys

MASK = (1 << 64) - 1
SIGN = 1 << 63
VARS = ('x', 'y', 'z', 'w')
HELPERS = {'s64': 1, 'sar': 2, 'rol': 2, 'ror': 2, 'udiv': 2, 'urem': 2, 'mulhu': 2}
VAL, BOOL, SVAL = 'val', 'bool', 'sval'

# The checker, the code generator and to_z3 recurse once or twice per AST level;
# Python frames cost no C stack since 3.11. Python's own parser stops near 2500 levels
# (x + x + ... with 2000 terms is fine), 200 nested parentheses.
if sys.getrecursionlimit() < 20000:
    sys.setrecursionlimit(20000)

_BIN = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.BitAnd: '&', ast.BitOr: '|',
        ast.BitXor: '^', ast.LShift: '<<', ast.RShift: '>>'}
_CMP = {ast.Eq: '==', ast.NotEq: '!=', ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>='}
_LIT = re.compile('0[xX][0-9a-fA-F]+|0|[1-9][0-9]*')
_WHAT = {VAL: 'a 64-bit value', BOOL: 'a condition', SVAL: 's64(...)'}


class ExprError(ValueError):
    """The expression is not in the language (the message says why)."""


def _fail(node, src, msg):
    seg = None
    if hasattr(node, 'lineno'):
        seg = ast.get_source_segment(src, node)
    if seg is not None and seg != src:
        msg = f'{msg} (at {seg!r})'
    raise ExprError(msg)


def _need(node, src, kind):
    k = _check(node, src)
    if k != kind:
        _fail(node, src, f'expected {_WHAT[kind]}, found {_WHAT[k]}')


def _is_s64(node):
    return type(node) is ast.Call and type(node.func) is ast.Name and node.func.id == 's64'


def _check(node, src, cmp_operand=False):
    """Type of node: VAL, BOOL or (only as a comparison operand) SVAL."""
    t = type(node)
    if t is ast.Name:
        if node.id in VARS:
            return VAL
        _fail(node, src, f'unknown name {node.id!r} (the variables are x, y, z, w)')
    if t is ast.Constant:
        v = node.value
        if v is True or v is False:
            return BOOL
        if type(v) is not int:
            _fail(node, src, f'literal {v!r} is not an integer')
        text = ast.get_source_segment(src, node)
        if text is None or not _LIT.fullmatch(text):
            _fail(node, src, f'integer literal {text!r}: write decimal or 0x hex')
        if v > MASK:
            _fail(node, src, f'literal {text} does not fit in 64 bits')
        return VAL
    if t is ast.BinOp:
        if type(node.op) not in _BIN:
            _fail(node, src, f'operator {type(node.op).__name__} is not in the language')
        _need(node.left, src, VAL)
        _need(node.right, src, VAL)
        return VAL
    if t is ast.UnaryOp:
        op = type(node.op)
        if op is ast.Not:
            _need(node.operand, src, BOOL)
            return BOOL
        if op is ast.USub or op is ast.Invert:
            _need(node.operand, src, VAL)
            return VAL
        _fail(node, src, 'unary + is not in the language')
    if t is ast.BoolOp:
        for v in node.values:
            _need(v, src, BOOL)
        return BOOL
    if t is ast.Compare:
        for op in node.ops:
            if type(op) not in _CMP:
                _fail(node, src, f'comparison {type(op).__name__} is not in the language')
        for v in [node.left] + node.comparators:
            if _check(v, src, True) == BOOL:
                _fail(v, src, 'a condition cannot be an operand of a comparison')
        return BOOL
    if t is ast.Call:
        f = node.func
        if type(f) is not ast.Name or f.id not in HELPERS:
            _fail(node, src, 'unknown function (the helpers are ' + ', '.join(HELPERS) + ')')
        n = HELPERS[f.id]
        if node.keywords or len(node.args) != n or any(type(a) is ast.Starred for a in node.args):
            _fail(node, src, f'{f.id}() takes {n} positional argument(s)')
        for a in node.args:
            _need(a, src, VAL)
        if f.id == 's64':
            if not cmp_operand:
                _fail(node, src, 's64() is only allowed as an operand of a comparison')
            return SVAL
        return VAL
    _fail(node, src, f'{t.__name__} is not in the language')


@functools.lru_cache(maxsize=None)
def _parse(expr):
    src = expr.strip()
    if not src:
        raise ExprError('empty expression')
    try:
        tree = ast.parse(src, mode='eval')
        kind = _check(tree.body, src)
    except SyntaxError as e:
        raise ExprError(f'syntax error: {e.msg}') from None
    except (RecursionError, MemoryError):
        raise ExprError('expression nested too deeply') from None
    return tree, src, kind


def parse(expr, kind=None):
    """Check expr; return its type 'val' or 'bool'. Raises ExprError."""
    if not isinstance(expr, str):
        raise ExprError(f'an expression is a string, not {type(expr).__name__}')
    k = _parse(expr)[2]
    if kind is not None and k != kind:
        raise ExprError(f'expected {_WHAT[kind]}, found {_WHAT[k]}: {expr!r}')
    return k


def parse_ok(expr, kind=None):
    """True when expr is in the language (and of the given kind: 'val' / 'bool')."""
    try:
        parse(expr, kind)
        return True
    except ExprError:
        return False


def variables(expr):
    """Set of the variables (x, y, z, w) that expr uses."""
    parse(expr)
    return {n.id for n in ast.walk(_parse(expr)[0]) if type(n) is ast.Name and n.id in VARS}


def _count(n):
    t = type(n)
    if t is ast.Name or t is ast.Constant:
        return 1
    if t is ast.BinOp:
        return 1 + _count(n.left) + _count(n.right)
    if t is ast.UnaryOp:
        return 1 + _count(n.operand)
    if t is ast.BoolOp:
        return len(n.values) - 1 + sum(_count(v) for v in n.values)
    if t is ast.Compare:
        return len(n.ops) + _count(n.left) + sum(_count(v) for v in n.comparators)
    return 1 + sum(_count(a) for a in n.args)          # ast.Call


def nodes(expr):
    """AST node count: leaves + operator applications (a chain of n operands counts n - 1)."""
    parse(expr)
    return _count(_parse(expr)[0].body)


# ---------------------------------------------------------------- reference evaluator
class U64:
    """An unsigned 64-bit value: every operation masks its result to 64 bits."""
    __slots__ = ('v',)

    def __init__(self, v):
        self.v = v & MASK

    def __repr__(self):
        return f'U64({self.v:#x})'

    def signed(self):
        return self.v - ((self.v & SIGN) << 1)

    def __add__(a, b): return U64(a.v + b.v)
    def __sub__(a, b): return U64(a.v - b.v)
    def __mul__(a, b): return U64(a.v * b.v)
    def __and__(a, b): return U64(a.v & b.v)
    def __or__(a, b): return U64(a.v | b.v)
    def __xor__(a, b): return U64(a.v ^ b.v)
    def __lshift__(a, b): return U64(a.v << b.v) if b.v < 64 else U64(0)
    def __rshift__(a, b): return U64(a.v >> b.v)
    def __invert__(a): return U64(~a.v)
    def __neg__(a): return U64(-a.v)

    def __bool__(self):
        raise TypeError('a 64-bit value used as a condition')

    # unsigned comparisons; against s64(...) both sides are read as signed
    def __eq__(a, b): return a.v == b.v if type(b) is U64 else a.signed() == b.v
    def __ne__(a, b): return a.v != b.v if type(b) is U64 else a.signed() != b.v
    def __lt__(a, b): return a.v < b.v if type(b) is U64 else a.signed() < b.v
    def __le__(a, b): return a.v <= b.v if type(b) is U64 else a.signed() <= b.v
    def __gt__(a, b): return a.v > b.v if type(b) is U64 else a.signed() > b.v
    def __ge__(a, b): return a.v >= b.v if type(b) is U64 else a.signed() >= b.v


class S64:
    """s64(e): the signed view of a 64-bit value; its comparisons are signed."""
    __slots__ = ('v',)

    def __init__(self, u):
        self.v = u.signed()

    def __repr__(self):
        return f'S64({self.v})'

    def __bool__(self):
        raise TypeError('s64(...) used as a condition')

    @staticmethod
    def _o(b):
        return b.v if type(b) is S64 else b.signed()

    def __eq__(a, b): return a.v == S64._o(b)
    def __ne__(a, b): return a.v != S64._o(b)
    def __lt__(a, b): return a.v < S64._o(b)
    def __le__(a, b): return a.v <= S64._o(b)
    def __gt__(a, b): return a.v > S64._o(b)
    def __ge__(a, b): return a.v >= S64._o(b)


def _r_sar(a, k):
    return U64(a.signed() >> min(k.v, 63))


def _r_rol(a, k):
    k = k.v % 64
    return U64((a.v << k) | (a.v >> (64 - k)))


def _r_ror(a, k):
    k = k.v % 64
    return U64((a.v >> k) | (a.v << (64 - k)))


_REF = {'__builtins__': {}, 's64': S64, 'sar': _r_sar, 'rol': _r_rol, 'ror': _r_ror,
        'udiv': lambda a, b: U64(a.v // b.v) if b.v else U64(MASK),
        'urem': lambda a, b: U64(a.v % b.v) if b.v else U64(a.v),
        'mulhu': lambda a, b: U64((a.v * b.v) >> 64)}


def _lit(node, consts):
    name = f'_k{len(consts)}'
    consts[name] = U64(node.value)
    return ast.copy_location(ast.Name(id=name, ctx=ast.Load()), node)


@functools.lru_cache(maxsize=None)
def _ref_code(expr):
    """Code object of expr with its integer literals bound to U64 constants."""
    tree = ast.parse(_parse(expr)[1], mode='eval')     # a fresh tree: the cached one stays intact
    consts = {}
    for node in ast.walk(tree):                         # iterative: no recursion limit
        for field, value in ast.iter_fields(node):
            if isinstance(value, list):
                for i, v in enumerate(value):
                    if type(v) is ast.Constant and type(v.value) is int:
                        value[i] = _lit(v, consts)
            elif type(value) is ast.Constant and type(value.value) is int:
                setattr(node, field, _lit(value, consts))
    ns = dict(_REF)
    ns.update(consts)
    return builtins.compile(tree, '<expr>', 'eval'), ns


def _args4(args):
    a = [int(v) & MASK for v in args]
    if len(a) > 4:
        raise ValueError(f'at most 4 arguments, got {len(a)}')
    return a + [0] * (4 - len(a))


def ev(expr, args=()):
    """Value of expr (int in [0, 2**64) or bool) for args = (x, y, z, w), zero-padded."""
    parse(expr)
    code, ns = _ref_code(expr)
    a = _args4(args)
    env = dict(ns)
    env.update(x=U64(a[0]), y=U64(a[1]), z=U64(a[2]), w=U64(a[3]))
    r = eval(code, env)
    if type(r) is U64:
        return r.v
    if type(r) is bool:
        return r
    raise TypeError(f'{expr!r} evaluated to {r!r}')


# ---------------------------------------------------------------- fast compiled form
def _shl(a, k):
    return (a << k) & MASK if k < 64 else 0


def _sar(a, k):
    if k > 63:
        k = 63
    return ((a - ((a & SIGN) << 1)) >> k) & MASK


def _rol(a, k):
    k &= 63
    return ((a << k) | (a >> (64 - k))) & MASK


def _ror(a, k):
    k &= 63
    return ((a >> k) | (a << (64 - k))) & MASK


def _udiv(a, b):
    return a // b if b else MASK


def _urem(a, b):
    return a % b if b else a


_FAST = {'__builtins__': {}, 'M': MASK, 'S': SIGN, '_shl': _shl, '_sar': _sar,
         '_rol': _rol, '_ror': _ror, '_udiv': _udiv, '_urem': _urem}


class _Gen:
    """Straight-line Python over ints: one temporary per distinct subterm."""

    def __init__(self):
        self.lines = []
        self.memo = {}

    def tmp(self, code):
        t = self.memo.get(code)
        if t is None:
            t = f't{len(self.memo)}'
            self.memo[code] = t
            self.lines.append(f'{t} = {code}')
        return t

    def val(self, n):
        """A name or literal holding the value of n (all operands are atoms)."""
        t = type(n)
        if t is ast.Name:
            return n.id
        if t is ast.Constant:
            return repr(n.value)
        if t is ast.BinOp:
            op = _BIN[type(n.op)]
            a = self.val(n.left)
            b = self.val(n.right)
            if op in ('+', '-', '*'):
                return self.tmp(f'({a} {op} {b}) & M')
            if op == '<<':
                return self.tmp(f'_shl({a}, {b})')
            return self.tmp(f'{a} {op} {b}')
        if t is ast.UnaryOp:
            op = type(n.op)
            a = self.val(n.operand)
            if op is ast.USub:
                return self.tmp(f'-{a} & M')
            if op is ast.Invert:
                return self.tmp(f'{a} ^ M')
            return self.tmp(f'not {a}')
        if t is ast.BoolOp:
            vals = [self.val(v) for v in n.values]
            return self.tmp((' and ' if type(n.op) is ast.And else ' or ').join(vals))
        if t is ast.Compare:
            ops = [n.left] + n.comparators
            vals = [self.val(o.args[0]) if _is_s64(o) else self.val(o) for o in ops]
            parts = []
            for i, op in enumerate(n.ops):
                a, b = vals[i], vals[i + 1]
                if _is_s64(ops[i]) or _is_s64(ops[i + 1]):
                    a, b = f'({a} ^ S)', f'({b} ^ S)'    # signed order = unsigned order of a ^ 2**63
                parts.append(self.tmp(f'{a} {_CMP[type(op)]} {b}'))
            return parts[0] if len(parts) == 1 else self.tmp(' and '.join(parts))
        name = n.func.id                                    # ast.Call (s64 only in Compare)
        a, b = (self.val(v) for v in n.args)
        if name == 'mulhu':
            return self.tmp(f'({a} * {b}) >> 64')
        return self.tmp(f'_{name}({a}, {b})')


@functools.lru_cache(maxsize=None)
def _fast(expr):
    tree = _parse(expr)[0]
    g = _Gen()
    res = g.val(tree.body)
    used = variables(expr)
    body = [f'    {v} &= M' for v in VARS if v in used]
    body += ['    ' + line for line in g.lines] + [f'    return {res}']
    nl = chr(10)
    src = 'def _f(x=0, y=0, z=0, w=0):' + nl + nl.join(body) + nl
    ns = dict(_FAST)
    exec(builtins.compile(src, '<truth>', 'exec'), ns)
    f = ns['_f']
    f.expr = expr
    f.source = src
    return f


def compile(expr):
    """Reusable callable f(x=0, y=0, z=0, w=0) -> int | bool for expr (cached per
    string); the same results as ev(expr, (x, y, z, w)), several times faster."""
    parse(expr)
    return _fast(expr)


# ---------------------------------------------------------------- z3
def to_z3(expr, xs=None):
    """z3 term for expr: a 64-bit BitVec for a value, a Bool for a condition.
    xs: four 64-bit bit-vectors for x, y, z, w (default BitVec('x', 64) ...)."""
    import z3
    parse(expr)
    if xs is None:
        xs = [z3.BitVec(v, 64) for v in VARS]
    env = dict(zip(VARS, xs))
    binop = {ast.Add: lambda a, b: a + b, ast.Sub: lambda a, b: a - b,
             ast.Mult: lambda a, b: a * b, ast.BitAnd: lambda a, b: a & b,
             ast.BitOr: lambda a, b: a | b, ast.BitXor: lambda a, b: a ^ b,
             ast.LShift: lambda a, b: a << b, ast.RShift: z3.LShR}
    ucmp = {ast.Eq: lambda a, b: a == b, ast.NotEq: lambda a, b: a != b, ast.Lt: z3.ULT,
            ast.LtE: z3.ULE, ast.Gt: z3.UGT, ast.GtE: z3.UGE}
    scmp = {ast.Eq: lambda a, b: a == b, ast.NotEq: lambda a, b: a != b,
            ast.Lt: lambda a, b: a < b, ast.LtE: lambda a, b: a <= b,
            ast.Gt: lambda a, b: a > b, ast.GtE: lambda a, b: a >= b}
    calls = {'sar': lambda a, b: a >> b, 'rol': z3.RotateLeft, 'ror': z3.RotateRight,
             'udiv': z3.UDiv, 'urem': z3.URem,
             'mulhu': lambda a, b: z3.Extract(127, 64, z3.ZeroExt(64, a) * z3.ZeroExt(64, b))}

    def g(n):
        t = type(n)
        if t is ast.Name:
            return env[n.id]
        if t is ast.Constant:
            if n.value is True or n.value is False:
                return z3.BoolVal(n.value)
            return z3.BitVecVal(n.value, 64)
        if t is ast.BinOp:
            return binop[type(n.op)](g(n.left), g(n.right))
        if t is ast.UnaryOp:
            a = g(n.operand)
            op = type(n.op)
            return -a if op is ast.USub else (~a if op is ast.Invert else z3.Not(a))
        if t is ast.BoolOp:
            vals = [g(v) for v in n.values]
            return z3.And(*vals) if type(n.op) is ast.And else z3.Or(*vals)
        if t is ast.Compare:
            ops = [n.left] + n.comparators
            parts = []
            for i, op in enumerate(n.ops):
                l, r = ops[i], ops[i + 1]
                table = scmp if (_is_s64(l) or _is_s64(r)) else ucmp
                a = g(l.args[0]) if _is_s64(l) else g(l)
                b = g(r.args[0]) if _is_s64(r) else g(r)
                parts.append(table[type(op)](a, b))
            return parts[0] if len(parts) == 1 else z3.And(*parts)
        a, b = (g(v) for v in n.args)
        return calls[n.func.id](a, b)

    return g(_parse(expr)[0].body)
