"""Tests of truth.py: python -I gen/test_truth.py [--n 2000] (exit code 1 on failure).

Explicit asserts on the semantics, then a differential test on random expressions:
ev (U64 wrapper class) against compile (generated code) against z3 (SMT-LIB semantics).
"""
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import truth                                    # noqa: E402
from truth import ev, parse, parse_ok, nodes, variables, MASK, SIGN   # noqa: E402

C = truth.compile


def both(expr, args=()):
    """ev and compile agree; return the value."""
    a = ev(expr, args)
    b = C(expr)(*args)
    assert a == b and type(a) is type(b), (expr, args, a, b)
    return a


# wraparound
assert both('x + y', [MASK, 1]) == 0
assert both('x - y', [0, 1]) == MASK
assert both('x * y', [SIGN, 2]) == 0
assert both('x * x', [1 << 32]) == 0
assert both('0 - 1') == MASK
assert both('0xffffffffffffffff + 0xffffffffffffffff') == MASK - 1
assert both('(1 << 63) + (1 << 63)') == 0
# ~ and unary -
assert both('~x', [0]) == MASK
assert both('~x', [MASK]) == 0
assert both('~0') == MASK
assert both('~x + 1', [5]) == both('-x', [5]) == MASK - 4
assert both('-x', [1]) == MASK
assert both('-x', [0]) == 0
assert both('-x', [SIGN]) == SIGN
assert both('--x', [7]) == 7
assert both('-1') == MASK
assert both('~-x', [3]) == 2
# >> is logical, sar is arithmetic; shift counts >= 64
assert both('x >> 1', [SIGN]) == 1 << 62
assert both('sar(x, 1)', [SIGN]) == 0xC000000000000000
assert both('sar(x, 63)', [SIGN]) == MASK
assert both('sar(x, 64)', [SIGN]) == MASK
assert both('sar(x, y)', [5, MASK]) == 0
assert both('sar(x, 0)', [SIGN | 5]) == SIGN | 5
assert both('x >> 63', [MASK]) == 1
assert both('x >> 64', [MASK]) == 0
assert both('x >> y', [MASK, MASK]) == 0
assert both('x << 63', [3]) == SIGN
assert both('x << 64', [1]) == 0
assert both('x << y', [1, MASK]) == 0
assert both('(1 << 70) >> 64') == 0
# rol / ror
V = 0x0123456789ABCDEF
assert both('rol(x, 0)', [V]) == V and both('ror(x, 0)', [V]) == V
assert both('rol(x, 64)', [V]) == V and both('ror(x, 64)', [V]) == V
assert both('rol(x, 1)', [SIGN]) == 1
assert both('ror(x, 1)', [1]) == SIGN
assert both('rol(x, 65)', [1]) == 2
assert both('ror(x, y)', [1, 68]) == 1 << 60
assert both('rol(x, 8)', [V]) == 0x23456789ABCDEF01
assert all(both('rol(x, y)', [V, k]) == both('ror(x, 64 - y)', [V, k]) for k in range(1, 64))
assert all(both('rol(x, y)', [V, k]) == both('ror(x, -y)', [V, k]) for k in range(0, 130))
# udiv / urem / mulhu
assert both('udiv(x, y)', [7, 2]) == 3 and both('urem(x, y)', [7, 2]) == 1
assert both('udiv(x, 0)', [7]) == MASK
assert both('urem(x, 0)', [7]) == 7
assert both('udiv(x, y)', [MASK, 2]) == (1 << 63) - 1
assert both('urem(x, 10)', [MASK]) == MASK % 10
assert both('mulhu(x, y)', [MASK, MASK]) == MASK - 1
assert both('mulhu(x, y)', [1 << 32, 1 << 32]) == 1
assert both('mulhu(x, 2)', [SIGN]) == 1
# comparisons: unsigned unless an operand is s64(...)
assert both('s64(x) < 0', [MASK]) is True
assert both('x < 0', [MASK]) is False
assert both('s64(x) < s64(y)', [MASK, 0]) is True
assert both('x < y', [MASK, 0]) is False
assert both('s64(x) > 0x7fffffffffffffff', [SIGN]) is False
assert both('s64(x) == -1', [MASK]) is True
assert both('s64(x) <= y', [SIGN, 0]) is True
assert both('-1 < s64(x)', [0]) is True
assert both('s64(x) >= s64(y)', [0, SIGN]) is True
assert both('s64(x) != s64(y)', [5, 5]) is False
assert both('0 < x < 10', [5]) is True and both('0 < x < 10', [10]) is False
assert both('s64(x) < 0 < y', [MASK, 1]) is True
assert both('s64(x) < 0 < y', [MASK, 0]) is False
assert both('x <= y >= z', [1, 2, 2]) is True
# precedence (Python's)
assert both('x & y == 0', [1, 2]) is True
assert both('x + y << 2', [1, 1]) == 8
assert both('x ^ y & z', [1, 3, 2]) == 3
assert both('x | y ^ z', [1, 2, 2]) == 1
assert both('-x * y', [1, 2]) == MASK - 1
assert both('~x & y', [1, 3]) == 2
assert both('not x == y', [1, 1]) is False
assert both('x == 1 or x == 2 and y == 0', [1, 5]) is True
assert both('(x == 1 or x == 2) and y == 0', [1, 5]) is False
assert both('x - y - z', [10, 3, 2]) == 5
assert both('x << y << z', [1, 2, 3]) == 32
assert both('x * y + z * w', [2, 3, 4, 5]) == 26
# literals
assert both('0x10') == 16 and both('0XFF') == 255
assert both('18446744073709551615') == MASK and parse_ok('0xffffffffffffffff')
for bad in ('0b101', '0o7', '1_000', '00', '0x10000000000000000', '18446744073709551616', '1.5', '1j'):
    assert not parse_ok(bad), bad
# syntax outside the language
for bad in ('x ** 2', 'x / y', 'x // y', 'x % y', 'a + 1', 'x.real', 'abs(x)', '__import__("os")',
            '(lambda: 1)()', 'x if y else z', '[x]', 'x[0]', '"s"', 'x in y', 'x is y', '+x',
            's64(x)', 's64(x) + 1 < 2', 's64(s64(x)) < 0', '(x < y) + 1', 'x and y', 'not x',
            'sar(x)', 'sar(x, k=1)', 'rol(*x)', '', '   ', 'x; y', 'x = 1', '(x < y) < z',
            'x @ y', 'None', 'x < y + (y == z)', 'True + 1', 'f(x)', 'x.__class__', 'X'):
    assert not parse_ok(bad), bad
assert not parse_ok(5) and not parse_ok(None)
try:
    parse('s64(x) + 1')
    raise SystemExit('parse accepted s64 outside a comparison')
except truth.ExprError as e:
    assert 's64' in str(e)
# kinds, whitespace, True / False
assert parse('x + y') == 'val' and parse('x < y') == 'bool' and parse('True') == 'bool'
assert not parse_ok('x < y', 'val') and not parse_ok('x + y', 'bool')
assert parse_ok('True', 'bool') and parse_ok('not True or False', 'bool')
assert parse_ok('  (x + y)  ') and both('  (x + y)  ', [1, 2]) == 3
assert both('True') is True and both('not True') is False
# nodes / variables
assert nodes('(x + y)') == 3 and nodes('x') == 1 and nodes('7') == 1
assert nodes('s64(x) < 0') == 4
assert nodes('0 < x < 10') == 5
assert nodes('x < y and y < z and z < w') == 11
assert nodes('rol(x, 13)') == 3 and nodes('~-x') == 3
assert variables('x + w') == {'x', 'w'} and variables('rol(y, 3) < 5') == {'y'}
assert variables('True') == set()
# arguments: zero padding, 64-bit masking of inputs
assert both('w', [1]) == 0 and both('x + y + z + w', [1, 2, 3, 4]) == 10
assert both('x', [-1]) == MASK and both('x', [(1 << 64) + 5]) == 5
assert type(ev('x < y', [1, 2])) is bool and type(C('x < y')(1, 2)) is bool
assert C('(x + y)') is C('(x + y)')
# deep expressions (straight-line code: no nesting limit in the compiled form)
long_sum = ' + '.join(['x'] * 400)
assert both(long_sum, [3]) == 1200 and nodes(long_sum) == 799
nested = '(' * 150 + 'x' + ' + 1)' * 150
assert both(nested, [MASK]) == 149
assert not parse_ok('(' * 300 + 'x' + ')' * 300)

# ------------------------------------------------ differential test: ev / compile / z3
BIN = ['+', '-', '*', '&', '|', '^', '<<', '>>']
CMP = ['==', '!=', '<', '<=', '>', '>=']
HELP = ['sar', 'rol', 'ror', 'udiv', 'urem', 'mulhu']
LITS = [0, 1, 2, 3, 7, 31, 63, 64, 65, 127, 128, 255, MASK, MASK - 1, SIGN, SIGN - 1, 0xffffffff]


def rand_val(r, d):
    if d <= 0 or r.random() < 0.2:
        if r.random() < 0.65:
            return r.choice('xyzw')
        v = r.choice(LITS) if r.random() < 0.7 else r.getrandbits(r.choice([6, 16, 64]))
        return hex(v) if r.random() < 0.5 else str(v)
    c = r.randrange(6)
    if c <= 2:
        return f'({rand_val(r, d - 1)} {r.choice(BIN)} {rand_val(r, d - 1)})'
    if c == 3:
        return f'{r.choice(["-", "~"])}{rand_val(r, d - 1)}'
    if c == 4:
        k = rand_val(r, d - 1) if r.random() < 0.5 else f'({rand_val(r, d - 1)} & 63)'
        return f'{r.choice(HELP)}({rand_val(r, d - 1)}, {k})'
    return f'({rand_val(r, d - 1)} {r.choice(["<<", ">>"])} {r.randrange(70)})'


def rand_bool(r, d):
    c = r.randrange(5)
    if d <= 0 or c <= 1:
        k = r.choice([2, 2, 2, 3])
        ops = [rand_val(r, 2) for _ in range(k)]
        ops = [f's64({o})' if r.random() < 0.4 else o for o in ops]
        return '(' + ops[0] + ''.join(f' {r.choice(CMP)} {o}' for o in ops[1:]) + ')'
    if c == 2:
        return f'({rand_bool(r, d - 1)} and {rand_bool(r, d - 1)})'
    if c == 3:
        return f'({rand_bool(r, d - 1)} or {rand_bool(r, d - 1)})'
    return f'(not {rand_bool(r, d - 1)})'


def rand_input(r):
    pick = lambda: r.choice(LITS) if r.random() < 0.4 else r.getrandbits(r.choice([3, 8, 32, 64]))
    return [pick() for _ in range(4)]


def main():
    n = 2000
    if '--n' in sys.argv:
        n = int(sys.argv[sys.argv.index('--n') + 1])
    r = random.Random(12345)
    checks = 0
    exprs = []
    for i in range(n):
        e = rand_val(r, r.randrange(1, 6)) if i % 2 == 0 else rand_bool(r, r.randrange(1, 4))
        assert parse_ok(e), e
        exprs.append(e)
        f = C(e)
        for _ in range(10):
            a = rand_input(r)
            assert ev(e, a) == f(*a), (e, a, ev(e, a), f(*a))
            checks += 1
    import z3
    xs = [z3.BitVec(v, 64) for v in truth.VARS]
    for e in exprs[:max(1, n // 5)]:
        term = truth.to_z3(e, xs)
        for _ in range(3):
            a = rand_input(r)
            got = z3.simplify(z3.substitute(term, *[(v, z3.BitVecVal(k, 64)) for v, k in zip(xs, a)]))
            want = ev(e, a)
            got = z3.is_true(got) if type(want) is bool else got.as_long()
            assert got == want, (e, a, got, want)
            checks += 1
    e = '((x ^ y) + 2 * (x & y)) - ((x | y) + (x & y)) + rol(x, 13) * mulhu(y, z)'
    a = [r.getrandbits(64) for _ in range(4)]
    f = C(e)
    t0 = time.perf_counter()
    for _ in range(20000):
        ev(e, a)
    t1 = time.perf_counter()
    for _ in range(20000):
        f(*a)
    t2 = time.perf_counter()
    src = open(os.path.abspath(__file__), encoding='utf-8').read()
    nassert = sum(1 for line in src.splitlines() if line.lstrip().startswith('assert '))
    print(f'test_truth: OK  assert statements={nassert}  random expressions={n}  '
          f'random checks={checks} (ev vs compile, {n // 5 * 3} vs z3)')
    print(f'speed on a {truth.nodes(e)}-node expression: ev {(t1 - t0) * 50:.2f} us, '
          f'compile {(t2 - t1) * 50:.2f} us per evaluation')


if __name__ == '__main__':
    main()
