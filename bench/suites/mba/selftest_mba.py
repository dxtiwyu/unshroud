"""selftest_mba.py: every rewrite of gen_mba.py checked on random 64-bit inputs.

usage: python -I suites/mba/selftest_mba.py   (prints the number of checks, exit 1 on a failure)
"""
import os
import random
import sys

os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np                              # noqa: E402

sys.dont_write_bytecode = True                  # no __pycache__ in the suite directory
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_mba as g                             # noqa: E402

S = 64
R = random.Random(5)
ENV = {v: np.array([R.getrandbits(64) if i % 3 else R.choice(g.EDGE) for i in range(S)], dtype=np.uint64)
       for v in g.VARS}
ENV['_n'] = S
FAILS = []
COUNT = [0]


def same(a, b, what):
    COUNT[0] += 1
    if not np.array_equal(g.ev(a, ENV), g.ev(b, ENV)):
        FAILS.append(what + ': ' + g.show(b)[:120])


def operands(r):
    xs = [g.V('x'), g.V('y'), g.B('&', g.V('x'), g.V('z')), g.B('+', g.V('y'), g.C(0x1234)),
          g.B('*', g.V('z'), g.V('w')), g.U('~', g.V('w')), g.B('^', g.B('-', g.V('x'), g.V('y')), g.V('z'))]
    return g.cp(r.choice(xs)), g.cp(r.choice(xs))


def main():
    g.memory_guard(1024, 1024)
    r = random.Random(11)
    fv = list(g.VARS)
    for op, rules in g.RW.items():
        for name, (fl, f) in rules.items():
            for _ in range(20):
                a, b = operands(r)
                if op == '*' and name == 'M1':
                    pass
                orig = g.U(op, g.cp(a)) if op in ('~', 'neg') else g.B(op, g.cp(a), g.cp(b))
                new = f(a, b if op not in ('~', 'neg') else None)
                same(orig, new, f'{op} {name}')
    for _ in range(40):
        a, b = operands(r)
        same(g.B('*', g.cp(a), g.cp(b)), g.r_mul2(g.cp(a), g.cp(b), r), 'mul2')
        same(g.U('~', g.cp(a)), g.r_not_split(g.cp(a), r.choice(fv), r), 'not_split')
        s = g.B(r.choice('+-'), g.cp(a), g.cp(b))
        same(g.B('*', g.cp(s), g.cp(b)), g.r_dist(g.cp(s), g.cp(b), r), 'dist')
        k = g.C(g.rand_const(r))
        same(g.B('*', g.cp(k), g.cp(a)), g.r_ksplit(g.cp(k), g.cp(a), r), 'ksplit')
        same(g.cp(a), g.r_affine(g.cp(a), r), 'affine')
        same(g.cp(a), g.r_mask(g.cp(a), r), 'mask')
        same(g.cp(a), g.r_split(g.cp(a), r, fv), 'split')
        same(g.cp(a), g.r_nest(g.cp(a), r, fv), 'nest')
        z = g.poly_zero(fv, r)
        same(g.C(0), z, 'poly_zero')
    for t in (1, 2, 3, 4):
        for _ in range(30):
            atoms = [g.V(v) for v in r.sample(fv, t)]
            if r.random() < 0.5:
                atoms = [g.small_term(fv, r, True) if r.random() < 0.5 else x for x in atoms]
            z = g.build_sum(g.zero_terms(t, r), atoms, r)
            same(g.C(0), z, f'zero t={t}')
    for s in g.LIN_T + ['(x ^ (y + z))', '((x * y) & (~z))', '(((x - 3) | y) ^ (z * w))']:
        for mode in ('lin', 'np'):
            for _ in range(6):
                e = g.from_str(s)
                n = g.cp(e)
                new = g.apply_sy(n, mode, r, fv)
                if new is not None:
                    same(e, new, f'synth {mode} {s}')
                new = g.apply_zero(g.cp(e), mode, r, fv)
                same(e, new, f'zero-insert {mode} {s}')
    for K in g.CONSTS:
        for _ in range(4):
            same(g.C(K), g.const_seed(K, fv[:r.randint(1, 4)], r), f'const {K:#x}')
    print(f'{COUNT[0]} checks, {len(FAILS)} failures')
    for f in FAILS[:20]:
        print('FAIL', f)
    return 1 if FAILS else 0


if __name__ == '__main__':
    sys.exit(main())
