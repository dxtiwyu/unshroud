"""Tests of validate.py: mutated copies of the smoke suite must fail with the right
message, the real one must pass. python -I gen/test_validate.py [--perf N]

--perf N also builds N random functions (MBA-style bodies with barriers, half of them
with two paths) through common.build_dll / write_suite_json in a temp dir and times
validate.py on them with --n 2000.
"""
import copy
import io
import json
import os
import random
import shutil
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                   # noqa: E402
import validate                                 # noqa: E402

SMOKE = os.path.join(common.SUITES, 'smoke', 'smoke.json')
M = (1 << 64) - 1


def fn(data, name):
    return next(f for f in data['functions'] if f['name'] == name)


def mutations():
    """(label, mutate(data), expected substring or None when it must pass, prove)"""
    def put(name, **kw):
        def m(d):
            fn(d, name).update(kw)
        return m

    def path(name, i, **kw):
        def m(d):
            fn(d, name)['paths'][i].update(kw)
        return m

    def top(**kw):
        def m(d):
            d.update(kw)
        return m

    def dup(d):
        d['functions'].append(copy.deepcopy(d['functions'][0]))

    return [
        ('unchanged', lambda d: None, None, False),
        ('equivalent out', path('smoke_mba_add', 0, out='((x | y) + (x & y))'), None, False),
        ('wrong out', path('smoke_mba_add', 0, out='(x - y)'), 'smoke_mba_add: x=', False),
        ('gap at x == y', path('smoke_branch', 1, cond='s64(x) > s64(y)'), 'no path cond holds', False),
        ('gap, z3', path('smoke_branch', 1, cond='s64(x) > s64(y)'), 'z3: gap', True),
        ('overlap', path('smoke_branch', 1, cond='s64(x) >= s64(y) or x == 1'), 'several path conds hold', False),
        ('overlap, z3', path('smoke_branch', 1, cond='s64(x) >= s64(y) or x == 1'), 'z3: overlap', True),
        ('unsigned for signed', lambda d: [path('smoke_branch', 0, cond='x < y', witness=[[1, 2, 0, 0]])(d),
                                           path('smoke_branch', 1, cond='x >= y', witness=[[2, 1, 0, 0]])(d)],
         'smoke_branch: x=', False),
        ('bad witness', path('smoke_args4', 0, witness=[[5, 3, 7, 8]]), 'does not satisfy', False),
        ('witness beyond nargs', path('smoke_branch', 0, witness=[[1, 2, 3, 0]]), 'bad witness', False),
        ('truth differs', put('smoke_opaque', truth='(x ^ y)'), 'truth', False),
        ('truth null, one path', put('smoke_mba_add', truth=None), 'truth must be', False),
        ('wrong rva', put('smoke_helpers', rva='0x1000'), 'but the export is at', False),
        ('expr outside the language', path('smoke_mba_add', 0, out='x ** 2'), 'not in the language', False),
        ('variable beyond nargs', path('smoke_branch', 0, out='(y - z)'), "uses ['z'] but nargs=2", False),
        ('ror for rol', path('smoke_helpers', 0, out='((ror(x, (y & 63)) ^ sar(y, 7)) + (mulhu(x, y) ^ udiv(x, (y | 1))))'),
         'smoke_helpers: x=', False),
        ('>> for sar', path('smoke_helpers', 0, out='((rol(x, (y & 63)) ^ (y >> 7)) + (mulhu(x, y) ^ udiv(x, (y | 1))))'),
         'smoke_helpers: x=', False),
        ('4-arg wrong arm', path('smoke_args4', 1, out='((x ^ z) + (y | w))'), 'smoke_args4: x=', False),
        ('duplicate name', dup, 'duplicate name', False),
        ('image base', top(image_base='0x140000000'), 'image_base', False),
        ('missing dll', top(dll='nope.dll'), 'cannot load the suite', False),
    ]


def run_case(tmp, data, label, mutate, expect, prove):
    d = copy.deepcopy(data)
    mutate(d)
    path = os.path.join(tmp, 'case.json')
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(d, fh)
    out = io.StringIO()
    rep = validate.validate(path, n=500, seed=1, prove=prove, out=out)
    text = out.getvalue()
    if expect is None:
        good = rep['ok'] and 'FAIL' not in text
    else:
        good = (not rep['ok']) and expect in text
    print(f'{"ok  " if good else "BAD "} {label:<26} {text.strip().splitlines()[0][:110]}')
    return good


def rand_expr(r, depth, lines, counter):
    """(C temp name or leaf, truth expression); the C side keeps a BAR on every temp."""
    if depth == 0 or r.random() < 0.15:
        v = r.choice(['x', 'y', 'x', 'y', str(r.getrandbits(r.choice([4, 16, 64])))])
        return (v + 'ULL' if v[0].isdigit() else v), v
    c = r.randrange(5)
    a, ta = rand_expr(r, depth - 1, lines, counter)
    if c == 4:
        op = r.choice(['~', '-'])
        code, t = f'{op}{a}', f'{op}{ta}'
    elif c == 3:
        k = r.randrange(64)
        op = r.choice(['<<', '>>'])
        code, t = f'{a} {op} {k}', f'({ta} {op} {k})'
    else:
        b, tb = rand_expr(r, depth - 1, lines, counter)
        op = r.choice(['+', '-', '*', '&', '|', '^'])
        code, t = f'{a} {op} {b}', f'({ta} {op} {tb})'
    counter[0] += 1
    name = f't{counter[0]}'
    lines.append(f'    u64 {name} = {code}; BAR({name});')
    return name, t


def perf(nfuncs):
    r = random.Random(7)
    tmp = common.scratch_dir('perf_')
    try:
        src, funcs = [common.C_PRELUDE], []
        for i in range(nfuncs):
            name = f'perf_{i:04d}'
            lines, counter = [], [0]
            e1, t1 = rand_expr(r, 4, lines, counter)
            if i % 2:
                e2, t2 = rand_expr(r, 4, lines, counter)
                body = (lines + ['    u64 r;', f'    if (x < y) {{ r = {e1}; BAR(r); }} else {{ r = {e2}; BAR(r); }}',
                                 '    return r;'])
                paths = [{'cond': 'x < y', 'out': t1, 'witness': [common.find_witness('x < y', 2)]},
                         {'cond': 'x >= y', 'out': t2, 'witness': [common.find_witness('x >= y', 2)]}]
            else:
                body = lines + [f'    return {e1};']
                paths = [{'cond': 'True', 'out': t1, 'witness': [[1, 2]]}]
            src.append(f'EXPORT u64 {name}(u64 x, u64 y)' + common.NL + '{' + common.NL +
                       common.NL.join(body) + common.NL + '}' + common.NL)
            funcs.append({'name': name, 'nargs': 2, 'category': f'perf{len(paths)}', 'difficulty': 1, 'paths': paths})
        c = os.path.join(tmp, 'perf.c')
        with open(c, 'w', encoding='utf-8') as fh:
            fh.write(common.NL.join(src))
        t0 = time.perf_counter()
        common.build_dll([c], os.path.join(tmp, 'perf.dll'))
        t1 = time.perf_counter()
        out = common.write_suite_json(os.path.join(tmp, 'perf.json'), 'perf', 'perf.dll', funcs)
        t2 = time.perf_counter()
        code, text = common.validate(os.path.join(tmp, 'perf.json'), n=2000)
        t3 = time.perf_counter()
        print(text.strip().splitlines()[-1])
        print(f'perf: {nfuncs} functions ({sum(f["insns"] for f in out)} instructions): build {t1 - t0:.1f} s, '
              f'write_suite_json {t2 - t1:.1f} s, validate.py --n 2000 {t3 - t2:.1f} s (exit {code})')
        return code == 0
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main():
    with open(SMOKE, encoding='utf-8') as fh:
        data = json.load(fh)
    data['dll'] = os.path.join(os.path.dirname(SMOKE), data['dll'])     # absolute: the copies live elsewhere
    tmp = common.scratch_dir('tv_')
    try:
        results = [run_case(tmp, data, *case) for case in mutations()]
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    code, text = common.validate(SMOKE)
    cli_ok = code == 0 and text.strip().splitlines()[-1].startswith('VALID suite=smoke functions=5 passed=5 failed=0')
    results.append(cli_ok)
    print(f'{"ok  " if cli_ok else "BAD "} {"CLI on the real suite":<26} exit {code}: {text.strip().splitlines()[-1]}')
    if '--perf' in sys.argv:
        results.append(perf(int(sys.argv[sys.argv.index('--perf') + 1])))
    bad = results.count(False)
    print(f'test_validate: {len(results) - bad}/{len(results)} cases as expected')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
