"""run_all.py: validate every suites/*/*.json and print one table.

usage: python -I gen/run_all.py [--n 2000] [--seed 1] [--prove] [--timeout 1800] [suite ...]
Each suite runs validate.py in its own process (a crash or a hang in one DLL cannot take
the others down; --timeout seconds per suite). Columns: suite, functions, passed,
failed, inputs, seconds, categories (count per category, failures in brackets). The
failing lines of validate.py follow the table. Exit code 1 when anything failed.
"""
import argparse
import glob
import json
import os
import subprocess
import sys
import tempfile
from collections import Counter

GEN = os.path.dirname(os.path.abspath(__file__))
SUITES = os.path.join(os.path.dirname(GEN), 'suites')
TMP = os.path.join(os.path.dirname(GEN), '_tmp')


def run_suite(path, n, seed, prove, timeout):
    os.makedirs(TMP, exist_ok=True)
    fd, rep_path = tempfile.mkstemp(suffix='.json', prefix='report_', dir=TMP)
    os.close(fd)
    cmd = [sys.executable, '-I', os.path.join(GEN, 'validate.py'), path, '--n', str(n),
           '--seed', str(seed), '--report', rep_path] + (['--prove'] if prove else [])
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        out = p.stdout + p.stderr
        try:
            with open(rep_path, encoding='utf-8') as fh:
                rep = json.load(fh)
        except (OSError, ValueError):
            rep = None
        if rep is None:
            lines = out.strip().splitlines()
            rep = {'functions': [], 'failed': 1, 'passed': 0, 'inputs': 0, 'seconds': 0,
                   'errors': [f'validate.py exit {p.returncode}: ' + (lines[-1] if lines else 'no output')]}
    except subprocess.TimeoutExpired:
        out = ''
        rep = {'functions': [], 'failed': 1, 'passed': 0, 'inputs': 0, 'seconds': timeout,
               'errors': [f'timeout after {timeout} s']}
    finally:
        os.remove(rep_path)
    fails = [line for line in out.splitlines() if line.startswith('FAIL')]
    fails += [f'FAIL {e}' for e in rep.get('errors', []) if not any(e in f for f in fails)]
    return rep, fails


def main():
    ap = argparse.ArgumentParser(description='Validate every bench suite.')
    ap.add_argument('suites', nargs='*', help='suite names (default: all)')
    ap.add_argument('--n', type=int, default=2000)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--prove', action='store_true')
    ap.add_argument('--timeout', type=int, default=1800)
    a = ap.parse_args()
    paths = sorted(glob.glob(os.path.join(SUITES, '*', '*.json')))
    if a.suites:
        paths = [p for p in paths if os.path.basename(os.path.dirname(p)) in a.suites]
    if not paths:
        print(f'no suite json under {SUITES}')
        return 1
    rows, all_fails, tot = [], [], Counter()
    for path in paths:
        name = os.path.splitext(os.path.basename(path))[0]
        rep, fails = run_suite(path, a.n, a.seed, a.prove, a.timeout)
        cats, bad = Counter(), Counter()
        for f in rep['functions']:
            cats[f['category']] += 1
            bad[f['category']] += not f['ok']
        cat = ' '.join(f'{c}:{k}' + (f'[{bad[c]} failed]' if bad[c] else '') for c, k in sorted(cats.items(), key=str))
        nf = len(rep['functions'])
        rows.append((name, nf, rep['passed'], rep['failed'], rep['inputs'], rep['seconds'], cat))
        all_fails += [f'{name}: {f}' for f in fails]
        tot.update(functions=nf, passed=rep['passed'], failed=rep['failed'], inputs=rep['inputs'])
    head = ('suite', 'functions', 'passed', 'failed', 'inputs', 'seconds', 'categories')
    rows.append(('TOTAL', tot['functions'], tot['passed'], tot['failed'], tot['inputs'],
                 round(sum(r[5] for r in rows), 2), ''))
    w = [max(len(str(r[i])) for r in rows + [head]) for i in range(6)]
    fmt = lambda r: '  '.join(str(v).ljust(w[i]) if i == 0 else str(v).rjust(w[i]) for i, v in enumerate(r[:6])) + '  ' + str(r[6])
    print(fmt(head))
    for r in rows:
        print(fmt(r))
    for f in all_fails:
        print(f)
    return 1 if tot['failed'] else 0


if __name__ == '__main__':
    sys.exit(main())
