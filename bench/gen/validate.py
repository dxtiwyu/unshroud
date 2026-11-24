"""validate.py: check a bench suite against its DLL by native execution.

usage: python -I gen/validate.py suites/<s>/<s>.json [--n 2000] [--seed 1]
                                 [--prove] [--only NAME,NAME] [--report FILE] [-v]

THE REFERENCE FOR SUITE AUTHORS: the expression language, the json format, what is checked.

== Ground-truth format (shared by every suite) ==
suites/<suite>/<suite>.json:
{"suite": "<suite>", "dll": "<suite>.dll" (relative to the json), "image_base": "0x180000000",
 "functions": [ {"name": "mba_0007", "rva": "0x1230", "size": 812, "insns": 190, "nargs": 2,
   "category": "linear", "difficulty": 3,
   "truth": "(x + y)"   (the output when the function has a single path, else null),
   "paths": [ {"cond": "True", "out": "(x + y)", "witness": [[1, 2, 0, 0]]} ],
   "opaque": [ {"kind": "x*(x+1) even", "always": true, "dead_out": "0xdead0003"} ],
   ...suite-specific fields... } ] }
Every feasible path has a cond, an out and at least one witness input that reaches
it. For every input exactly one path cond holds. Opaque (infeasible) arms are not
paths: they are listed in "opaque".
Field rules (common.write_suite_json writes this format and fills rva / size / insns):
  name        the exported name; functions are sorted by name, names are unique
  rva         hex string: the entry point (= the export's rva); one function per rva
  size        bytes from rva to the end of the last instruction (alignment padding
              excluded: int3 / nop after it); the code reachable from the entry stays inside
  insns       number of instructions in [rva, rva + size)
  nargs       0..4; arguments beyond nargs are not passed and expressions do not use them
  category    string (suite-defined), difficulty int (suite-defined scale)
  truth       non-null exactly when there is a single path (its cond is then "True"),
              and then equal to that path's out
  paths       [{cond, out, witness}]: cond a condition, out a value; witness a non-empty
              list of inputs, each [x, y, z, w] (4 ints, zeros beyond nargs) satisfying cond
  opaque      [{kind, always, dead_out}]: an opaque predicate in the code; kind says what
              it is, always is its constant truth value, dead_out the value its dead arm
              would return (null when the dead arm returns nothing simple); [] if none

== Expression language (cond / out / truth / dead_out) ==
Python syntax over x, y, z, w (arguments 1..4 = rcx, rdx, r8, r9, unsigned 64-bit);
operators + - * & | ^ ~ << >> and unary - (every result taken mod 2**64, >> is logical,
~ is the 64-bit NOT); integer literals (decimal or 0x); helper functions s64(e) (signed
view, only inside comparisons), sar(a, k), rol(a, k), ror(a, k), udiv(a, b), urem(a, b),
mulhu(a, b); comparisons == != < <= > >= (unsigned unless wrapped in s64); and, or,
not, True. gen/truth.py implements ev(expr, args), compile(expr), parse_ok(expr), nodes(expr).
Exact rules:
  * literals: decimal without leading zeros, or 0x / 0X hex; 0 <= literal < 2**64;
    no 0b / 0o / underscores. A negative constant is unary minus: -1 = 2**64-1.
  * a << k and a >> k with k >= 64 give 0 (no masking of k: write x << (y & 63) for the
    x86 shl behaviour); sar(a, k) is the arithmetic shift, k >= 64 gives 0 or 2**64-1;
    rol(a, k) / ror(a, k) rotate by k mod 64 (rol(a, 0) = rol(a, 64) = a).
  * udiv / urem are unsigned; udiv(a, 0) = 2**64-1 and urem(a, 0) = a (suites must not
    divide by zero: this only keeps the evaluator total); mulhu(a, b) = (a * b) >> 64,
    the high half of the unsigned 128-bit product. All of these agree with SMT-LIB
    (bvshl, bvlshr, bvashr, ext_rotate_left/right, bvudiv, bvurem): truth.to_z3.
  * a comparison is signed when either of its two operands is s64(...): both 64-bit
    values are then read as two's complement (s64(x) < 0 means x is negative,
    s64(x) <= 5 compares x with 5 signed). s64(e) appears only as a direct operand of
    a comparison. A chain a < b < c means (a < b) and (b < c), pair by pair.
  * precedence is Python's: x & y == 0 is (x & y) == 0; x + y << 2 is (x + y) << 2;
    x ^ y & z is x ^ (y & z); x | y ^ z is x | (y ^ z); not a == b is not (a == b);
    and binds tighter than or. Parenthesize generously.
  * values and conditions do not mix: no arithmetic on comparisons, no value as a
    condition (write x != 0, not x). cond is a condition (True / False / comparisons
    / and / or / not); out, truth and dead_out are values. No other names, calls,
    operators (/, //, %, **), conditional expressions or attributes.

== What is checked ==
Per function: the format above (expressions parse, variables within nargs, witnesses
well formed, truth consistent, rva = export rva). Inputs: every witness of every path;
the edge values 0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x7fffffff, 0x80000000, 0xffffffff,
2**63-1, 2**63, 2**64-2, 2**64-1 in combinations (all of them up to 3 arguments; with
4 arguments every pair of positions plus a random sample); small values (-8..32);
related arguments (one argument equal to another, +-1, ~, -, sign flip, shifted);
edge values +- small offsets; random 64-bit values (uniform and of random bit length)
until there are at least --n inputs. The DLL is loaded with ctypes.WinDLL and the
code at image + rva is called (restype c_uint64, argtypes c_uint64 * nargs). For every
input exactly one path cond must hold ("no path" / "several paths") and the native
result must equal that path's out (and truth when not null); every witness must
satisfy its own path's cond. A native exception (access violation, divide error) fails
the function. --prove also asks z3 whether the conds partition the input space (a gap
or an overlap fails the function; a z3 timeout is only reported).
Output: one line per failing function (its first counterexample), then
  VALID suite=<s> functions=<n> passed=<p> failed=<f> inputs=<total>
Exit code 1 when anything failed. Inputs are deterministic for a given --seed.
"""
import argparse
import ctypes
import itertools
import json
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                   # noqa: E402
import truth                                    # noqa: E402

MASK = truth.MASK
SIGN = truth.SIGN
EDGE = [0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x7fffffff, 0x80000000, 0xffffffff,
        2**63 - 1, 2**63, 2**64 - 2, 2**64 - 1]
RELATED = [lambda v: v, lambda v: (v + 1) & MASK, lambda v: (v - 1) & MASK, lambda v: v ^ MASK,
           lambda v: -v & MASK, lambda v: v ^ SIGN, lambda v: (v << 1) & MASK, lambda v: v >> 1]


def make_inputs(func, n, seed):
    """Deterministic list of 4-tuples for func (see the module doc), witnesses first."""
    nargs = func['nargs']
    r = random.Random(f'{seed}:{func["name"]}')
    seen = {}
    pad = (0,) * (4 - nargs)

    def add(a):
        seen.setdefault(tuple(a[:nargs]) + pad, None)

    for p in func['paths']:
        for w in p['witness']:
            seen.setdefault(tuple(w) + (0,) * (4 - len(w)), None)
    if nargs == 0:
        add(())
        return list(seen)
    if nargs <= 3:
        for a in itertools.product(EDGE, repeat=nargs):
            add(a)
    else:
        for i, j in itertools.combinations(range(nargs), 2):
            for u in EDGE:
                for v in EDGE:
                    a = [0] * nargs
                    a[i], a[j] = u, v
                    add(a)
        for _ in range(n // 2):
            add([r.choice(EDGE) for _ in range(nargs)])
    k = max(64, n // 10)
    for _ in range(k):
        add([r.randrange(-8, 33) & MASK for _ in range(nargs)])
    for _ in range(k):
        a = [r.getrandbits(64) if r.random() < 0.5 else r.getrandbits(r.randint(1, 64)) for _ in range(nargs)]
        i, j = r.sample(range(nargs), 2) if nargs > 1 else (0, 0)
        a[j] = r.choice(RELATED)(a[i])
        add(a)
    for _ in range(k):
        add([(r.choice(EDGE) + r.randrange(-4, 5)) & MASK for _ in range(nargs)])
    while len(seen) < n:
        add([r.getrandbits(64) if r.random() < 0.6 else r.getrandbits(r.randint(1, 64)) for _ in range(nargs)])
    return list(seen)


def _show(a, nargs):
    return ', '.join(f'{v}={a[i]:#x}' for i, v in enumerate(truth.VARS[:nargs])) or '()'


def check_function(f, image, exp, n, seed, prove=False):
    """(ok, message, number of inputs) for one function dict of a suite json."""
    errs = common._check_function(f)
    name = f.get('name')
    if not errs:
        if len(f['paths']) == 1 and f.get('truth') is None:
            errs.append('truth must be the out of the single path (it is null)')
        for k in ('size', 'insns'):
            if type(f.get(k)) is not int or f[k] <= 0:
                errs.append(f'{k} must be a positive int')
        try:
            rva = int(f.get('rva'), 16)
        except (TypeError, ValueError):
            errs.append(f'rva {f.get("rva")!r} is not a hex string')
        else:
            if name in exp and exp[name] != rva:
                errs.append(f'rva {rva:#x} but the export is at {exp[name]:#x}')
    if errs:
        return False, '; '.join(errs), 0
    nargs, paths = f['nargs'], f['paths']
    conds = [truth.compile(p['cond']) for p in paths]
    outs = [truth.compile(p['out']) for p in paths]
    tf = truth.compile(f['truth']) if f.get('truth') is not None else None
    for i, p in enumerate(paths):
        for w in p['witness']:
            if not conds[i](*w):
                return False, f'witness {_show(w, nargs)} does not satisfy path {i} cond {p["cond"]!r}', 0
    if prove:
        msg = common.partition_problem([p['cond'] for p in paths], nargs)
        if msg and 'unknown' not in msg:
            return False, f'z3: {msg}', 0
    fn = ctypes.WINFUNCTYPE(ctypes.c_uint64, *([ctypes.c_uint64] * nargs))(image + rva)
    inputs = make_inputs(f, n, seed)
    rng = range(len(conds))
    for a in inputs:
        hits = [i for i in rng if conds[i](*a)]
        if len(hits) != 1:
            what = 'no path cond holds' if not hits else f'several path conds hold: {hits}'
            return False, f'{_show(a, nargs)}: {what}', len(inputs)
        try:
            got = fn(*a[:nargs])
        except OSError as e:
            return False, f'{_show(a, nargs)}: native call raised {e}', len(inputs)
        i = hits[0]
        want = outs[i](*a)
        if got != want:
            return False, (f'{_show(a, nargs)}: native {got:#x} != path {i} out {paths[i]["out"]!r} '
                           f'= {want:#x} [cond {paths[i]["cond"]!r}]'), len(inputs)
        if tf is not None and tf(*a) != got:
            return False, f'{_show(a, nargs)}: native {got:#x} != truth {f["truth"]!r} = {tf(*a):#x}', len(inputs)
    return True, '', len(inputs)


def validate(json_path, n=2000, seed=1, prove=False, only=None, verbose=False, out=sys.stdout):
    """Validate one suite; print the failure lines and the VALID line; return a report dict."""
    t0 = time.perf_counter()
    rep = {'json': os.path.abspath(json_path), 'suite': None, 'functions': [], 'errors': []}
    try:
        with open(json_path, encoding='utf-8') as fh:
            data = json.load(fh)
        rep['suite'] = data['suite']
        dll_path = os.path.join(os.path.dirname(os.path.abspath(json_path)), data['dll'])
        if int(data['image_base'], 16) != common.image_base(dll_path):
            rep['errors'].append(f'image_base {data["image_base"]} but the DLL says {common.image_base(dll_path):#x}')
        exp = common.exports(dll_path)
        image = ctypes.WinDLL(os.path.abspath(dll_path))._handle
        funcs = data['functions']
        assert isinstance(funcs, list), 'functions is not a list'
    except Exception as e:                      # noqa: BLE001 - any broken file is a failure
        rep['errors'].append(f'cannot load the suite: {type(e).__name__}: {e}')
        funcs = []
    if not funcs and not rep['errors']:
        rep['errors'].append('no functions')
    names = [f.get('name') if isinstance(f, dict) else None for f in funcs]
    for f in funcs:
        if not isinstance(f, dict):
            ok, msg, k = False, 'not an object', 0
        elif only and f.get('name') not in only:
            continue
        elif names.count(f.get('name')) > 1:
            ok, msg, k = False, 'duplicate name', 0
        else:
            ok, msg, k = check_function(f, image, exp, n, seed, prove)
        name = f.get('name') if isinstance(f, dict) else '?'
        cat = f.get('category') if isinstance(f, dict) else None
        rep['functions'].append({'name': name, 'category': cat, 'ok': ok, 'message': msg, 'inputs': k})
        if not ok:
            print(f'FAIL {name}: {msg}', file=out)
        elif verbose:
            print(f'ok   {name}: {k} inputs', file=out)
    for e in rep['errors']:
        print(f'FAIL {rep["suite"]}: {e}', file=out)
    fl = rep['functions']
    rep['passed'] = sum(1 for r in fl if r['ok'])
    rep['failed'] = len(fl) - rep['passed'] + (1 if rep['errors'] else 0)
    rep['inputs'] = sum(r['inputs'] for r in fl)
    rep['seconds'] = round(time.perf_counter() - t0, 2)
    print(f'VALID suite={rep["suite"]} functions={len(fl)} passed={rep["passed"]} '
          f'failed={rep["failed"]} inputs={rep["inputs"]}', file=out)
    rep['ok'] = rep['failed'] == 0
    return rep


def main(argv=None):
    ap = argparse.ArgumentParser(description='Validate a bench suite json against its DLL.')
    ap.add_argument('json')
    ap.add_argument('--n', type=int, default=2000, help='minimum inputs per function (2000)')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--prove', action='store_true', help='z3: the conds partition the inputs')
    ap.add_argument('--only', help='comma-separated function names')
    ap.add_argument('--report', help='write a json report here')
    ap.add_argument('-v', '--verbose', action='store_true')
    a = ap.parse_args(argv)
    only = set(a.only.split(',')) if a.only else None
    rep = validate(a.json, a.n, a.seed, a.prove, only, a.verbose)
    if a.report:
        with open(a.report, 'w', encoding='utf-8') as fh:
            json.dump(rep, fh, indent=1)
    return 0 if rep['ok'] else 1


if __name__ == '__main__':
    sys.exit(main())
