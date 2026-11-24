"""suite_smoke.py: the smoke suite, built only through common.py (and a test of it).

usage: python -I gen/suite_smoke.py      -> suites/smoke/smoke.{c,dll,map,json}, validated
Five functions: an MBA x + y, a real branch, an opaque predicate x*(x+1) even with a
dead arm returning 0xDEAD0001 that stays a jcc, a 4-argument function, and the helpers
of the expression language (rol, sar, mulhu, udiv) checked against the CPU.
Also cross-checks common.func_sizes against llvm-objdump on this DLL.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                   # noqa: E402

SUITE = 'smoke'
SRC = common.C_PRELUDE + '''
/* MBA: x + y == (x | y) + (x & y); without the barriers clang folds it to one lea */
EXPORT u64 smoke_mba_add(u64 x, u64 y)
{
    u64 a = x | y; BAR(a);
    u64 b = x & y; BAR(b);
    return a + b;
}

/* a real branch on a signed comparison: each arm puts a barrier on its own result */
EXPORT u64 smoke_branch(u64 x, u64 y)
{
    u64 r;
    if ((s64)x < (s64)y) { r = y - x; BAR(r); }
    else                 { r = x ^ y; BAR(r); }
    return r;
}

/* opaque predicate: x * (x + 1) is always even; the dead arm returns 0xDEAD0001 */
EXPORT u64 smoke_opaque(u64 x, u64 y)
{
    u64 t = x * (x + 1); BAR(t);
    u64 r;
    if ((t & 1) == 0) { r = x + y;      BAR(r); }
    else              { r = 0xDEAD0001; BAR(r); }
    return r;
}

/* four arguments (rcx, rdx, r8, r9): two paths on z == w, an MBA in the second one */
EXPORT u64 smoke_args4(u64 x, u64 y, u64 z, u64 w)
{
    u64 r;
    if (z == w) { r = x - y; BAR(r); }
    else {
        u64 a = x ^ z; BAR(a);
        u64 b = y & w; BAR(b);
        u64 o = a | b; BAR(o);
        u64 n = a & b; BAR(n);
        r = o + n;     BAR(r);          /* (x ^ z) + (y & w) */
    }
    return r;
}

/* the language helpers against the CPU: rol by a variable count, sar, mulhu, udiv */
EXPORT u64 smoke_helpers(u64 x, u64 y)
{
    u64 k = y & 63;
    u64 r = (x << k) | (x >> ((64 - k) & 63));               /* rol(x, y & 63) */
    u64 s = (u64)((s64)y >> 7);                               /* sar(y, 7)      */
    u64 h = (u64)(((unsigned __int128)x * y) >> 64);          /* mulhu(x, y)    */
    u64 q = x / (y | 1);                                      /* udiv(x, y | 1) */
    return (r ^ s) + (h ^ q);
}
'''

M = (1 << 64) - 1
# no hidden branch around the 64-bit div of smoke_helpers (see common.py, barrier notes)
NO_DIV_BRANCH = ['-Xclang', '-target-feature', '-Xclang', '-idivq-to-divl']
FUNCTIONS = [
    {'name': 'smoke_mba_add', 'nargs': 2, 'category': 'mba', 'difficulty': 1,
     'paths': [{'cond': 'True', 'out': '(x + y)', 'witness': [[1, 2]]}],
     'code': 'or, and, add kept (no lea folding)'},
    {'name': 'smoke_branch', 'nargs': 2, 'category': 'branch', 'difficulty': 1,
     'paths': [{'cond': 's64(x) < s64(y)', 'out': '(y - x)', 'witness': [[1, 2], [M, 0]]},
               {'cond': 's64(x) >= s64(y)', 'out': '(x ^ y)', 'witness': [[2, 1], [0, M]]}],
     'code': 'one jcc, no cmov'},
    {'name': 'smoke_opaque', 'nargs': 2, 'category': 'opaque', 'difficulty': 1,
     'paths': [{'cond': 'True', 'out': '(x + y)', 'witness': [[1, 2]]}],
     'opaque': [{'kind': 'x*(x+1) even', 'always': True, 'dead_out': '0xdead0001'}],
     'code': 'one jcc, no cmov; 0xdead0001 only after the jcc'},
    {'name': 'smoke_args4', 'nargs': 4, 'category': 'args4', 'difficulty': 1,
     'paths': [{'cond': 'z == w', 'out': '(x - y)', 'witness': [[5, 3, 7, 7]]},
               {'cond': 'z != w', 'out': '((x ^ z) + (y & w))', 'witness': [[5, 3, 7, 8]]}],
     'code': 'one jcc, no cmov; or, and kept'},
    {'name': 'smoke_helpers', 'nargs': 2, 'category': 'helpers', 'difficulty': 1,
     'paths': [{'cond': 'True', 'out': '((rol(x, (y & 63)) ^ sar(y, 7)) + (mulhu(x, y) ^ udiv(x, (y | 1))))',
                'witness': [[0x0123456789abcdef, 0x8000000000000081]]}],
     'code': 'rol, sar, mul, div; no jcc (built without the div bypass)'},
]


def check_code(dll):
    """What the barriers must give, checked on the disassembly: a list of problems."""
    exp = common.exports(dll)
    sizes = common.func_sizes(dll)
    ins = {n: common.disasm(dll, exp[n], sizes[n]) for n in exp}
    ms = {n: {i.mnemonic for i in v} for n, v in ins.items()}
    st = {n: common.insn_stats(dll, exp[n], sizes[n]) for n in exp}
    problems = []
    if not {'or', 'and', 'add'} <= ms['smoke_mba_add']:
        problems.append('smoke_mba_add: the MBA was folded')
    for n in ('smoke_branch', 'smoke_opaque', 'smoke_args4'):
        if st[n]['jcc'] < 1 or st[n]['cmov']:
            problems.append(f'{n}: jcc={st[n]["jcc"]} cmov={st[n]["cmov"]} (a real jcc is required)')
    code = ins['smoke_opaque']
    jcc_at = next((k for k, i in enumerate(code) if i.mnemonic.startswith('j') and i.mnemonic != 'jmp'), None)
    dead_at = next((k for k, i in enumerate(code) if '0xdead0001' in i.op_str), None)
    if jcc_at is None or dead_at is None or dead_at < jcc_at or 'imul' not in ms['smoke_opaque']:
        problems.append('smoke_opaque: predicate, jcc or dead arm not as written')
    if not {'or', 'and'} <= ms['smoke_args4']:
        problems.append('smoke_args4: the MBA was folded')
    h = ms['smoke_helpers']
    if not (h & {'rol', 'ror'} and {'sar', 'mul', 'div'} <= h) or st['smoke_helpers']['jcc']:
        problems.append(f'smoke_helpers: expected rol/ror, sar, mul, div and no jcc; got {sorted(h)}')
    return problems


def main():
    d = common.suite_dir(SUITE)
    src = os.path.join(d, f'{SUITE}.c')
    with open(src, 'w', encoding='utf-8', newline=common.NL) as fh:
        fh.write(SRC)
    dll = os.path.join(d, f'{SUITE}.dll')
    common.build_dll([src], dll, cflags=NO_DIV_BRANCH)
    problems = check_code(dll)
    sizes_vs_objdump = common.crosscheck_sizes(dll)
    for p in problems + sizes_vs_objdump:
        print('PROBLEM', p)
    if problems or sizes_vs_objdump:
        return 1
    jpath = os.path.join(d, f'{SUITE}.json')
    funcs = common.write_suite_json(jpath, SUITE, f'{SUITE}.dll', FUNCTIONS)
    raw = common.func_sizes(dll, trim=False)
    for g in funcs:
        st = common.insn_stats(dll, int(g['rva'], 16), g['size'])
        print(f'{g["name"]:<14} rva {g["rva"]} size {g["size"]:>3} (to next symbol {raw[g["name"]]:>3}) '
              f'insns {g["insns"]:>2} jcc {st["jcc"]} cmov {st["cmov"]} paths {len(g["paths"])}')
        if '--show' in sys.argv:
            print(common.listing(dll, int(g['rva'], 16), g['size']))
    print(f'func_sizes agrees with llvm-objdump on all {len(funcs)} exports; code checks passed')
    code, out = common.validate(jpath)
    print(out.strip())
    return code


if __name__ == '__main__':
    sys.exit(main())
