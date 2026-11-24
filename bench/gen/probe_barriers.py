"""probe_barriers.py: re-measure the clang -O2 barrier patterns documented in common.py.

usage: python -I gen/probe_barriers.py [--keep DIR] [--show NAME]
Builds a probe DLL from the variants below (and again with the flags of VARIANTS), checks each documented claim on the disassembly and prints a
table; exit code 1 when a claim no longer holds (e.g. after a clang update).
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                   # noqa: E402

SRC = common.C_PRELUDE + '''#define BARNV(v) __asm__("" : "+r"(v))
#define CLOB() __asm__ volatile("" ::: "memory")
/* (a) obfuscated arithmetic */
EXPORT u64 a_plain(u64 x, u64 y) { return (x | y) + (x & y); }
EXPORT u64 a_bar_both(u64 x, u64 y) { u64 a = x | y; BAR(a); u64 b = x & y; BAR(b); return a + b; }
EXPORT u64 a_bar_one(u64 x, u64 y) { u64 a = x | y; BAR(a); return a + (x & y); }
EXPORT u64 a_bar_inputs(u64 x, u64 y) { BAR(x); BAR(y); return (x | y) + (x & y); }
EXPORT u64 a_bar_result(u64 x, u64 y) { u64 r = (x | y) + (x & y); BAR(r); return r; }
EXPORT u64 a_nonvolatile(u64 x, u64 y) { u64 a = x | y; BARNV(a); u64 b = x & y; BARNV(b); return a + b; }
EXPORT u64 s_plain(u64 x, u64 y) { return (x | y) - (x & y); }
EXPORT u64 s_bar(u64 x, u64 y) { u64 a = x | y; BAR(a); u64 b = x & y; BAR(b); return a - b; }
EXPORT u64 n_plain(u64 x, u64 y) { return (x & ~y) + y; }
EXPORT u64 n_bar(u64 x, u64 y) { u64 n = ~y; BAR(n); u64 a = x & n; BAR(a); return a + y; }
EXPORT u64 o_plain(u64 x, u64 y) { return (~x | y) - ~x; }
EXPORT u64 o_bar(u64 x, u64 y) { u64 n = ~x; BAR(n); u64 a = n | y; BAR(a); return a - n; }
EXPORT u64 x_plain(u64 x, u64 y) { return (x ^ y) + 2 * (x & y); }
/* (b) real conditional jumps */
EXPORT u64 b_plain(u64 x, u64 y) { if ((s64)x < (s64)y) return y - x; return x ^ y; }
EXPORT u64 b_clob_both(u64 x, u64 y) { if ((s64)x < (s64)y) { CLOB(); return y - x; } CLOB(); return x ^ y; }
EXPORT u64 b_bar_arms(u64 x, u64 y) { u64 r; if ((s64)x < (s64)y) { r = y - x; BAR(r); } else { r = x ^ y; BAR(r); } return r; }
EXPORT u64 b_distinct_asm(u64 x, u64 y) { if ((s64)x < (s64)y) { __asm__ volatile("# lt"); return y - x; } __asm__ volatile("# ge"); return x ^ y; }
EXPORT u64 o_bar_pred_only(u64 x, u64 y) { u64 t = x * (x + 1); BAR(t); if ((t & 1) == 0) return x + y; return 0xDEAD0001; }
EXPORT u64 o_clob_both(u64 x, u64 y) { u64 t = x * (x + 1); BAR(t); if ((t & 1) == 0) { CLOB(); return x + y; } CLOB(); return 0xDEAD0001; }
EXPORT u64 o_bar_arms(u64 x, u64 y) { u64 t = x * (x + 1); BAR(t); u64 r; if ((t & 1) == 0) { r = x + y; BAR(r); } else { r = 0xDEAD0001; BAR(r); } return r; }
EXPORT u64 o_clob_one(u64 x, u64 y) { u64 t = x * (x + 1); BAR(t); if ((t & 1) == 0) { CLOB(); return x + y; } return 0xDEAD0001; }
EXPORT u64 o_pred_value(u64 x) { return (x * (x + 1)) & 1; }
/* more shapes */
EXPORT u64 m_chain3(u64 x, u64 y) { u64 r; if (x < y) { r = y - x; BAR(r); } else if (x == y) { r = x * 3; BAR(r); } else { r = x ^ y; BAR(r); } return r; }
EXPORT u64 m_andcond(u64 x, u64 y) { u64 r; if (x < y && (s64)y > 5) { r = y - x; BAR(r); } else { r = x ^ y; BAR(r); } return r; }
EXPORT u64 m_nested(u64 x, u64 y, u64 z) { u64 r; if (x < y) { if (z & 1) { r = x + z; BAR(r); } else { r = y + z; BAR(r); } } else { r = z; BAR(r); } return r; }
EXPORT u64 m_switch(u64 x, u64 y) { u64 r; switch (x & 3) { case 0: r = x + y; BAR(r); break; case 1: r = x - y; BAR(r); break; case 2: r = x ^ y; BAR(r); break; default: r = x * y; BAR(r); } return r; }
EXPORT u64 m_div(u64 x, u64 y) { return x / (y | 1); }
'''

# (claim, function, property, expected)
CLAIMS = [
    ('(x|y)+(x&y) without barrier is folded', 'a_plain', 'folded', True),
    ('BAR on both terms keeps or/and/add', 'a_bar_both', 'kept', True),
    ('BAR on one term keeps or/and/add', 'a_bar_one', 'kept', True),
    ('BAR on the inputs only does not help', 'a_bar_inputs', 'folded', True),
    ('BAR on the result only does not help', 'a_bar_result', 'folded', True),
    ('non-volatile asm barrier also kept it', 'a_nonvolatile', 'kept', True),
    ('(x|y)-(x&y) without barrier becomes xor', 's_plain', 'folded', True),
    ('(x|y)-(x&y) with barriers is kept', 's_bar', 'kept', True),
    ('(x&~y)+y without barrier becomes or', 'n_plain', 'folded_n', True),
    ('(x&~y)+y with barriers is kept', 'n_bar', 'kept_n', True),
    ('(~x|y)-~x without barrier becomes and', 'o_plain', 'folded', True),
    ('(~x|y)-~x with barriers is kept', 'o_bar', 'kept_o', True),
    ('(x^y)+2*(x&y) is not folded by clang 23 anyway', 'x_plain', 'kept_x', True),
    ('plain if/else becomes cmov', 'b_plain', 'cmov', True),
    ('same asm volatile(::: memory) in both arms: cmov', 'b_clob_both', 'cmov', True),
    ('BAR on each arm result keeps a jcc', 'b_bar_arms', 'jcc', True),
    ('distinct asm text per arm keeps a jcc', 'b_distinct_asm', 'jcc', True),
    ('opaque: BAR on the predicate only: cmov', 'o_bar_pred_only', 'cmov', True),
    ('opaque: same clobber in both arms: cmov', 'o_clob_both', 'cmov', True),
    ('opaque: BAR on each arm result keeps a jcc', 'o_bar_arms', 'jcc', True),
    ('opaque: asm in one arm keeps a jcc', 'o_clob_one', 'jcc', True),
    ('opaque: the dead constant only in the dead arm', 'o_bar_arms', 'dead_after_jcc', True),
    ('opaque: asm in one arm loads the constant first', 'o_clob_one', 'dead_after_jcc', False),
    ('x*(x+1)&1 is not folded to 0', 'o_pred_value', 'has_imul', True),
    ('cmov converter flag: plain if/else gets a jcc', 'b_plain@conv', 'jcc', True),
    ('cmov converter flag: opaque pred-only gets a jcc', 'o_bar_pred_only@conv', 'jcc', True),
    ('if / else if / else, BAR per arm: a jcc per test', 'm_chain3', 'jcc2', True),
    ('a && b in one if: setcc and a single jcc', 'm_andcond', 'setcc_one_jcc', True),
    ('nested ifs, BAR per arm: a jcc per test', 'm_nested', 'jcc2', True),
    ('switch: a jump table (indirect jmp)', 'm_switch', 'jump_table', True),
    ('switch with -fno-jump-tables: a jcc chain', 'm_switch@nojt', 'jcc3', True),
    ('64-bit udiv: clang adds a branch to a 32-bit div', 'm_div', 'div_branch', True),
    ('udiv with idivq-to-divl off: no branch', 'm_div@nodivl', 'div_nobranch', True),
]
VARIANTS = {'': [], 'conv': ['-mllvm', '-x86-cmov-converter-force-all=true'],
            'nojt': ['-fno-jump-tables'],
            'nodivl': ['-Xclang', '-target-feature', '-Xclang', '-idivq-to-divl']}


def measure(dll, name):
    rva = common.exports(dll)[name]
    size = common.func_sizes(dll)[name]
    ins = common.disasm(dll, rva, size)
    ms = {i.mnemonic for i in ins}
    st = common.insn_stats(dll, rva, size)
    first_jcc = next((k for k, i in enumerate(ins) if i.mnemonic.startswith('j') and i.mnemonic != 'jmp'), None)
    dead = next((k for k, i in enumerate(ins) if '0xdead0001' in i.op_str), None)
    return {
        'kept': {'or', 'and'} <= ms,
        'folded': 'or' not in ms,
        'folded_n': 'and' not in ms,
        'kept_n': {'not', 'and'} <= ms,
        'kept_o': {'not', 'or', 'sub'} <= ms,
        'kept_x': {'xor', 'and'} <= ms,
        'cmov': st['cmov'] >= 1 and st['jcc'] == 0,
        'jcc': st['jcc'] >= 1 and st['cmov'] == 0,
        'dead_after_jcc': first_jcc is not None and dead is not None and dead > first_jcc,
        'has_imul': 'imul' in ms,
        'jcc2': st['jcc'] >= 2 and st['cmov'] == 0,
        'jcc3': st['jcc'] >= 3 and st['cmov'] == 0,
        'setcc_one_jcc': st['setcc'] >= 1 and st['jcc'] == 1,
        'jump_table': any(i.mnemonic == 'jmp' and not i.op_str.startswith('0x') for i in ins),
        'div_branch': st['jcc'] >= 1 and 'div' in ms,
        'div_nobranch': st['jcc'] == 0 and 'div' in ms,
    }, ' '.join(i.mnemonic for i in ins)


def main():
    args = sys.argv[1:]
    keep = args[args.index('--keep') + 1] if '--keep' in args else None
    show = args[args.index('--show') + 1] if '--show' in args else None
    d = os.path.abspath(keep) if keep else common.scratch_dir('probe_')
    os.makedirs(d, exist_ok=True)
    src = os.path.join(d, 'probe.c')
    with open(src, 'w', encoding='utf-8', newline=common.NL) as fh:
        fh.write(SRC)
    dlls = {}
    for v, flags in VARIANTS.items():
        dlls[v] = os.path.join(d, f'probe_{v or "default"}.dll')
        common.build_dll([src], dlls[v], cflags=flags)
    clang = common._run([common.CLANG, '--version']).splitlines()[0]
    print(f'{clang}; -O2; probe dir {d}')
    bad = 0
    for claim, fname, prop, want in CLAIMS:
        name, _, variant = fname.partition('@')
        got, code = measure(dlls[variant], name)
        ok = got[prop] == want
        bad += not ok
        print(f'{"ok  " if ok else "FAIL"} {claim:<52} {fname:<22} {prop}={got[prop]}')
        if show and (show == fname or not ok):
            print('     ' + code)
    if show:
        name, _, variant = show.partition('@')
        dll = dlls[variant]
        print(common.listing(dll, common.exports(dll)[name], common.func_sizes(dll)[name]))
    if not keep:
        import shutil
        shutil.rmtree(d, ignore_errors=True)
    print(f'{len(CLAIMS) - bad}/{len(CLAIMS)} claims hold')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
