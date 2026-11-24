"""gen_vm.py: the vm suite, VMProtect-like virtual machines (variants A and B).

usage: python -I suites/vm/gen_vm.py [--n 2000] [--show NAME,NAME]
Rebuilds everything from SEED: vm_a.inc, vm_b.inc, vm.c, vm.dll (+ vm.map), vm.json, then
runs gen/validate.py on it. 40 functions: vma_000..vma_019 (variant A), vmb_000..vmb_019
(variant B), each a whole interpreter (13 handlers + an invalid-opcode handler, dispatch by
computed goto through a table of handler offsets, one indirect jmp at the end of every
handler) running its own encrypted bytecode stored in .rdata. Modules: vmlib.py (the two
VMs: opcode numbering, encryption, flags, C text), vmprog.py (programs, ground truth,
compiler, assembler, emulator), z3witness.py (a z3 witness query in a process of its own).

Categories: expr (straight line), branch (1-4 virtual conditional branches), loop (one loop,
4-16 iterations, no other branch), mixed (a loop and 1-3 branches). Difficulty 1..5:
expr 1 (<= 15 operations) or 2; branch 2 (1 if), 3 (2 ifs) or 4 (3-4 ifs); loop 3
(<= 8 iterations) or 4; mixed 4 (1 if) or 5.
Checks after the build: no jcc / cmov and 13 indirect jmps per export (capstone, and again
with llvm-objdump -d), sizes against llvm-objdump (common.crosscheck_sizes), the bytecode read
back from llvm-objdump -s -j .rdata (identical, and its opcode bytes not plain opcodes), then
write_suite_json and gen/validate.py. Every program is first cross-checked three ways
(Python emulation of the encrypted bytecode == AST semantics == the path's truth) on its
witnesses and 100 random inputs. Witnesses: random search, then z3 in a fresh process
(z3witness.py: z3's model depends on the asking process's history), bounded by Z3_RLIMIT
(z3's deterministic operation count) and Z3_MB.
The DLL's link timestamp is replaced by a content hash (normalize_timestamp): a rebuild
gives byte-identical vm.c, vm_a.inc, vm_b.inc, vm.dll, vm.map and vm.json.

Suite-specific fields: variant, bytecode_size (bytes), bytecode_rva, vinsns (virtual
instructions executed on the first witness of path 0), handlers (distinct handlers in the
bytecode), branches (JCC instructions in the bytecode, the loop back edge included),
ifs (if statements of the program), loop (trip count, 0 when none), ops (operations in
the program's expressions, loop body counted once), vstack_max (deepest virtual stack,
arguments included), indirect_jmps (in the native code), program (the source AST).
"""
import argparse
from collections import Counter
import json
import os
import random
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), 'gen'))
import common                                   # noqa: E402
import truth                                    # noqa: E402
import vmlib                                    # noqa: E402
import vmprog                                   # noqa: E402
from vmprog import ARGS                         # noqa: E402

SUITE = 'vm'
SEED = 20261116
Z3_MB = 1024                                    # memory cap of the z3 witness search (MB)
Z3_RLIMIT = 100_000_000                         # z3 operation budget per witness query (the
                                                # largest query of SEED's draws uses 10.9 M)
Z3_STATS = Counter()
JUNK = 0.05                                     # dead PUSH_IMM / POP_VREG pairs per instruction
# per variant: (category, nargs, parameters); each variant draws its own programs
PLAN = [
    ('expr', 1, {'ops': 6}), ('expr', 2, {'ops': 14}), ('expr', 3, {'ops': 23}),
    ('expr', 4, {'ops': 31}), ('expr', 2, {'ops': 40}),
    ('branch', 2, {'nb': 1}), ('branch', 3, {'nb': 1}), ('branch', 2, {'nb': 2}),
    ('branch', 4, {'nb': 2}), ('branch', 3, {'nb': 3}), ('branch', 4, {'nb': 3}),
    ('branch', 4, {'nb': 4}),
    ('loop', 1, {'n': 4}), ('loop', 2, {'n': 7}), ('loop', 3, {'n': 12}), ('loop', 4, {'n': 16}),
    ('mixed', 2, {'nb': 1, 'n': 5}), ('mixed', 3, {'nb': 2, 'n': 9}),
    ('mixed', 4, {'nb': 2, 'n': 14}), ('mixed', 3, {'nb': 3, 'n': 6}),
]
PICKS = [0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x7fffffff, 0x80000000, 0xffffffff,
         2**63 - 1, 2**63, 2**64 - 2, 2**64 - 1]


def pick(r):
    c = r.random()
    if c < 0.2:
        return r.choice(PICKS)
    if c < 0.35:
        return r.randrange(64)
    return r.getrandbits(r.choice((8, 16, 32, 63, 64, 64, 64)))


def witnesses(cond, nargs, r, want=2, tries=3000):
    """(inputs, status): up to want inputs [x, y, z, w] satisfying cond; random search
    first, then z3 (z3witness.py, in a process of its own: see there). status 'sat', or
    'unsat' / 'unknown ...' / 'bad model' (no input)."""
    f = truth.compile(cond)
    found = []
    for _ in range(tries):
        a = [pick(r) for _ in range(nargs)] + [0] * (4 - nargs)
        if f(*a) and a not in found:
            found.append(a)
            if len(found) >= want:
                break
    if found:
        return found, 'sat'
    env = {'SYSTEMROOT': os.environ.get('SYSTEMROOT', 'C:/Windows')}     # fixed history
    cmd = [sys.executable, '-I', 'z3witness.py', str(nargs), str(Z3_RLIMIT), str(Z3_MB)]
    try:
        p = subprocess.run(cmd, input=cond, capture_output=True, text=True, env=env, cwd=HERE,
                           timeout=120)
    except subprocess.TimeoutExpired:
        return [], 'unknown (z3 worker timed out)'
    if p.returncode != 0:
        raise RuntimeError(f'z3witness.py failed (exit {p.returncode}): {p.stderr.strip()[-500:]}')
    status, a, used = json.loads(p.stdout)
    Z3_STATS['queries'] += 1
    Z3_STATS[status.split(' ')[0]] += 1
    Z3_STATS['max_rlimit'] = max(Z3_STATS['max_rlimit'], used)
    if a is None:
        return [], status
    return ([a], 'sat') if f(*a) else ([], 'bad model')


def render(stmts):
    """The program as one line of C-like text (expressions in the bench language)."""
    env = {n: (n, 1, 0) for n in ARGS + vmprog.LOCALS + ('i',)}
    out = []
    for s in stmts:
        k = s[0]
        if k == 'set':
            out.append(f'{s[1]} = {vmprog.sym(s[2], env)[0]};')
        elif k == 'ret':
            out.append(f'return {vmprog.sym(s[1], env)[0]};')
        elif k == 'if':
            c = vmprog.sym_cond(s[1], env)
            out.append(f'if {c} {{ {render(s[2])} }} else {{ {render(s[3])} }}')
        elif k == 'loop':
            out.append(f'for (i = {s[1]}; i != 0; i--) {{ {render(s[2])} }}')
    return ' '.join(out)


def count_ifs(stmts):
    n = 0
    for s in stmts:
        if s[0] == 'if':
            n += 1 + count_ifs(s[2]) + count_ifs(s[3])
    return n


def difficulty(cat, ifs, n, ops):
    if cat == 'expr':
        return 1 if ops <= 15 else 2
    if cat == 'branch':
        return 2 if ifs <= 1 else (3 if ifs == 2 else 4)
    if cat == 'loop':
        return 3 if n <= 8 else 4
    return 4 if ifs <= 1 else 5


def draw(g, cat, p):
    if cat == 'expr':
        return g.expr_prog(p['ops'])
    if cat == 'branch':
        return g.branch_prog(p['nb'])
    if cat == 'loop':
        return g.loop_prog(p['n'])
    return g.mixed_prog(p['nb'], p['n'])


def cross_check(V, name, prog, code, paths, nargs, r, extra=100):
    """Emulated bytecode == AST semantics == the one path whose cond holds, on every
    witness and on random inputs; returns (vinsns of path 0's first witness, max depth)."""
    conds = [truth.compile(p['cond']) for p in paths]
    outs = [truth.compile(p['out']) for p in paths]
    inputs = [w for p in paths for w in p['witness']]
    inputs += [[pick(r) for _ in range(nargs)] + [0] * (4 - nargs) for _ in range(extra)]
    maxd = 0
    for a in inputs:
        hits = [i for i, c in enumerate(conds) if c(*a)]
        if len(hits) != 1:
            raise RuntimeError(f'{name}: {len(hits)} path conds hold on {a}')
        want = outs[hits[0]](*a)
        got, steps, d, _ = vmprog.emulate(V, code, a, nargs)
        ast = vmprog.run_ast(prog, a)
        if not got == ast == want:
            raise RuntimeError(f'{name}: on {a} emulated {got:#x}, AST {ast:#x}, truth {want:#x}')
        maxd = max(maxd, d)
    return vmprog.emulate(V, code, paths[0]['witness'][0], nargs)[1], maxd


def build_function(V, idx, spec):
    cat, nargs, p = spec
    name = f'{V.prefix}_{idx:03d}'
    r = random.Random(f'{SEED}:{V.letter}:{idx}')
    for attempt in range(500):
        prog = draw(vmprog.ProgramGen(r, nargs), cat, p)
        ops = vmprog.prog_ops(prog)
        if not 5 <= ops <= 40:
            continue
        try:
            ps = vmprog.paths(prog, nargs)
        except vmprog.TooBig:
            continue
        used = set()
        for c, o in ps:
            used |= truth.variables(c) | truth.variables(o)
        if used != set(ARGS[:nargs]):
            continue
        paths = []
        for c, o in ps:
            ws, status = witnesses(c, nargs, r)
            if status != 'sat':
                break
            paths.append({'cond': c, 'out': o, 'witness': ws})
        if len(paths) != len(ps):
            continue                                    # an arm no input reaches: draw again
        try:
            blocks = vmprog.Compiler(V, r, nargs).compile(prog, junk=JUNK)
        except vmprog.RegPressure:
            continue
        code, info = vmprog.assemble(V, blocks, r)
        vinsns, maxd = cross_check(V, name, prog, code, paths, nargs, r)
        ifs = count_ifs(prog)
        loop = next((s[1] for s in prog if s[0] == 'loop'), 0)
        insns = [h for b in blocks.values() for h, _ in b]
        return {
            'name': name, 'nargs': nargs, 'category': cat,
            'difficulty': difficulty(cat, ifs, loop, ops), 'paths': paths, 'opaque': [],
            'variant': V.letter, 'bytecode_size': len(code), 'vinsns': vinsns,
            'handlers': sorted(set(insns)), 'branches': insns.count('JCC'), 'ifs': ifs,
            'loop': loop, 'ops': ops, 'vstack_max': maxd, 'program': render(prog),
            '_code': code, '_info': info, '_attempts': attempt + 1, '_V': V,
        }
    raise RuntimeError(f'{name}: no acceptable program in 500 draws')


NL = chr(10)
C_HEAD = '''/* vm.c: the vm suite (generated by gen_vm.py; do not edit).
   Every export is a VM entry: it pushes its native arguments onto the virtual stack (an
   array on the native stack) and includes the interpreter of its variant (vm_a.inc or
   vm_b.inc), which runs the function's encrypted bytecode bc_<name> (in .rdata). */
'''


def c_source(funcs):
    out = [C_HEAD + common.C_PRELUDE.rstrip(NL),
           'typedef unsigned char u8;',
           'typedef u64 __attribute__((aligned(1))) u64u;    /* unaligned 8-byte operand */',
           '#define ROL8(v, n) ((u8)(((u8)(v) << (n)) | ((u8)(v) >> (8 - (n)))))',
           '#define ROR8(v, n) ROL8(v, 8 - (n))',
           '#define ROL64(v, n) (((u64)(v) << (n)) | ((u64)(v) >> (64 - (n))))',
           '#define ROR64(v, n) ROL64(v, 64 - (n))',
           f'#define VSTK {vmlib.VSTK}                                    /* virtual stack slots */',
           '']
    out += [V.c_macros() for V in vmlib.VARIANTS.values()]
    for f in funcs:
        V, code, name, nargs = f['_V'], f['_code'], f['name'], f['nargs']
        out.append(f'/* {name}: {f["program"]} */')
        out.append(f'static const u8 bc_{name}[{len(code)}] = {{')
        out += ['    ' + ', '.join(f'0x{b:02x}' for b in code[i:i + 16]) + ','
                for i in range(0, len(code), 16)]
        out += ['};', f'EXPORT u64 {name}({", ".join("u64 " + a for a in ARGS[:nargs])})', '{',
                '    u64 vstk[VSTK];                     /* virtual stack */',
                '    u64 *vsp = vstk;' if V.up else '    u64 *vsp = vstk + VSTK;']
        out += [f'    {V.letter}_PUSH({a});                        /* VM entry */' for a in V.args_pushed(nargs)]
        out += [f'#define VM_CODE bc_{name}', f'#include "vm_{V.letter.lower()}.inc"',
                '#undef VM_CODE', '}', '']
    return NL.join(out)


def check_code(dll, funcs):
    """The native code must not branch except through the dispatch: no jcc, no cmov, and
    one indirect jmp per dispatching handler (12) plus the entry dispatch."""
    exp, sizes = common.exports(dll), common.func_sizes(dll)
    problems = []
    for f in funcs:
        rva, size = exp[f['name']], sizes[f['name']]
        st = common.insn_stats(dll, rva, size)
        ind = sum(1 for i in common.disasm(dll, rva, size)
                  if i.mnemonic == 'jmp' and not i.op_str.startswith('0x'))
        f['indirect_jmps'] = ind
        if st['jcc'] or st['cmov'] or st['data']:
            problems.append(f'{f["name"]}: jcc={st["jcc"]} cmov={st["cmov"]} data={st["data"]}')
        if ind < len(vmlib.HANDLERS):
            problems.append(f'{f["name"]}: {ind} indirect jmps (dispatch merged?)')
    return problems


def bytecode_rvas(dll, funcs):
    import pefile
    pe = pefile.PE(dll, fast_load=True)
    rdata = next(s for s in pe.sections if s.Name.rstrip(bytes(1)) == b'.rdata')
    data = rdata.get_data()
    problems = []
    for f in funcs:
        k = data.find(f['_code'])
        if k < 0 or data.find(f['_code'], k + 1) >= 0:
            problems.append(f'{f["name"]}: bytecode not found once in .rdata')
        f['bytecode_rva'] = hex(rdata.VirtualAddress + k)
    pe.close()
    return problems


def objdump_check(dll, funcs):
    """The spec's two checks, made on llvm-objdump's output. (1) llvm-objdump -d: every
    export has no jcc and no cmov, and an indirect jmp for the entry dispatch and for each
    dispatching handler (at least 13, the capstone count of check_code must agree). (2)
    llvm-objdump -s -j .rdata: the bytes at bytecode_rva are the encrypted bytecode, and
    its opcode bytes are not plain opcodes: few equal the plain opcode, and few would reach
    the right handler if read without decryption. Returns (problems, stats)."""
    text = common._run([common.OBJDUMP, '-d', '--x86-asm-syntax=intel', '--no-show-raw-insn', dll])
    per, cur = {}, None
    for line in text.splitlines():
        tok = line.split()
        if len(tok) == 2 and tok[1].startswith('<') and tok[1].endswith('>:'):
            cur = per.setdefault(tok[1][1:-2], Counter())
            continue
        parts = line.split(chr(9))
        if cur is None or len(parts) < 2 or not parts[0].strip().endswith(':'):
            continue
        m, ops = parts[1].strip(), (parts[2].strip() if len(parts) > 2 else '')
        if m == 'jmp':
            cur['ijmp' if not ops.startswith('0x') else 'jmp'] += 1
        elif m.startswith('j') or m.startswith('loop'):
            cur['jcc'] += 1
        elif m.startswith('cmov'):
            cur['cmov'] += 1
    problems = []
    for f in funcs:
        c = per.get(f['name'])
        if c is None:
            problems.append(f'{f["name"]}: no llvm-objdump listing')
            continue
        if c['jcc'] or c['cmov'] or c['ijmp'] < len(vmlib.HANDLERS) or c['ijmp'] != f['indirect_jmps']:
            problems.append(f'{f["name"]}: llvm-objdump jcc={c["jcc"]} cmov={c["cmov"]} '
                            f'indirect jmps={c["ijmp"]} (capstone {f["indirect_jmps"]})')
    dump = common._run([common.OBJDUMP, '-s', '-j', '.rdata', dll])
    start, blob = None, bytearray()
    for line in dump.splitlines():
        tok = line.split()
        if not line.startswith(' ') or len(tok) < 2:
            continue
        try:
            addr = int(tok[0], 16)
            row = bytes.fromhex(line[len(tok[0]) + 2:len(tok[0]) + 37].replace(' ', ''))
        except ValueError:
            continue
        if start is None:
            start = addr
        if addr != start + len(blob):
            problems.append(f'llvm-objdump .rdata dump: gap at {addr:#x}')
            break
        blob += row
    base = common.image_base(dll)
    st = Counter()
    for f in funcs:
        V, code = f['_V'], f['_code']
        off = base + int(f['bytecode_rva'], 16) - (start or 0)
        stored = bytes(blob[off:off + len(code)])
        if stored != code:
            problems.append(f'{f["name"]}: llvm-objdump .rdata bytes at {f["bytecode_rva"]} differ from the bytecode')
            continue
        st['functions'] += 1
        for pos, h, op in f['_info']['opc']:
            st['opcodes'] += 1
            st['plain'] += stored[pos] == op
            st['handler'] += V.handler_of(stored[pos]) == h
        st['first_ok'] += V.handler_of(stored[0]) == f['_info']['opc'][0][1]
    return problems, st


def normalize_timestamp(dll):
    """lld writes the link time into the COFF header (TimeDateStamp, the only byte that
    differs between two builds of vm.c); common.build_dll takes no linker flags, so do what
    -Brepro does: replace it with a hash of the image (computed with the field zeroed), and
    show that value in the map's Timestamp line. vm.dll and vm.map are then bit-identical
    across rebuilds."""
    import zlib
    with open(dll, 'rb') as fh:
        data = bytearray(fh.read())
    pe = int.from_bytes(data[0x3c:0x40], 'little')
    if data[pe:pe + 4] != b'PE' + bytes(2):
        raise RuntimeError(f'{dll}: no PE signature')
    data[pe + 8:pe + 12] = bytes(4)
    stamp = zlib.crc32(data)
    data[pe + 8:pe + 12] = stamp.to_bytes(4, 'little')
    with open(dll, 'wb') as fh:
        fh.write(data)
    mapf = common.map_path(dll)
    with open(mapf, encoding='utf-8') as fh:
        lines = fh.read().split(NL)
    lines = [f' Timestamp is {stamp:08x} (content hash, gen_vm.normalize_timestamp)'
             if ln.startswith(' Timestamp is ') else ln for ln in lines]
    with open(mapf, 'w', encoding='utf-8', newline=NL) as fh:
        fh.write(NL.join(lines))


def main():
    ap = argparse.ArgumentParser(description='Build and validate the vm suite.')
    ap.add_argument('--n', type=int, default=2000, help='validate.py inputs per function')
    ap.add_argument('--show', help='comma-separated names: print their disassembly')
    a = ap.parse_args()
    t0 = time.time()
    d = common.suite_dir(SUITE)
    funcs = []
    for V in vmlib.VARIANTS.values():
        for i, spec in enumerate(PLAN):
            f = build_function(V, i, spec)
            funcs.append(f)
            print(f'{f["name"]} {f["category"]:<6} nargs {f["nargs"]} paths {len(f["paths"]):>2} '
                  f'ops {f["ops"]:>2} bytecode {f["bytecode_size"]:>4} vinsns {f["vinsns"]:>5} '
                  f'draws {f["_attempts"]}', flush=True)
    print(f'programs drawn and cross-checked in {time.time() - t0:.1f} s; z3 witness queries: '
          f'{Z3_STATS["queries"]} (sat {Z3_STATS["sat"]}, unsat {Z3_STATS["unsat"]}, unknown '
          f'{Z3_STATS["unknown"]}), largest rlimit count {Z3_STATS["max_rlimit"]}')
    for V in vmlib.VARIANTS.values():
        with open(os.path.join(d, f'vm_{V.letter.lower()}.inc'), 'w', encoding='utf-8', newline=NL) as fh:
            fh.write(V.c_inc())
    src = os.path.join(d, 'vm.c')
    with open(src, 'w', encoding='utf-8', newline=NL) as fh:
        fh.write(c_source(funcs))
    dll = os.path.join(d, 'vm.dll')
    common.build_dll([src], dll)
    normalize_timestamp(dll)
    print(f'built {dll} in {time.time() - t0:.1f} s')
    problems = check_code(dll, funcs) + common.crosscheck_sizes(dll) + bytecode_rvas(dll, funcs)
    if not problems:
        more, st = objdump_check(dll, funcs)
        problems += more
    for p in problems:
        print('PROBLEM', p)
    if problems:
        return 1
    ij = sorted(f['indirect_jmps'] for f in funcs)
    print(f'llvm-objdump -d: every export has 0 jcc, 0 cmov, {ij[0]}..{ij[-1]} indirect jmps (dispatch)')
    n = st['opcodes']
    print(f'llvm-objdump -s -j .rdata: {st["functions"]} bytecodes read back identical; of their {n} '
          f'opcode bytes {st["plain"]} ({100 * st["plain"] / n:.2f} %) are stored as the plain opcode '
          f'and {st["handler"]} ({100 * st["handler"] / n:.2f} %) would reach the right handler '
          f'without decryption (first instruction: {st["first_ok"]} of {st["functions"]})')
    jpath = os.path.join(d, f'{SUITE}.json')
    clean = [{k: v for k, v in f.items() if not k.startswith('_')} for f in funcs]
    out = common.write_suite_json(jpath, SUITE, 'vm.dll', clean)
    ins = sorted(g['insns'] for g in out)
    print(f'insns per function: min {ins[0]} median {statistics.median(ins)} max {ins[-1]}')
    for g in out:
        if a.show and g['name'] in a.show.split(','):
            print(f'{g["name"]}:')
            print(common.listing(dll, int(g['rva'], 16), g['size']))
    code, text = common.validate(jpath, n=a.n)
    print(text.strip())
    print(f'total {time.time() - t0:.1f} s')
    return code


if __name__ == '__main__':
    sys.exit(main())
