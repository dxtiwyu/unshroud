"""gen_mut.py: the mut suite, VMProtect-style mutation at the x86 level.

usage: python -I suites/mut/gen_mut.py [--n 2000] [--no-validate] [--show NAME,NAME]
Rebuilds everything from SEED: mut.s (the assembly of every function), mut.dll (+ mut.map),
mut.json, then runs gen/validate.py on the json (native execution).

20 source programs (mut_prog.py: straight-line arithmetic / bitwise code over x, y, z, w
with 0-3 if / else on comparisons, 8-40 operations, no loops; degenerate draws are refused:
an intermediate value that never changes, such as t2 = (x ^ k) ^ x, a result that hardly
depends on one of the arguments, a constant path out, two paths with the same out), each
emitted by mut_emit.py
(linear-scan register allocation, spills to [rbp - 8k], flags live only between a cmp /
test and its jcc) and then mutated by mut_pass.py at three strengths: light (about 2x the
instructions of the unmutated emitter output), medium (about 5x) and heavy (about 15x).
The three functions of one program share its ground truth (the AST's paths).
Mutation kinds: equivalent substitutions (MBA / De Morgan forms, split immediates, lea /
push-pop forms of mov, push / pop as lea + mov, jcc inversion), constant unfolding,
dead code on free registers, push / pop pairs, stack round trips through junk slots,
pushfq / popfq protected junk, opaque predicates (always-taken jumps over dead blocks that
write live registers; never-taken jumps to dead arms returning a constant), values split
in two registers and recombined, and (medium, heavy) the code cut in chunks reordered and
chained by jmp. Every pass recomputes exact register / flag / slot liveness.

Checks: every mutated function is emulated (mut_x86.emulate: undefined flags poisoned,
unwritten stack reads, rsp and callee-saved registers checked at ret) on its witnesses and
random inputs against the program's interpreter, and the dead-tagged instructions must be
exactly the ones that never run (no junk, so no opaque predicate, in unreachable code);
the DLL's instruction count of every function equals the generated one; sizes are
cross-checked with llvm-objdump; on the DLL's own instructions, with every opaque jcc
going its recorded way, every listed opaque jcc is reachable, the unreachable
instructions are exactly the dead ones and a function has ifs + opaque jccs; then
write_suite_json and gen/validate.py.

Categories: linear (no if), branch (1-3 ifs, none nested), nested (an if inside an arm).
Difficulty 1..5: strength (light 1, medium 2, heavy 3) + 1 with an if + 1 when nested.
Suite-specific fields: strength, base_insns (unmutated emitter output), source (the
program id shared by its three strengths), ops, ifs, program (readable source),
mutations (count of each mutation kind applied, all of it in live code). Every opaque
record also has jcc_rva (hex rva of the jcc that tests it) and jcc_taken (true: that
jcc is always taken, false: never taken; a jcc inversion may flip the jump of either
form); dead_out is the constant its dead arm returns (the "ret" form) or null (the
"skip" form: a dead block jumped over).
Witnesses come from seeded random sampling only; z3 (deterministic rlimit, memory cap)
only proves infeasible if-combinations, and a program whose feasible path the sampling
misses is drawn again, so a rebuild gives the same files.
"""
import argparse
import json
import os
import random
import statistics
import sys
import time
import zlib
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), 'gen'))
import common                                   # noqa: E402
import mut_emit as E                            # noqa: E402
import mut_pass as MP                           # noqa: E402
import mut_prog as P                            # noqa: E402
import mut_x86 as X                             # noqa: E402

SUITE = 'mut'
SEED = 20261116
NL = chr(10)
STRENGTHS = ('light', 'medium', 'heavy')
LEVEL = {'light': 1, 'medium': 2, 'heavy': 3}
EMU_RANDOM = 40                                 # random inputs emulated per function
EXTRA_SAVED = ('rbx', 'rsi', 'rdi', 'r12', 'r13', 'r14', 'r15')
# (category, nargs, operations wanted, ifs, nested, variable shifts)
SPECS = [
    ('linear', 1, 10, 0, False, False), ('linear', 2, 14, 0, False, False),
    ('linear', 2, 22, 0, False, True), ('linear', 3, 18, 0, False, False),
    ('linear', 3, 30, 0, False, True), ('linear', 4, 26, 0, False, False),
    ('linear', 4, 36, 0, False, False),
    ('branch', 1, 12, 1, False, False), ('branch', 2, 16, 1, False, True),
    ('branch', 2, 20, 2, False, False), ('branch', 3, 24, 1, False, False),
    ('branch', 3, 28, 2, False, True), ('branch', 4, 32, 3, False, False),
    ('branch', 4, 34, 2, False, False),
    ('nested', 2, 18, 2, True, False), ('nested', 2, 24, 3, True, True),
    ('nested', 3, 22, 2, True, False), ('nested', 3, 28, 3, True, False),
    ('nested', 4, 30, 2, True, True), ('nested', 4, 34, 3, True, False),
]


REFUSED = []                                    # degenerate draws refused (printed by main)


def draw_program(k, spec):
    """(body, paths, draws) of source program k: drawn again until it has the shape of
    spec, 8..40 operations, both arms of every if feasible, a sampled witness for
    every feasible path, and nothing degenerate (mut_prog.degenerate: no constant
    intermediate value, a result that depends on every argument, no constant path out,
    no two paths with the same out; checked with its own rng, so a draw that passes
    is the one the earlier generator picked)."""
    cat, nargs, want, nif, nested, vshift = spec
    rng = random.Random(f'{SEED}:prog:{k}')
    for draw in range(1, 501):
        body = P.Gen(rng, nargs, vshift).program(want, nif, nested)
        if not 8 <= P.count_ops(body) <= 40 or P.count_ifs(body) != nif:
            continue
        if P.is_nested(body) != nested or P.uses_vshift(body) != vshift:
            continue
        paths, why = P.analyze(body, nargs, rng, allow_sat=False)
        if paths is None:
            continue
        bad = P.crosscheck(body, nargs, paths, rng)
        if bad:
            raise RuntimeError(f'program {k}: paths and interpreter disagree: {bad}')
        why = P.degenerate(body, nargs, paths, random.Random(f'{SEED}:degen:{k}:{draw}'))
        if why:
            REFUSED.append(f'program {k} draw {draw}: {why}')
            continue
        return body, paths, draw
    raise RuntimeError(f'program {k}: nothing suitable in 500 draws')


def check_emulation(name, code, body, nargs, paths, rng):
    """Emulate code on the witnesses and EMU_RANDOM random inputs (random initial
    registers and flags), compare with the interpreter, and check that the dead-tagged
    instructions are exactly the unreachable ones: no dead instruction ever ran, and
    every other instruction ran (the witnesses cover every path of the program, and
    the junk is straight-line code but for its opaque jumps). So every opaque jcc runs
    and no junk sits in dead code."""
    inputs = [w for p in paths for w in p['witness']] + [P.sample(rng, nargs) for _ in range(EMU_RANDOM)]
    trace = set()
    for a in inputs:
        init = {g: rng.getrandbits(64) for g in X.GPR}
        want = P.execute(body, a)[0]
        got = X.emulate(code, a, init, trace=trace)
        if got != want:
            raise RuntimeError(f'{name}: emulation gives {got:#x}, the program {want:#x}, on {a}')
    ran = sorted(i for i in trace if code[i].tag == 'dead')
    if ran:
        raise RuntimeError(f'{name}: dead code executed: {[X.fmt(code[i]).strip() for i in ran[:3]]}')
    idle = [i for i, ins in enumerate(code) if ins.m != 'label' and ins.tag != 'dead' and i not in trace]
    if idle:
        raise RuntimeError(f'{name}: {len(idle)} live instructions never executed, e.g. '
                           f'{[f"{i}: {X.fmt(code[i]).strip()}" for i in idle[:3]]}')
    return len(inputs)


def build_function(k, strength, spec, body, paths):
    """The mutated code of program k at one strength and its json fields."""
    cat, nargs, _, nif, nested, _ = spec
    name = f'mut_{k:02d}_{strength}'
    rng = random.Random(f'{SEED}:mut:{name}')
    base = E.emit(body, nargs, name)['code']
    base_n = MP.n_insns(base)
    check_emulation(name + ' (base)', base, body, nargs, paths, rng)
    lo, hi = {'light': (0, 1), 'medium': (1, 3), 'heavy': (2, 5)}[strength]
    extra = rng.sample(EXTRA_SAVED, rng.randint(lo, hi))
    em = E.emit(body, nargs, name, extra_saved=extra, njunk=1 + LEVEL[strength])
    ctx = MP.Ctx(name, rng, em['junk'], em['epi'], em['saved'])
    code = MP.mutate(ctx, em['code'], base_n, strength)
    for ins in code:
        X.check_operands(ins)
    opq = sorted(int(ins.tag[5:]) for ins in code if MP.is_opq(ins))
    if opq != list(range(len(ctx.opaque))):
        raise RuntimeError(f'{name}: opaque jcc tags {opq} for {len(ctx.opaque)} records')
    nemu = check_emulation(name, code, body, nargs, paths, rng)
    f = {'name': name, 'nargs': nargs, 'category': cat,
         'difficulty': LEVEL[strength] + (1 if nif else 0) + (1 if nested else 0),
         'paths': [{'cond': p['cond'], 'out': p['out'], 'witness': p['witness']} for p in paths],
         'opaque': ctx.opaque, 'strength': strength, 'base_insns': base_n, 'source': k,
         'ops': P.count_ops(body), 'ifs': nif, 'program': NL.join(P.show(body)),
         'mutations': dict(sorted(ctx.stats.items()))}
    return f, code, nemu


def asm_text(items):
    lines = ['# mut suite: generated by gen_mut.py (do not edit)', '    .intel_syntax noprefix', '    .text']
    for f, code in items:
        lines += ['', f'# {f["name"]}: strength {f["strength"]}, source program {f["source"]}, '
                      f'{f["base_insns"]} instructions unmutated']
        lines += ['#     ' + ln for ln in f['program'].split(NL)]
        lines += [f'    .globl {f["name"]}', '    .p2align 4, 0xcc', f'{f["name"]}:']
        lines += [X.fmt(i) for i in code]
    return NL.join(lines) + NL


def normalize_timestamp(dll):
    """Replace the link timestamp (PE header, and the map's 'Timestamp is' line) by a
    hash of the image, so that a rebuild gives identical files."""
    import pefile
    pe = pefile.PE(dll, fast_load=True)
    off = pe.FILE_HEADER.get_file_offset() + 4
    pe.close()
    data = bytearray(open(dll, 'rb').read())
    data[off:off + 4] = bytes(4)
    h = zlib.crc32(bytes(data))
    data[off:off + 4] = h.to_bytes(4, 'little')
    with open(dll, 'wb') as fh:
        fh.write(bytes(data))
    mapf = common.map_path(dll)
    lines = open(mapf, encoding='utf-8').read().split(NL)
    lines = [f' Timestamp is {h:08x} (content hash, gen_mut.normalize_timestamp)'
             if ln.startswith(' Timestamp is ') else ln for ln in lines]
    with open(mapf, 'w', encoding='utf-8', newline=NL) as fh:
        fh.write(NL.join(lines))


def locate_opaque(dll, items):
    """Add jcc_rva (the rva of its jcc in the DLL) and jcc_taken (that jcc is always
    taken: true, never taken: false) to every opaque record; the k-th instruction of the
    generated code is the k-th one decoded (check_dll checked the counts). Then check on
    the DLL's own instructions (static control flow, every opaque jcc going its
    recorded way) that every listed jcc is reachable, that the unreachable instructions
    are exactly the dead ones, and that the function has ifs + opaque jccs."""
    exp = common.exports(dll)
    sizes = common.func_sizes(dll)
    problems = []
    for f, code in items:
        dec = [i for i in common.disasm(dll, exp[f['name']], sizes[f['name']]) if i.mnemonic != '.byte']
        real = [x for x in code if x.m != 'label']
        way = {}
        for x, d in zip(real, dec):
            if MP.is_opq(x):
                if d.mnemonic != x.m:
                    raise RuntimeError(f'{f["name"]}: {d.mnemonic} at {d.rva:#x}, {x.m} generated')
                way[d.rva] = x.tag.startswith('opq_t')
                f['opaque'][int(x.tag[5:])].update(jcc_rva=hex(d.rva), jcc_taken=way[d.rva])
        at = {d.rva: k for k, d in enumerate(dec)}
        seen, todo = set(), [0]
        while todo:
            k = todo.pop()
            if k in seen:
                continue
            seen.add(k)
            m, a = dec[k].mnemonic, dec[k].rva
            if m == 'ret':
                continue
            if not m.startswith('j'):
                todo.append(k + 1)
                continue
            t = at[int(dec[k].op_str, 16)]
            todo += [t] if m == 'jmp' or way.get(a) is True else [k + 1] if way.get(a) is False else [k + 1, t]
        jcc = [k for k, d in enumerate(dec) if d.mnemonic.startswith('j') and d.mnemonic != 'jmp']
        ndead = sum(1 for x in real if x.tag == 'dead')
        if len(way) != len(f['opaque']) or not all(at[a] in seen for a in way):
            problems.append(f'{f["name"]}: an opaque jcc is missing or unreachable')
        if len(dec) - len(seen) != ndead:
            problems.append(f'{f["name"]}: {len(dec) - len(seen)} unreachable instructions, {ndead} dead ones')
        if any(k not in seen for k in jcc) or len(jcc) != f['ifs'] + len(f['opaque']):
            problems.append(f'{f["name"]}: {len(jcc)} jcc for {f["ifs"]} ifs and {len(f["opaque"])} opaque')
    if problems:
        raise RuntimeError('opaque check on the DLL failed:' + NL + NL.join(problems))


def check_dll(dll, items):
    """Instruction counts as generated, sizes as llvm-objdump sees them, jcc present."""
    exp = common.exports(dll)
    sizes = common.func_sizes(dll)
    problems = list(common.crosscheck_sizes(dll))
    for f, code in items:
        rva, size = exp[f['name']], sizes[f['name']]
        st = common.insn_stats(dll, rva, size)
        if st['insns'] != MP.n_insns(code) or st['data']:
            problems.append(f'{f["name"]}: {st["insns"]} instructions in the DLL, {MP.n_insns(code)} generated')
        if f['ifs'] and st['jcc'] < f['ifs']:
            problems.append(f'{f["name"]}: {st["jcc"]} jcc for {f["ifs"]} ifs')
    if problems:
        raise RuntimeError('DLL check failed:' + NL + NL.join(problems))


def summary(out):
    print('categories:', dict(sorted(Counter(f['category'] for f in out).items())))
    ins = sorted(f['insns'] for f in out)
    print(f'insns per function: min {ins[0]} median {statistics.median(ins)} max {ins[-1]}')
    for s in STRENGTHS:
        fs = [f for f in out if f['strength'] == s]
        rs = sorted(f['insns'] / f['base_insns'] for f in fs)
        n = sorted(f['insns'] for f in fs)
        print(f'  {s}: {len(fs)} functions, insns {n[0]}..{n[-1]}, x unmutated: min {rs[0]:.1f} '
              f'median {statistics.median(rs):.1f} max {rs[-1]:.1f}')
    kinds = Counter()
    for f in out:
        kinds.update(f['mutations'])
    groups = Counter()
    for k, v in kinds.items():
        groups[k.split('.')[0]] += v
    print('mutations applied:', dict(sorted(groups.items())))
    opq = Counter(o['kind'] + (' (ret)' if o['dead_out'] else ' (skip)') for f in out for o in f['opaque'])
    print(f'opaque predicates: {sum(opq.values())}')


def main():
    ap = argparse.ArgumentParser(description='Build the mut suite (see the module doc).')
    ap.add_argument('--n', type=int, default=2000, help='validate.py --n (default 2000)')
    ap.add_argument('--no-validate', action='store_true', help='stop after writing the json')
    ap.add_argument('--show', default='', help='print the disassembly of these functions')
    a = ap.parse_args()
    t0 = time.time()
    d = common.suite_dir(SUITE)
    items, draws, nemu = [], 0, 0
    for k, spec in enumerate(SPECS):
        body, paths, nd = draw_program(k, spec)
        draws += nd
        for s in STRENGTHS:
            f, code, ne = build_function(k, s, spec, body, paths)
            items.append((f, code))
            nemu += ne
    print(f'{len(items)} functions mutated, each emulated on its witnesses and {EMU_RANDOM} random '
          f'inputs ({nemu} runs, all equal to the program; dead code never ran, all other code ran); '
          f'{draws} program draws; {time.time() - t0:.1f} s')
    print(f'{len(REFUSED)} degenerate draws refused:')
    for why in REFUSED:
        print('   ', why)
    s_path = os.path.join(d, SUITE + '.s')
    with open(s_path, 'w', encoding='utf-8', newline=NL) as fh:
        fh.write(asm_text(items))
    dll = os.path.join(d, SUITE + '.dll')
    common.build_dll([s_path], dll)
    normalize_timestamp(dll)
    check_dll(dll, items)
    locate_opaque(dll, items)
    json_path = os.path.join(d, SUITE + '.json')
    out = common.write_suite_json(json_path, SUITE, SUITE + '.dll', [f for f, _ in items])
    summary(out)
    for name in filter(None, a.show.split(',')):
        g = next(x for x in out if x['name'] == name)
        print(common.listing(dll, int(g['rva'], 16), g['size']))
    if a.no_validate:
        return 0
    rc, text = common.validate(json_path, n=a.n)
    print(text.rstrip())
    print(f'total {time.time() - t0:.1f} s')
    return rc


if __name__ == '__main__':
    sys.exit(main())
