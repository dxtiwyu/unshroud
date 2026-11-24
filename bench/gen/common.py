"""common.py: helpers for the bench suite generators.

Layout
  bench/gen/          truth.py, common.py, validate.py, run_all.py, probe_barriers.py,
                      suite_<name>.py (one generator per suite, by convention)
  bench/suites/<s>/   <s>.c / <s>.s, <s>.dll, <s>.map, <s>.json
A generator writes its sources, calls build_dll, checks the code where it matters
(insn_stats / listing: a branch that must stay a jcc, arithmetic that must stay
obfuscated), calls write_suite_json, then validate (validate.py on the json).
Under python -I the script's directory is not on sys.path; a generator in gen/ starts
    import os, sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import common, truth
(so never name a file in gen/ like a standard module).

Build (build_dll), the verified no-CRT recipe in two steps:
  clang --target=x86_64-pc-windows-msvc -O2 -ffreestanding -fno-builtin
        -fno-stack-protector [cflags] -c src.c                (each C source)
  clang --target=x86_64-pc-windows-msvc -c -x assembler src.s (each assembly source)
  clang --target=x86_64-pc-windows-msvc -shared -nostdlib -fuse-ld=lld -Wl,-noentry
        -Wl,-opt:noicf -Wl,-noimplib -Wl,-map:<out>.map [-Wl,-export:NAME ...] -o out.dll
-opt:noicf keeps two functions with identical code at two addresses (no folding).
Image base 0x180000000. Functions take up to four unsigned long long arguments (rcx,
rdx, r8, r9) and return one. No CRT: if clang emits calls to memset / memcpy, define
them. C exports: __declspec(dllexport). Assembly: Intel syntax ('.intel_syntax noprefix'
at the top, build_dll refuses a file without it); every .globl / .global symbol is
exported; inside a function use .L labels (any other label is a symbol: it would end
the function there, and write_suite_json reports the code that runs past that end).

Function sizes (func_sizes): leaf functions have no .pdata entry, so sizes come from
the linker map (publics and static symbols): size = next symbol address - this one,
bounded by the end of the section, minus the alignment padding after the last
instruction (trailing int3 / nop; trim=False keeps it). crosscheck_sizes(dll) compares
them with llvm-objdump: every export starts at its objdump label and ends where the
objdump listing of that label ends, the padding apart (gen/suite_smoke.py runs it).

Barrier patterns, measured with clang 23.1.5 -O2 (python -I gen/probe_barriers.py
builds every variant below again and checks each claim):
    #define BAR(v) __asm__ volatile("" : "+r"(v))     /* emits no instruction */
(a) Obfuscated arithmetic survives when the barrier sits on the intermediate terms:
      u64 a = x | y; BAR(a); u64 b = x & y; BAR(b); return a + b;   /* or, and, add */
    Without it clang folds the identity: (x | y) + (x & y) -> lea rax, [rcx + rdx];
    (x | y) - (x & y) -> xor; (x & ~y) + y -> or; (~x | y) - ~x -> and.
    A barrier on the inputs only (BAR(x); BAR(y)) or on the result only does NOT help:
    the identities need no known values. One barrier on one operand of the outer
    operation was enough for these two-term identities; to be safe put BAR on every
    intermediate. clang 23 does not know every identity ((x ^ y) + 2 * (x & y) stays
    xor / and / lea even without barriers), but do not rely on that.
    Non-volatile asm ("" : "+r"(v)) also held here, but only volatile is guaranteed
    not to be merged or moved; use BAR.
(b) A real conditional jump survives when each arm puts a barrier on its own,
    different result:
      u64 r;
      if ((s64)x < (s64)y) { r = y - x; BAR(r); } else { r = x ^ y; BAR(r); }
      return r;                                   /* cmp / jle, each arm separate */
    and for an opaque predicate with a dead arm:
      u64 t = x * (x + 1); BAR(t);                /* keeps x*(x+1) as written */
      if ((t & 1) == 0) { r = x + y; BAR(r); } else { r = 0xDEAD0001; BAR(r); }
      return r;                                   /* lea / imul / test / jne */
    Volatile asm cannot be speculated, and SimplifyCFG cannot merge two asm statements
    whose operands differ (an asm operand cannot become a phi), so neither arm can
    be turned into a cmov operand. What did NOT work: a plain if/else (cmove / cmovg);
    the same __asm__ volatile("" ::: "memory") in both arms (still cmov: the twin
    statements are hoisted out of the arms first); BAR on the predicate only (cmov).
    Also works: a different asm text in each arm (__asm__ volatile("# live") /
    __asm__ volatile("# dead")). An asm statement in one arm only keeps the jcc, but
    the other arm's constant is then loaded before the branch.
    Global alternative: cflags=['-mllvm', '-x86-cmov-converter-force-all=true'] turns
    every cmov into a jcc (each arm in its own block) for the whole DLL.
    clang 23 does not fold x*(x+1)&1 (without BAR(t) it computes the low bit of
    x * ~x in 32 bits); BAR(t) keeps the predicate as written.
    More shapes (same rule: BAR on each arm's own result): if / else if / else
    chains and nested ifs give one jcc per test; a && b (or ||) in one if is
    computed with setcc and ends in a single jcc (nest the ifs for one jcc per
    comparison); a switch becomes a jump table (an indirect jmp through .rdata)
    unless cflags=['-fno-jump-tables'] (then a chain of jcc).
    A branch you did not write: a 64-bit div / idiv gets a test of the operands
    against 2**32 and a 32-bit div on the short side (both sides give the same
    value); cflags=['-Xclang', '-target-feature', '-Xclang', '-idivq-to-divl'] removes it.
Check every function that must keep a jcc with insn_stats(...)['jcc'] (and 'cmov').

API
  C_PRELUDE                       typedef u64 / s64, EXPORT, BAR for generated C
  suite_dir(suite)                bench/suites/<suite> (created)
  scratch_dir(prefix)             a new directory under bench/_tmp (remove it when done)
  build_dll(sources, out_dll, cflags=(), asm=False, exports=())  -> map path (BuildError)
  exports(dll) {name: rva}, image_base(dll), code_sections(dll), read(dll, rva, size)
  parse_map(map_file) [(name, va)], func_sizes(dll, map_file=None, trim=True) {name: size}
  disasm(dll, rva, size) [Insn], count_insns(...), listing(...) str, insn_stats(...) Counter
  code_extent(dll, rva, size, others), crosscheck_sizes(dll) [problems vs llvm-objdump]
  find_witness(cond, nargs) [x, y, z, w] or None (random search, then z3)
  partition_problem(conds, nargs) None when z3 proves exactly one cond always holds
  write_suite_json(path, suite, dll_name, functions) -> the function dicts written
  validate(json_path, n=2000, seed=1) -> (exit code, output) of validate.py
"""
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
from collections import Counter, namedtuple

import capstone
import pefile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import truth                                    # noqa: E402

NL = chr(10)
LLVM_BIN = os.environ.get('BENCH_LLVM_BIN', 'C:/Program Files/LLVM/bin')
CLANG = os.path.join(LLVM_BIN, 'clang.exe')
OBJDUMP = os.path.join(LLVM_BIN, 'llvm-objdump.exe')
TARGET = '--target=x86_64-pc-windows-msvc'
CFLAGS = ['-O2', '-ffreestanding', '-fno-builtin', '-fno-stack-protector']
LDFLAGS = ['-shared', '-nostdlib', '-fuse-ld=lld', '-Wl,-noentry', '-Wl,-opt:noicf', '-Wl,-noimplib']
IMAGE_BASE = 0x180000000
GEN = os.path.dirname(os.path.abspath(__file__))
BENCH = os.path.dirname(GEN)
SUITES = os.path.join(BENCH, 'suites')
TMP = os.path.join(BENCH, '_tmp')        # transient work directories (never outside bench)
C_PRELUDE = '''typedef unsigned long long u64;
typedef long long s64;
#define EXPORT __declspec(dllexport)
#define BAR(v) __asm__ volatile("" : "+r"(v))
'''


class BuildError(RuntimeError):
    """A compile or link step failed; the message holds the command and its output."""


def scratch_dir(prefix='work_'):
    """A new empty directory under bench/_tmp (the caller removes it)."""
    os.makedirs(TMP, exist_ok=True)
    return tempfile.mkdtemp(prefix=prefix, dir=TMP)


def suite_dir(suite):
    """bench/suites/<suite>, created if needed."""
    d = os.path.join(SUITES, suite)
    os.makedirs(d, exist_ok=True)
    return d


def map_path(dll):
    """The map build_dll writes next to the DLL: <out>.map."""
    return os.path.splitext(os.path.abspath(dll))[0] + '.map'


def _run(cmd):
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0:
        shown = ' '.join(f'"{c}"' if ' ' in c else c for c in cmd)
        raise BuildError(f'command failed (exit {p.returncode}): {shown}{NL}{p.stdout}{p.stderr}')
    return p.stdout + p.stderr


def _asm_globals(text):
    names = []
    for line in text.splitlines():
        for stmt in line.split('#')[0].split(';'):
            tok = stmt.strip().split(None, 1)
            if len(tok) == 2 and tok[0] in ('.globl', '.global'):
                names += [n.strip() for n in tok[1].split(',') if n.strip()]
    return [n for n in names if f'-export:{n}' not in text]


def build_dll(sources, out_dll, cflags=(), asm=False, exports=()):
    """Build out_dll (see the module doc); return the path of its map (<out>.map).

    sources: a path or a list of paths. A source is assembly when asm=True or its
    extension is .s / .S / .asm (.S goes through the preprocessor); C otherwise.
    cflags: extra clang flags for the C sources. exports: more names to export.
    Raises BuildError with the failing command and the compiler / linker output."""
    if isinstance(sources, str):
        sources = [sources]
    out_dll = os.path.abspath(out_dll)
    os.makedirs(os.path.dirname(out_dll), exist_ok=True)
    mapf = map_path(out_dll)
    names = list(exports)
    tmp = scratch_dir('build_')
    try:
        objs = []
        for i, src in enumerate(sources):
            src = os.path.abspath(src)
            if not os.path.isfile(src):
                raise BuildError(f'no such source: {src}')
            stem, ext = os.path.splitext(os.path.basename(src))
            obj = os.path.join(tmp, f'{i}_{stem}.o')
            if asm or ext in ('.s', '.S', '.asm'):
                text = open(src, encoding='utf-8', errors='replace').read()
                if '.intel_syntax' not in text:
                    raise BuildError(f'{src}: put ".intel_syntax noprefix" at the top (Intel syntax)')
                lang = 'assembler-with-cpp' if ext == '.S' else 'assembler'
                _run([CLANG, TARGET, '-c', '-x', lang, src, '-o', obj])
                names += _asm_globals(text)
            else:
                _run([CLANG, TARGET] + CFLAGS + list(cflags) + ['-c', src, '-o', obj])
            objs.append(obj)
        for f in (out_dll, mapf):
            try:
                if os.path.exists(f):
                    os.remove(f)
            except OSError as e:
                raise BuildError(f'cannot replace {f}: {e} (is the DLL loaded by a running process?)') from None
        exp = [f'-Wl,-export:{n}' for n in dict.fromkeys(names)]
        _run([CLANG, TARGET] + LDFLAGS + [f'-Wl,-map:{mapf}'] + exp + ['-o', out_dll] + objs)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return mapf


# ---------------------------------------------------------------- PE, map, sizes
_PE_CACHE = {}


def _pe(dll):
    """pefile.PE of dll, read into memory (the file stays unlocked), cached until it changes."""
    path = os.path.abspath(dll)
    st = os.stat(path)
    key = (st.st_mtime_ns, st.st_size)
    hit = _PE_CACHE.get(path)
    if hit is None or hit[0] != key:
        with open(path, 'rb') as fh:
            pe = pefile.PE(data=fh.read(), fast_load=True)
        pe.parse_data_directories(directories=[pefile.DIRECTORY_ENTRY['IMAGE_DIRECTORY_ENTRY_EXPORT']])
        hit = (key, pe)
        _PE_CACHE[path] = hit
    return hit[1]


def image_base(dll):
    """Preferred image base of dll (0x180000000 with the recipe)."""
    return _pe(dll).OPTIONAL_HEADER.ImageBase


def exports(dll):
    """{exported name: rva} (forwarders skipped)."""
    d = getattr(_pe(dll), 'DIRECTORY_ENTRY_EXPORT', None)
    if d is None:
        return {}
    return {s.name.decode(): s.address for s in d.symbols if s.name and not s.forwarder}


def code_sections(dll):
    """[(name, start_rva, end_rva)] of the executable sections (end = start + VirtualSize)."""
    out = []
    for s in _pe(dll).sections:
        if s.Characteristics & 0x20000000:          # IMAGE_SCN_MEM_EXECUTE
            name = s.Name.rstrip(bytes(1)).decode(errors='replace')
            out.append((name, s.VirtualAddress, s.VirtualAddress + s.Misc_VirtualSize))
    return out


def read(dll, rva, size):
    """size bytes of the image at rva."""
    return _pe(dll).get_data(rva, size)


def parse_map(map_file):
    """[(name, va)] of an lld-link map: 'Publics by Value' and 'Static symbols'."""
    syms = []
    active = False
    with open(map_file, encoding='utf-8', errors='replace') as fh:
        for line in fh:
            if 'Publics by Value' in line:
                active = True
                continue
            tok = line.split()
            if not active or len(tok) < 3 or len(tok[0]) != 13 or tok[0][4] != ':':
                continue
            try:
                sec = int(tok[0][:4], 16)
                va = int(tok[2], 16)
            except ValueError:
                continue
            if sec:                                  # section 0: absolute symbols
                syms.append((tok[1], va))
    return syms


def func_sizes(dll, map_file=None, trim=True):
    """{name: size} of every map symbol in an executable section: next symbol - this
    one, bounded by the section end, minus trailing int3 / nop padding when trim."""
    base = image_base(dll)
    secs = code_sections(dll)
    bysec = {}
    for name, va in parse_map(map_file or map_path(dll)):
        rva = va - base
        for sec in secs:
            if sec[1] <= rva < sec[2]:
                bysec.setdefault(sec, []).append((rva, name))
                break
    sizes = {}
    for sec, syms in bysec.items():
        addrs = sorted({rva for rva, _ in syms}) + [sec[2]]
        nxt = dict(zip(addrs, addrs[1:]))
        for rva, name in syms:
            size = nxt[rva] - rva
            sizes[name] = _trimmed(dll, rva, size) if trim else size
    return sizes


def _trimmed(dll, rva, size):
    end = rva
    for i in disasm(dll, rva, size):
        if i.mnemonic not in ('int3', 'nop'):
            end = i.rva + i.size
    return end - rva


# ---------------------------------------------------------------- disassembly
Insn = namedtuple('Insn', 'rva size mnemonic op_str raw')
_MD = {}


def _md(detail=False):
    md = _MD.get(detail)
    if md is None:
        md = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
        md.detail = detail
        md.skipdata = not detail
        _MD[detail] = md
    return md


def disasm(dll, rva, size):
    """Linear capstone disassembly of [rva, rva + size): a list of Insn(rva, size,
    mnemonic, op_str, raw); jump targets in op_str are rvas; undecodable bytes are
    Insn(..., '.byte', ...)."""
    return [Insn(i.address, i.size, i.mnemonic, i.op_str, bytes(i.bytes))
            for i in _md().disasm(read(dll, rva, size), rva)]


def count_insns(dll, rva, size):
    """Number of instructions in [rva, rva + size) (undecodable bytes not counted)."""
    return sum(1 for i in disasm(dll, rva, size) if i.mnemonic != '.byte')


def listing(dll, rva, size):
    """Printable disassembly: one 'rva: bytes  mnemonic operands' line per instruction."""
    return NL.join(f'{i.rva:8x}: {i.raw.hex(" "):<30} {i.mnemonic} {i.op_str}'.rstrip()
                   for i in disasm(dll, rva, size))


def insn_stats(dll, rva, size):
    """Counter: insns, jcc, jmp, cmov, setcc, call, ret, data (undecodable bytes)."""
    c = Counter()
    for i in disasm(dll, rva, size):
        m = i.mnemonic
        if m == '.byte':
            c['data'] += 1
            continue
        c['insns'] += 1
        if m == 'jmp':
            c['jmp'] += 1
        elif m.startswith('j') or m.startswith('loop'):
            c['jcc'] += 1
        elif m.startswith('cmov'):
            c['cmov'] += 1
        elif m.startswith('set'):
            c['setcc'] += 1
        elif m in ('call', 'ret'):
            c[m] += 1
    return c


def code_extent(dll, rva, size, others=()):
    """Follow the code from rva: fall-through and direct jumps; calls are not entered,
    a jump to the start of another function (others: rvas) is a tail call. Returns
    (hi, problems): the end of the furthest instruction reached, and what could not be
    followed or left [rva, rva + size) (indirect jumps, undecodable bytes, code past
    the end of the function)."""
    sec = next((s for s in code_sections(dll) if s[1] <= rva < s[2]), None)
    if sec is None:
        return rva, [f'{rva:#x} is not in an executable section']
    data = read(dll, sec[1], sec[2] - sec[1])
    md = _md(True)
    others = set(others) - {rva}
    end = rva + size
    hi, problems, seen, todo = rva, [], set(), [rva]
    while todo:
        a = todo.pop()
        while a not in seen:
            if not (rva <= a < end):
                problems.append(f'code at {a:#x} is reached but lies outside [{rva:#x}, {end:#x})')
                break
            seen.add(a)
            ins = next(md.disasm(data[a - sec[1]:a - sec[1] + 16], a, 1), None)
            if ins is None:
                problems.append(f'undecodable byte at {a:#x}')
                break
            hi = max(hi, a + ins.size)
            m = ins.mnemonic
            if m in ('ret', 'retf', 'iretq', 'int3', 'ud2', 'hlt'):
                break
            if m == 'jmp' or m.startswith('j') or m.startswith('loop'):
                op = ins.operands[0] if ins.operands else None
                if op is None or op.type != capstone.x86.X86_OP_IMM:
                    problems.append(f'indirect {m} at {a:#x} not followed')
                    if m == 'jmp':
                        break
                elif op.imm not in others:
                    todo.append(op.imm)
                if m == 'jmp':
                    break
            a += ins.size
    return hi, problems


# ---------------------------------------------------------------- witnesses, partitions
_PICKS = [0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x7fffffff, 0x80000000, 0xffffffff,
          2**63 - 1, 2**63, 2**64 - 2, 2**64 - 1]


def _pick(r):
    c = r.random()
    if c < 0.25:
        return r.choice(_PICKS)
    if c < 0.45:
        return r.randrange(64)
    if c < 0.55:
        return (1 << 64) - 1 - r.randrange(64)
    return r.getrandbits(r.choice([8, 16, 32, 63, 64, 64]))


def find_witness(cond, nargs, seed=0, tries=20000, use_z3=True, timeout_ms=10000):
    """An input [x, y, z, w] (zeros beyond nargs) on which cond holds, or None.
    Random edge / small / random values first, then z3 (when use_z3)."""
    f = truth.compile(cond)
    r = random.Random(f'{seed}:{cond}')
    pad = [0] * (4 - nargs)
    for _ in range(tries):
        a = [_pick(r) for _ in range(nargs)] + pad
        if f(*a):
            return a
    if not use_z3:
        return None
    import z3
    xs = [z3.BitVec(v, 64) for v in truth.VARS]
    s = z3.Solver()
    s.set('timeout', timeout_ms)
    s.add(truth.to_z3(cond, xs))
    s.add(*[v == 0 for v in xs[nargs:]])
    if s.check() != z3.sat:
        return None
    m = s.model()
    a = [m.eval(v, model_completion=True).as_long() for v in xs]
    return a if f(*a) else None


def partition_problem(conds, nargs, timeout_ms=20000):
    """Prove with z3 that exactly one of conds holds for every input (variables beyond
    nargs fixed to 0). Returns None when proven, else a message: a counterexample
    input for a gap or an overlap, or 'unknown' (timeout)."""
    import z3
    xs = [z3.BitVec(v, 64) for v in truth.VARS]
    terms = [truth.to_z3(c, xs) for c in conds]
    zero = [v == 0 for v in xs[nargs:]]

    def model(*extra):
        s = z3.Solver()
        s.set('timeout', timeout_ms)
        s.add(*zero, *extra)
        r = s.check()
        if r == z3.sat:
            m = s.model()
            return [m.eval(v, model_completion=True).as_long() for v in xs]
        return 'unknown' if r == z3.unknown else None

    a = model(z3.Not(z3.Or(*terms)))
    if a is not None:
        return 'gap: ' + (a if a == 'unknown' else f'no cond holds on {[hex(v) for v in a]}')
    for i in range(len(terms)):
        for j in range(i + 1, len(terms)):
            a = model(terms[i], terms[j])
            if a is not None:
                return f'overlap {i}/{j}: ' + (a if a == 'unknown' else f'both hold on {[hex(v) for v in a]}')
    return None


# ---------------------------------------------------------------- suite json
SPEC_KEYS = ('name', 'rva', 'size', 'insns', 'nargs', 'category', 'difficulty',
             'truth', 'paths', 'opaque')
REQUIRED = ('name', 'nargs', 'category', 'difficulty', 'paths')


def _expr_problems(where, e, kind, nargs):
    try:
        truth.parse(e, kind)
    except truth.ExprError as ex:
        return [f'{where}: {ex}']
    extra = truth.variables(e) - set(truth.VARS[:nargs])
    return [f'{where}: uses {sorted(extra)} but nargs={nargs}'] if extra else []


def _check_function(f):
    """Problems of one function dict (before the DLL is looked at)."""
    errs = [f'missing "{k}"' for k in REQUIRED if k not in f]
    if errs:
        return errs
    nargs = f['nargs']
    if type(nargs) is not int or not 0 <= nargs <= 4:
        return [f'nargs={nargs!r} (0..4)']
    if not isinstance(f['category'], str) or not f['category']:
        errs.append('category must be a non-empty string')
    if type(f['difficulty']) is not int:
        errs.append('difficulty must be an int')
    paths = f['paths']
    if not isinstance(paths, list) or not paths:
        return errs + ['paths must be a non-empty list']
    for i, p in enumerate(paths):
        if not isinstance(p, dict) or not {'cond', 'out', 'witness'} <= set(p):
            errs.append(f'path {i}: needs cond, out, witness')
            continue
        perrs = _expr_problems(f'path {i} cond', p['cond'], 'bool', nargs)
        perrs += _expr_problems(f'path {i} out', p['out'], 'val', nargs)
        errs += perrs
        ws = p['witness']
        if not isinstance(ws, list) or not ws:
            errs.append(f'path {i}: witness must be a non-empty list of inputs')
            continue
        for w in ws:
            ok = (isinstance(w, list) and nargs <= len(w) <= 4 and
                  all(type(v) is int and 0 <= v <= truth.MASK for v in w) and not any(w[nargs:]))
            if not ok:
                errs.append(f'path {i}: bad witness {w!r} (list of {nargs}..4 ints in [0, 2**64), zero beyond nargs)')
            elif not perrs and not truth.compile(p['cond'])(*w):
                errs.append(f'path {i}: witness {w!r} does not satisfy its cond {p["cond"]!r}')
    if 'truth' in f and f['truth'] is not None:
        if len(paths) != 1:
            errs.append('truth must be null when the function has several paths')
        errs += _expr_problems('truth', f['truth'], 'val', nargs)
    for i, o in enumerate(f.get('opaque') or []):
        if not isinstance(o, dict) or not isinstance(o.get('kind'), str) or type(o.get('always')) is not bool:
            errs.append(f'opaque {i}: needs kind (string) and always (bool)')
        elif o.get('dead_out') is not None:
            errs += _expr_problems(f'opaque {i} dead_out', o['dead_out'], 'val', nargs)
    return errs


def write_suite_json(path, suite, dll_name, functions, check_extent=True):
    """Write the suite json (format: validate.py docstring) and return the function dicts.

    functions: dicts with name, nargs, category, difficulty, paths ([{cond, out,
    witness}]), optional truth (default: the out of a single path, else None) and
    opaque (default []), plus any suite-specific fields (kept, after the standard
    ones). rva / size / insns come from the DLL (dll_name, relative to the json) and
    its map; witnesses are padded to 4 values. Every expression is checked with truth,
    every witness against its cond, every rva for uniqueness, and (check_extent) the
    code reachable from each entry must stay inside [rva, rva + size).
    Raises ValueError listing every problem; nothing is written then."""
    path = os.path.abspath(path)
    dll = os.path.join(os.path.dirname(path), dll_name)
    exp = exports(dll)
    sizes = func_sizes(dll, map_path(dll))
    starts = set(exp.values())
    errors, out, by_rva = [], [], {}
    names = [f.get('name') for f in functions]
    for f in sorted(functions, key=lambda f: str(f.get('name'))):
        name = f.get('name')
        errs = _check_function(f)
        if not isinstance(name, str) or not name:
            errs.append('name must be a non-empty string')
        elif names.count(name) > 1:
            errs.append('duplicate name')
        elif name not in exp:
            errs.append(f'not exported by {dll_name}')
        elif name not in sizes:
            errs.append(f'not in the map {os.path.basename(map_path(dll))}')
        if errs:
            errors += [f'{name}: {e}' for e in errs]
            continue
        rva, size = exp[name], sizes[name]
        if rva in by_rva:
            errors.append(f'{name}: same rva {rva:#x} as {by_rva[rva]}')
        by_rva[rva] = name
        if size <= 0:
            errors.append(f'{name}: size {size}')
            continue
        if check_extent:
            hi, problems = code_extent(dll, rva, size, starts)
            errors += [f'{name}: {p}' for p in problems if 'outside' in p or 'undecodable' in p]
        paths = [dict(p, witness=[list(w) + [0] * (4 - len(w)) for w in p['witness']]) for p in f['paths']]
        t = f['truth'] if 'truth' in f else (paths[0]['out'] if len(paths) == 1 else None)
        g = {'name': name, 'rva': hex(rva), 'size': size, 'insns': count_insns(dll, rva, size),
             'nargs': f['nargs'], 'category': f['category'], 'difficulty': f['difficulty'],
             'truth': t, 'paths': paths, 'opaque': list(f.get('opaque') or [])}
        g.update((k, v) for k, v in f.items() if k not in SPEC_KEYS)
        out.append(g)
    if not functions:
        errors.append('no functions')
    if errors:
        raise ValueError(f'{len(errors)} problem(s) in suite {suite}:{NL}' + NL.join(errors))
    top = {'suite': suite, 'dll': dll_name.replace(chr(92), '/'), 'image_base': hex(image_base(dll))}
    lines = ['{' + ', '.join(f'{json.dumps(k)}: {json.dumps(v)}' for k, v in top.items()) + ',',
             ' "functions": [']
    lines += ['  ' + json.dumps(g) + (',' if i + 1 < len(out) else '') for i, g in enumerate(out)]
    lines.append(' ]}')
    with open(path, 'w', encoding='utf-8', newline=NL) as fh:
        fh.write(NL.join(lines) + NL)
    with open(path, encoding='utf-8') as fh:
        assert json.load(fh)['functions'] == out
    return out


def validate(json_path, n=2000, seed=1, extra=()):
    """Run validate.py on json_path in a fresh process; return (exit code, output)."""
    cmd = [sys.executable, '-I', os.path.join(GEN, 'validate.py'), json_path,
           '--n', str(n), '--seed', str(seed)] + list(extra)
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


# ---------------------------------------------------------------- llvm-objdump cross-check
def objdump_functions(dll):
    """{label: [(rva, size, mnemonic)]} from llvm-objdump -d (labels = exported names)."""
    text = _run([OBJDUMP, '-d', '--x86-asm-syntax=intel', dll])
    base = image_base(dll)
    funcs, cur = {}, None
    for line in text.splitlines():
        tok = line.split()
        if len(tok) == 2 and tok[1].startswith('<') and tok[1].endswith('>:'):
            cur = funcs.setdefault(tok[1][1:-2], [])
            continue
        parts = line.split(chr(9))
        if cur is None or len(parts) < 2 or ':' not in parts[0]:
            continue
        addr, raw = parts[0].split(':', 1)
        try:
            va = int(addr.strip(), 16)
        except ValueError:
            continue
        cur.append((va - base, len(raw.split()), parts[1].strip()))
    return funcs


def crosscheck_sizes(dll, map_file=None):
    """Problems (a list of strings, empty when all agree) between the exports +
    func_sizes and llvm-objdump: each function must start at its objdump label; the
    instructions objdump lists from there up to the next map symbol must end exactly at
    that symbol; and rva + size must be the end of the last of them that is not
    padding (int3 / nop). (objdump labels only exports: a static function after an
    export is listed under the export's label, hence the bound by the next symbol.)"""
    sizes = func_sizes(dll, map_file)
    raw = func_sizes(dll, map_file, trim=False)
    od = objdump_functions(dll)
    problems = []
    for name, rva in sorted(exports(dll).items()):
        insns = od.get(name)
        if not insns:
            problems.append(f'{name}: no objdump label')
            continue
        if name not in sizes:
            problems.append(f'{name}: not in the map')
            continue
        if insns[0][0] != rva:
            problems.append(f'{name}: objdump label at {insns[0][0]:#x}, export at {rva:#x}')
        limit = rva + raw[name]
        mine = [i for i in insns if i[0] < limit]
        if mine[-1][0] + mine[-1][1] != limit:
            problems.append(f'{name}: objdump decodes across the next symbol at {limit:#x}')
        real = [i for i in mine if i[2] not in ('int3', 'nop')]
        od_end = real[-1][0] + real[-1][1] if real else rva
        if rva + sizes[name] != od_end:
            problems.append(f'{name}: size {sizes[name]} ends at {rva + sizes[name]:#x}, objdump at {od_end:#x}')
    return problems
