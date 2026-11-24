# Unshroud

A concolic execution and deobfuscation engine for x86-64 Windows code, built for obfuscated binaries: mixed
Boolean-arithmetic (MBA) expressions, opaque predicates, virtualization-based protection and mutated code.

Unshroud runs a function of a PE image with symbolic inputs, simplifies what the code computes, and explores its paths
by solving branch conditions. It is written from scratch in C++20 for one architecture (x86-64) and one platform
(Windows), and trades generality for speed and resolution on that target.

## What is in it

- **Expressions**: a hash-consed 64-bit expression DAG whose constructors normalize as they build (linear, xor and
  and/or normal forms, extract/concat, ranges, magic-number division turned back into division, De Morgan). Every
  rule can be checked on random values at run time (`UNSHROUD_CHECK`).
- **MBA simplification**: linear MBA through signature (corner-point) evaluation, including constants inside
  bitwise operations; nonlinear MBA by decomposition into few-term forms with products as atoms; boolean forms and
  synthesis. Each result is marked *exact* (proved) or *tested*.
- **Resolver**: slicing, a query cache, local search, modular low-bit unsatisfiability proofs and MBA preprocessing
  in front of [Bitwuzla](https://github.com/bitwuzla/bitwuzla).
- **Semantics**: x86-64 integer, SSE and AVX2 instructions with two-level lazy flags. Flags that the manual leaves
  undefined follow the host CPU (calibrated at start).
- **Native execution**: concrete code runs on the CPU. Traces are re-encoded with Zydis and run against a
  software page table with per-byte taint; any instruction that touches a symbolic byte goes back to the interpreter.
  Copy-on-write paged memory, snapshots and a journaled restore.
- **Exploration**: generational search with branch and path coverage; unknown memory reached through inputs becomes
  input (`--uc`); calls a path cannot get past are skipped and the path marked (`--havoc`); opaque branch sides
  proved dead.
- **A Windows process**: TEB/PEB, the loader's module list with the system DLLs mapped, API models, direct system
  calls by number, SEH and vectored exception dispatch, trap flag / `mov ss` / `iretq` / RF behaviour, debug
  registers, and privileged or hypervisor instructions faulting as they do on Windows.
- **Python module** (`unshroud.pyd`, nanobind): engine, expressions, simplifier and explorer from Python.

## Results

### MBA simplification: GAMBA data sets, Unshroud against Triton

The seven public MBA data sets of [GAMBA](https://github.com/DenuvoSoftwareSolutions/GAMBA), 64-bit: each line is an
obfuscated expression and its ground truth. Both engines are scored the same way (`bench/gamba/rescore.py`): one
node counter for the ground truth and both results (distinct subterms, no rewriting), and every result checked
against the ground truth on 200 random inputs.

- **solved**: the result is correct and no bigger than the ground truth.
- **e − gt → 0**: the engine's own simplifier reduces *expression minus ground truth* to 0 (the GAMBA criterion).

| Set | Expressions | Unshroud solved | Unshroud e − gt → 0 | Triton solved | Triton e − gt → 0 | Mean size: Unshroud / Triton / truth |
|---|---:|---:|---:|---:|---:|---|
| syntia | 500 | **95.4%** | **100%** | 66.8% | 36.6% | 3.6 / 5.0 / 3.7 |
| qsynth_ea | 500 | **87.0%** | **100%** | 22.6% | 10.6% | 7.5 / 16.3 / 9.3 |
| mba_obf_linear | 1,000 | **97.5%** | **100%** | 2.0% | 0.2% | 8.3 / 96.3 / 9.9 |
| mba_obf_nonlinear | 1,000 | **97.6%** | **100%** | 3.1% | 0.3% | 6.3 / 38.1 / 7.8 |
| mba_flatten | 1,000 * | **94.8%** | **100%** | 4.4% | 0.2% | 8.2 / 37.1 / 10.1 |
| neureduce | 1,000 * | **97.9%** | **100%** | 3.0% | 1.2% | 7.7 / 28.8 / 9.0 |
| loki_tiny | 1,000 * | **100%** | **100%** | 99.8% | 88.0% | 3.0 / 3.0 / 3.0 |

\* Evenly spaced samples (every 3rd, 10th and 25th line), because Triton needs hours for the full sets; both
engines are compared on the same lines. Unshroud alone on all 41,000 expressions: e − gt → 0 for every one, no wrong
result.

Expression by expression, Unshroud's result is smaller in 4,480 cases, the same size in 1,509 and bigger in 11. Unshroud
took 30 s for all 6,000; Triton about 3.4 hours of CPU time, with 1,002 expressions hitting the 10 s limit (part
of the Triton runs were on a faster machine).

Setup: Unshroud `unshroud_mbaset` with a 1 s budget per expression. Triton `triton-library` 1.0.0rc4 from PyPI, the
best of `simplify`, `simplify` with LLVM, `synthesize` and `synthesize` after LLVM for each expression, 10 s per
expression (after a timeout, the best of `simplify` and LLVM alone). A few Triton results (8 in mba_obf_nonlinear)
use operators outside the data sets' syntax and are not counted.

To reproduce (Git Bash, after building):

```sh
python -I bench/gamba/fetch.py                       # the data sets, hash-checked, into bench/gamba/data
for s in syntia qsynth_ea mba_obf_linear mba_obf_nonlinear mba_flatten neureduce loki_tiny; do
  build/unshroud_mbaset.exe bench/gamba/data/$s.txt --expr --jsonl bench/gamba/x_$s.jsonl
done
pip install triton-library psutil
python -I bench/gamba/tgamba.py bench/gamba/data/syntia.txt --jobs 4 --jsonl bench/gamba/t_syntia.jsonl
#   (the same for each set; --step 3 / 10 / 25 for mba_flatten / neureduce / loki_tiny)
python -I bench/gamba/rescore.py                     # the table
```

### Instruction semantics and the benchmark suites

`./test.sh` runs every instruction form found in the bundled DLLs on Unshroud and on the real CPU, concrete and with
symbolic inputs (0 differences), the Windows exception and trap tests against a native run of the same DLL, and four
benchmark suites with exact ground truth (MBA, opaque predicates, VM-based protection, mutation), where Unshroud reaches
every feasible path and resolves every output with no wrong result.

## Building

Windows only. Needs Visual Studio 2022 or later (C++ workload), [LLVM](https://github.com/llvm/llvm-project/releases)
`clang-cl`, [ninja](https://ninja-build.org/), Python 3, and [MSYS2](https://www.msys2.org/) for the solver.
Zydis, nanobind and Bitwuzla are git submodules pinned to the commits Unshroud is tested with.

```bat
git clone --recursive https://github.com/dxtiwyu/unshroud.git
cd unshroud
rem once, in an MSYS2 UCRT64 shell:
rem   pacman -S --needed mingw-w64-ucrt-x86_64-{gcc,meson,ninja,pkgconf,gmp,mpfr}
build.bat
```

The first `build.bat` builds the Bitwuzla submodule with MSYS2 UCRT64 (`deps/build_bitwuzla.sh`: one DLL with GMP,
MPFR and CaDiCaL linked in statically) and makes an MSVC import library for its C API; later builds reuse it. To use
an existing Bitwuzla install instead, set `BITWUZLA_DIR`; for MSYS2 outside `C:\msys64`, set `MSYS2_ROOT`.

The build goes to `build\`: the engine library, one executable per `tools\*.cpp` and `unshroud.pyd`.
`gen_ninja.py` lists the other settings (`UNSHROUD_CLANG_CL`, `UNSHROUD_PYTHON`, `UNSHROUD_PYLIB`, `UNSHROUD_OPT`). The default
flags include `-march=native`; set `UNSHROUD_OPT` to build for other CPUs.

## Testing

```sh
./test.sh          # everything (Git Bash); ./test.sh quick for the unit tests and CPU comparisons only
```

This runs the expression rules and simplifier on random inputs; every instruction form of the bundled DLLs
against the real CPU, concrete and symbolic (`t_diff`); native-execution edge cases; the Windows exception and trap
tests against a native run of the same DLL; and the four benchmark suites against their ground truth.

## Tools

| Tool | What it does |
|---|---|
| `unshroud_explore <pe> rva:nargs ...` | explores functions; JSON lines out (`--time`, `--paths`, `--uc`, `--env`, `--py`, ...) |
| `unshroud_run <pe> <rva>` | one run of a function, symbolic registers optional |
| `unshroud_mba`, `unshroud_mbaset` | MBA simplifier on SMT-LIB input, or on data sets of `expression,groundtruth` lines |
| `unshroud_smt` | the resolver on SMT-LIB 2 bit-vector queries (`--baseline`: Bitwuzla alone) |
| `unshroud_opaque <pe> start:site` | is a conditional jump decided by the code just before it? |
| `unshroud_tseg`, `unshroud_ctx`, `unshroud_deob` | replay of recorded Tenet traces: calling contexts, and the deobfuscated form of each instruction |
| `unshroud_bench` | instructions per second on small loops |
| `t_*` | the self-tests run by `test.sh` |

The Python scripts in `py/` are the suite scorer (`bench_unshroud.py`), the synthetic Windows process for Python-driven
runs (`winenv.py`, `winapi.py`, `explore_env.py`), exception and trap checks, control-flow helpers (`rdcfg.py`,
`deadsides.py`, `switches.py`, `static_cov.py`) and a generator of harder MBA (`mbagen.py`).

## Limits

- x86-64 only, PE images only, and it builds and runs only on Windows.
- x87 floating point is not implemented (paths that reach it end there).
- `int 2e` is modelled as an access violation; real hardware takes the legacy system-call gate.
- User mode only. The Windows process is emulated: the machine's real system DLLs are mapped (relocated, with
  their exports) and the image's own initialization can run (`--init`), but system DLL code is never executed.
  Calls into it run C++ models of those functions, and a function without a model returns 0, so code that depends
  on system behaviour nobody modelled can take another path than on real Windows.

## License

Apache License 2.0, see `LICENSE` and `NOTICE`. Third-party components keep their own licenses, see
`THIRD_PARTY_NOTICES.md`.
