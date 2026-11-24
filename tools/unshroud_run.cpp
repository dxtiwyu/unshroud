// Runs one function of a PE image: unshroud_run <pe> <rva> [--max N] [--sym regs|none] [--show]
// The image runs in a Windows process (src/win.hpp) unless --no-env (UNSHROUD_ENV=0). --init: the entry point runs first
// (DLL_PROCESS_ATTACH); --entry: <rva> is called as an entry point (image base, 1, 0); --args a,b,c,d: argument values;
// --trace: every system call on stderr; --no-exc: exceptions end the run; --calls: the system functions called;
// --null N: accesses below 0x10000 (0 never fault, 1 fault when a handler is there; default 1); --seed-args: the explorer's
// first inputs (symbolic 0x1111.. * k); --init-any: as --init, and the state is kept even when the entry point ends the process.
#include "../src/util.hpp"
#include "../src/pe.hpp"
#include "../src/win.hpp"
#include <memory>
#include <vector>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <map>
#include <string>
using namespace unshroud;

static const char* stopName(Stop s) {
  static const char* n[] = {"none", "max", "address", "return", "fault", "unsupported", "exception", "hook", "syscall", "halt"};
  return (unsigned)s < 10 ? n[s] : "?";
}

int main(int argc, char** argv) {
  unshroud::limitMemory();
  if (argc < 3) { printf("usage: unshroud_run <pe> <rva> [--max N] [--sym regs|none] [--show] [--repeat N]\n"); return 1; }
  const char* pe = argv[1]; u64 rva = strtoull(argv[2], nullptr, 16);
  u64 maxIns = 200000; bool symRegs = true, show = false, lazy = false, settle = false; int repeat = 1;
  bool useEnv = true, init = false, trace = false, exc = true, entry = false, calls = false, initAny = false, symArgs = false; int nullFaults = 1; std::vector<u64> args;
  if (const char* e = getenv("UNSHROUD_ENV")) useEnv = *e && *e != 48;
  if (const char* e = getenv("UNSHROUD_INIT")) init = *e && *e != 48;
  for (int i = 3; i < argc; i++) {
    if (!strcmp(argv[i], "--max") && i + 1 < argc) maxIns = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--sym") && i + 1 < argc) symRegs = !strcmp(argv[++i], "regs");
    else if (!strcmp(argv[i], "--show")) show = true;
    else if (!strcmp(argv[i], "--lazy")) lazy = true;
    else if (!strcmp(argv[i], "--settle")) settle = true;
    else if (!strcmp(argv[i], "--repeat") && i + 1 < argc) repeat = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--no-env")) useEnv = false;
    else if (!strcmp(argv[i], "--init")) init = true;
    else if (!strcmp(argv[i], "--trace")) trace = true;
    else if (!strcmp(argv[i], "--calls")) calls = true;
    else if (!strcmp(argv[i], "--no-exc")) exc = false;
    else if (!strcmp(argv[i], "--null") && i + 1 < argc) nullFaults = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--init-any")) init = initAny = true;
    else if (!strcmp(argv[i], "--seed-args")) { args = {0x1111111111111111ull, 0x2222222222222222ull, 0x3333333333333333ull, 0x4444444444444444ull}; symArgs = true; }
    else if (!strcmp(argv[i], "--entry")) { entry = true; symRegs = false; }
    else if (!strcmp(argv[i], "--args") && i + 1 < argc) { for (char* s = argv[++i]; *s;) { args.push_back(strtoull(s, &s, 0)); if (*s == ',') s++; } symRegs = false; }
  }
  Image img; std::shared_ptr<State> pristine;
  std::unique_ptr<WinEnv> env;
  {
    Engine base; if (!loadPE(base, pe, img)) { printf("cannot load %s\n", pe); return 1; }
    if (useEnv) { env.reset(new WinEnv); env->exceptions = exc; env->nullFaults = nullFaults; if (!env->build(base, img, pe)) { printf("no process environment (system DLLs not readable)\n"); env.reset(); } }
    if (env && init) {
      env->attach(base); env->trace = trace;
      auto before = base.snapshot(); std::string info;
      if (env->runInit(base, 200000000, &info)) printf("init: the entry point returned after %llu instructions\n", (unsigned long long)base.icount);
      else { printf("init: the entry point did not return (%s)%s\n", info.c_str(), initAny ? ": the state it left is kept" : ""); if (!initAny) base.restore(*before); else env->afterInit(base); }
      env->calls.clear(); env->unmodeled.clear(); env->errors.clear();
    }
    pristine = base.snapshot();
  }
  double tall = 0; u64 iall = 0;
  for (int rep = 0; rep < repeat; rep++) {
    auto t0 = std::chrono::steady_clock::now();
    Engine E;
    E.restore(*pristine);
    double tmap = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    const u64 STACK = 0x00007f0000000000ull, RETADDR = 0xdead0000ull, ARGBUF = 0x0000600000000000ull;
    u64 heap = 0x0000610000000000ull;
    u64 rsp = env ? WinEnv::RSP0 : STACK - 0x1000;
    if (env) { env->attach(E); env->trace = trace; }
    E.writeMem(rsp, &RETADDR, 8);
    E.g[RSP] = rsp; E.g[RBP] = rsp;
    const int argr[4] = {RCX, RDX, R8, R9}; const char* argn[4] = {"rcx", "rdx", "r8", "r9"};
    for (int i = 0; i < 4; i++) { E.g[argr[i]] = ARGBUF + i * 0x10000ull; if (symRegs) E.symbolizeReg(argr[i], argn[i]); }
    if (entry) { E.g[RCX] = img.base; E.g[RDX] = 1; E.g[R8] = 0; E.g[R9] = 0; }
    for (size_t i = 0; i < args.size() && i < 4; i++) { E.g[argr[i]] = args[i]; E.gs[argr[i]] = 0; if (symArgs) E.symbolizeReg(argr[i], argn[i]); }
    std::map<std::string, int> hits;
    if (!env) for (auto& kv : img.stubs) {
      std::string name = kv.second;
      E.hooks[kv.first] = [name, &heap, &hits](Engine& e) -> Stop {
        hits[name]++;
        u64 r = 0;
        if (name == "HeapAlloc" || name == "VirtualAlloc" || name == "GetProcessHeap" || name == "HeapReAlloc" || name == "LocalAlloc" || name == "GlobalAlloc") { r = heap; heap += 0x100000; }
        e.g[RAX] = r; e.gs[RAX] = 0;
        u64 ret; e.readMem(e.g[RSP], &ret, 8); e.g[RSP] += 8; e.rip = ret;
        return ST_NONE;
      };
    }
    E.stops.insert(RETADDR);
    E.rip = img.base + rva;
    E.lazy = lazy;
    auto t1 = std::chrono::steady_clock::now();
    Stop s = E.run(maxIns);
    const size_t recorded = E.X.tape.size();
    E.gs[RAX] = E.X.force(E.gs[RAX]);           // what a caller reads: the result (the path is built already)
    if (settle) E.settle();
    double trun = std::chrono::duration<double>(std::chrono::steady_clock::now() - t1).count();
    tall += trun; iall += E.icount;
    if (repeat > 1 && rep + 1 < repeat) continue;
    if (repeat > 1) printf("repeat %d: %.3fs, %llu ins, %.0f ins/s\n", repeat, tall, (unsigned long long)iall, iall / tall);
    const char* why = s == ST_ADDRESS && E.rip == RETADDR ? "returned" : stopName(s);
    printf("stop: %s at pc 0x%llx %s\n", why, (unsigned long long)E.rip, E.stopInfo.c_str());
    if (s == ST_UNSUPPORTED || s == ST_FAULT) printf("  at: %s\n", E.disasm(E.rip).c_str());
    printf("map %.2fs  run %.3fs  ins %llu  (%.0f ins/s)  nodes %zu  path %zu  native %llu  blocks %llu\n", tmap, trun,
           (unsigned long long)E.icount, E.icount / (trun > 0 ? trun : 1e-9), E.X.n.size(), E.path.size(), (unsigned long long)E.nativeCount,
           (unsigned long long)E.blocksDecoded);
    if (lazy) printf("lazy: %zu operations recorded, %llu built\n", recorded, (unsigned long long)E.X.forcedCount);
    if (lazy && getenv("UNSHROUD_TAPE")) {
      std::map<std::string, std::pair<int, int>> ops;
      for (auto& t : E.X.tape) { auto& o = ops[t.op == O_SUBL ? "sub" : opName(t.op)]; o.first++; if (t.real) o.second++; }
      for (auto& kv : ops) printf("  %-8s recorded %7d built %7d\n", kv.first.c_str(), kv.second.first, kv.second.second);
      size_t n = E.X.tape.size();
      for (size_t i = n > 40 ? n - 40 : 0; i < n; i++) { auto& t = E.X.tape[i]; printf("  #%zu %s w%u lo%u a=%x b=%x c=%x k=%llx depth %u real %u\n", i, t.op == O_SUBL ? "sub" : opName(t.op), t.w, t.lo, t.a, t.b, t.c, (unsigned long long)t.k, t.pad, t.real); }
    }
    if (!hits.empty()) { printf("import stubs hit:"); for (auto& h : hits) printf(" %s:%d", h.first.c_str(), h.second); printf("\n"); }
    if (env) {
      printf("rax = 0x%llx  rsp = 0x%llx\n", (unsigned long long)E.g[RAX], (unsigned long long)E.g[RSP]);
      if (calls || trace) { printf("system functions called:"); for (auto& h : env->calls) printf(" %s:%llu", h.first.c_str(), (unsigned long long)h.second); printf("\n"); }
      if (!env->unmodeled.empty()) { printf("without a model (returned 0):"); for (auto& h : env->unmodeled) printf(" %s:%llu", h.first.c_str(), (unsigned long long)h.second); printf("\n"); }
      if (!env->errors.empty()) { printf("model errors:"); for (auto& h : env->errors) printf(" %s:%llu", h.first.c_str(), (unsigned long long)h.second); printf("\n"); }
    }
    if (show) {
      printf("rax = %s\n", E.gs[RAX] ? E.X.str(E.gs[RAX], 8).c_str() : "(concrete)");
      size_t k = 0;
      for (auto& pc : E.path) { if (k++ >= 10) break; printf("  pc 0x%llx kind %d: %s\n", (unsigned long long)pc.pc, pc.kind, E.X.str(pc.cond, 6).c_str()); }
    }
  }
  return 0;
}
