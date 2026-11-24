// Differential test of native execution (src/jit.hpp): two engines run the same functions of a PE from the same
// states - one with the interpreter only, one with generated code, every block compiled the first time it runs - in
// steps of random length. After every step the registers, the flags, the expressions, the path and (every few steps,
// and at the end) the whole memory must be the same. A difference is narrowed down to the instruction.
// usage: t_jit <pe> [--ins N] [--chunk K] [--hot H] [--uc] [--sym] [--init] [--seed S] [--mem N] [--quiet] rva ... | @file
#include "../src/util.hpp"
#include "../src/pe.hpp"
#include "../src/win.hpp"
#include "../src/jit.hpp"
#include <cstdio>
#include <cstring>
#include <fstream>
#include <memory>
#include <random>
#include <string>
using namespace unshroud;

struct World { Image img; std::unique_ptr<WinEnv> env; std::shared_ptr<State> pristine; };
static const u64 RET = 0xdead0000ull;

static bool setup(World& w, const char* pe, bool init, bool uc, bool jit, u32 hot) {
  Engine base; base.jitOn = jit; base.jitHot = hot;
  if (!loadPE(base, pe, w.img)) return false;
  w.env.reset(new WinEnv); w.env->retAddr = RET;
  if (!w.env->build(base, w.img, pe)) w.env.reset();
  if (w.env && init) {
    w.env->attach(base); std::string info;
    if (!w.env->runInit(base, 200000000, &info)) w.env->afterInit(base);
    printf("init %s: %llu instructions, %llu native%c", jit ? "with native code" : "interpreted", (unsigned long long)base.icount, (unsigned long long)base.jitIns, 10);
  }
  if (uc) for (auto& r : w.img.writable) base.markUnknown(r.first, r.second);
  w.pristine = base.snapshot();
  return true;
}

static void start(World& w, Engine& E, u64 rva, bool uc, bool sym, u64 seed) {
  E.restore(*w.pristine);
  const u64 rsp = w.env ? WinEnv::RSP0 : 0x7f0000000000ull - 0x1000;
  if (w.env) w.env->attach(E);
  E.writeMem(rsp, &RET, 8);
  E.g[RSP] = rsp; E.g[RBP] = rsp;
  const int regs[4] = {RCX, RDX, R8, R9}; const char* names[4] = {"x", "y", "z", "w"};
  for (int k = 0; k < 4; k++) {
    E.g[regs[k]] = seed ? seed * (k + 1) : uc ? E.ucFresh() : 0x1111111111111111ull * (k + 1);
    if (sym) E.symbolizeReg(regs[k], names[k]);
  }
  if (uc) {
    E.lazyMem = true;
    for (int k = 0; k < 4; k++) { const u64 a = rsp + 0x28 + 8 * k, sv = E.ucFresh(); E.writeMem(a, &sv, 8); if (sym) E.symbolizeMem(a, 8, "a" + std::to_string(5 + k)); }
  }
  E.rip = w.img.base + rva; E.stops.insert(RET);
  E.spinLimit = 200; E.spinReset(); E.loopLimit = 50000; E.runPageLimit = 4096; E.tableMax = 256;
}

static bool flagsSym(const Flags& f) {
  const u32 A6 = FL_ARITH;
  if (f.folded & A6) return true;
  const u32 lz = f.lazy & A6, pv = f.prev.lazy & A6 & ~lz;
  if (lz && (f.sa | f.sb | f.sr | f.sx)) return true;
  if (pv && (f.prev.sa | f.prev.sb | f.prev.sr | f.prev.sx)) return true;
  for (int p : {0, 2, 4, 6, 7, 11}) if (!((lz | pv) & (1u << p)) && f.sym[p]) return true;
  return false;
}

// what differs between the two engines ("": nothing)
static std::string cmp(Engine& A, Engine& B, bool mem) {
  char b[160]; std::string d;
  if (A.rip != B.rip) { snprintf(b, sizeof b, " rip %llx/%llx", (unsigned long long)A.rip, (unsigned long long)B.rip); d += b; }
  if (A.icount != B.icount) { snprintf(b, sizeof b, " icount %llu/%llu", (unsigned long long)A.icount, (unsigned long long)B.icount); d += b; }
  for (int r = 0; r < 16; r++) {
    if (A.g[r] != B.g[r]) { snprintf(b, sizeof b, " g%d %llx/%llx", r, (unsigned long long)A.g[r], (unsigned long long)B.g[r]); d += b; }
    if (A.gs[r] != B.gs[r]) { snprintf(b, sizeof b, " g%d-expr %u/%u", r, A.gs[r], B.gs[r]); d += b; }
  }
  const bool sa = flagsSym(A.fl), sb = flagsSym(B.fl);
  if (sa != sb) d += " flags-symbolic";
  else if (sa) {
    // Flag by flag: an expression in both engines or in neither; where there is one, it comes from the same deferred
    // operation (the same record) or is the same node. Flags without an expression may be held differently (a record
    // with plain operands in one engine, a bit in the other): their values are compared below, like all the others.
    const Flags &x = A.fl, &y = B.fl; bool same = true;
    const auto src = [](const Flags& f, int p, int& kind, const LazyRec*& rec) {      // 0 plain, 1 the record, 2 the one before, 3 its own node
      const u32 bit = 1u << p; kind = 0; rec = nullptr;
      if (f.lazy & bit) { if (f.sa | f.sb | f.sr | f.sx) kind = 1; }
      else if (f.prev.lazy & bit) { if (f.prev.sa | f.prev.sb | f.prev.sr | f.prev.sx) { kind = 2; rec = &f.prev; } }
      else if (f.sym[p] || (f.folded & bit)) kind = 3;
    };
    for (int p : {0, 2, 4, 6, 7, 11}) {
      int kx, ky; const LazyRec *rx, *ry; src(x, p, kx, rx); src(y, p, ky, ry);
      if (kx != ky) { same = false; break; }
      if (kx == 1) same = same && x.op == y.op && x.w == y.w && x.a == y.a && x.b == y.b && x.r == y.r && x.x == y.x && x.sa == y.sa && x.sb == y.sb && x.sr == y.sr && x.sx == y.sx;
      else if (kx == 2) same = same && rx->op == ry->op && rx->w == ry->w && rx->a == ry->a && rx->b == ry->b && rx->r == ry->r && rx->x == ry->x && rx->sa == ry->sa && rx->sb == ry->sb && rx->sr == ry->sr && rx->sx == ry->sx;
      else if (kx == 3) same = same && x.sym[p] == y.sym[p] && ((x.folded ^ y.folded) & (1u << p)) == 0;
    }
    if (!same) d += " flags-record";
  }
  if ((A.rflags() ^ B.rflags()) & (FL_ARITH | FL_DF)) { snprintf(b, sizeof b, " flags %llx/%llx", (unsigned long long)A.rflags(), (unsigned long long)B.rflags()); d += b; }
  for (int r = 0; r < 16; r++) if (memcmp(A.v[r], B.v[r], 32) || memcmp(A.vc[r], B.vc[r], sizeof A.vc[r])) { snprintf(b, sizeof b, " v%d", r); d += b; }
  if (A.vsym != B.vsym) d += " vsym";
  if (A.mxcsr != B.mxcsr) { snprintf(b, sizeof b, " mxcsr %x/%x", A.mxcsr, B.mxcsr); d += b; }
  if (A.fsbase != B.fsbase || A.gsbase != B.gsbase) d += " segment-base";
  if (A.path.size() != B.path.size()) { snprintf(b, sizeof b, " path %zu/%zu", A.path.size(), B.path.size()); d += b; }
  else for (size_t i = 0; i < A.path.size(); i++) if (A.path[i].cond != B.path[i].cond || A.path[i].pc != B.path[i].pc || A.path[i].taken != B.path[i].taken) { d += " path-constraint"; break; }
  if (A.X.n.size() != B.X.n.size() || A.X.vars.size() != B.X.vars.size()) { snprintf(b, sizeof b, " nodes %zu/%zu", A.X.n.size(), B.X.n.size()); d += b; }
  if (A.stopInfo != B.stopInfo) d += " stop-info " + A.stopInfo + "/" + B.stopInfo;
  if (mem && A.memHash() != B.memHash()) d += " memory";
  return d;
}

int main(int argc, char** argv) {
  _putenv_s("UNSHROUD_JIT_PAYK", "0");            // every block is compiled here, whether it pays or not (see Jit::run)
  unshroud::limitMemory();
  if (argc < 3) { printf("usage: t_jit <pe> [--ins N] [--chunk K] [--hot H] [--uc] [--sym] [--init] [--seed S] [--mem N] [--quiet] rva ... | @file%c", 10); return 1; }
  u64 maxIns = 2000000, chunk = 20000, seed = 0; u32 hot = 1; bool uc = false, sym = false, init = false, quiet = false; int memEvery = 16;
  std::vector<u64> rvas;
  for (int i = 2; i < argc; i++) {
    if (!strcmp(argv[i], "--ins")) maxIns = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--chunk")) chunk = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--hot")) hot = (u32)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--seed")) seed = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--mem")) memEvery = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--uc")) uc = true;
    else if (!strcmp(argv[i], "--sym")) sym = true;
    else if (!strcmp(argv[i], "--init")) init = true;
    else if (!strcmp(argv[i], "--quiet")) quiet = true;
    else if (argv[i][0] == '@') { std::ifstream f(argv[i] + 1); std::string t; while (std::getline(f, t, ',')) { if (!t.empty()) rvas.push_back(strtoull(t.c_str(), nullptr, 16)); } }
    else rvas.push_back(strtoull(argv[i], nullptr, 16));
  }
  World wa, wb;
  if (!setup(wa, argv[1], init, uc, false, hot) || !setup(wb, argv[1], init, uc, true, hot)) { printf("cannot load %s%c", argv[1], 10); return 1; }
  jitCalibrate(true);
  u64 totalIns = 0, totalJit = 0, steps = 0; int bad = 0, done = 0;
  for (u64 rva : rvas) {
    Engine A, B; A.jitOn = false; B.jitOn = true; B.jitHot = hot;
    start(wa, A, rva, uc, sym, seed); start(wb, B, rva, uc, sym, seed);
    std::mt19937_64 rng(rva * 0x9E3779B97F4A7C15ull + 1);
    const auto next = [&](std::mt19937_64& g) { return (u64)(g() % 4 == 0 ? 1 + g() % 16 : 1 + g() % chunk); };
    std::shared_ptr<State> ca = A.snapshot(), cb = B.snapshot(); std::mt19937_64 crng = rng; int cstep = 0, step = 0;
    std::string diff; u64 k = 0; Stop sa = ST_NONE, sb = ST_NONE;
    const u64 ic0 = A.icount;
    for (;; step++) {
      if (step - cstep >= 64) { ca = A.snapshot(); cb = B.snapshot(); crng = rng; cstep = step; }
      k = next(rng);
      const u64 before = A.icount;
      sa = A.run(k); sb = B.run(k);
      const bool end = sa != ST_COUNT || A.icount - before < k || A.icount - ic0 >= maxIns;
      diff = cmp(A, B, end || (memEvery && step % memEvery == 0));
      if (sa != sb) diff += " stop";
      if (!diff.empty() || end) break;
    }
    steps += (u64)step + 1; totalIns += A.icount - ic0; totalJit += B.jitIns; done++;
    if (diff.empty()) { if (!quiet) printf("%llx: ok  %llu instructions, %llu native (%llu entries), stop %d %s%c", (unsigned long long)rva, (unsigned long long)(A.icount - ic0), (unsigned long long)B.jitIns, (unsigned long long)B.jitRuns, (int)sa, A.stopInfo.c_str(), 10); continue; }
    bad++;
    printf("%llx: DIFFERENT after step %d (%llu instructions from %llu):%s%c", (unsigned long long)rva, step, (unsigned long long)k, (unsigned long long)(A.icount - k - ic0), diff.c_str(), 10);
    // the same steps again from the last saved states, then the failing one cut in two until one instruction is left
    A.restore(*ca); B.restore(*cb); rng = crng;
    for (int s = cstep; s < step; s++) { const u64 n = next(rng); A.run(n); B.run(n); }
    auto fa = A.snapshot(), fb = B.snapshot();
    u64 lo = 0, hi = k;
    while (hi - lo > 1) {
      const u64 mid = lo + (hi - lo) / 2;
      A.restore(*fa); B.restore(*fb); A.run(mid); B.run(mid);
      if (cmp(A, B, true).empty()) lo = mid; else hi = mid;
    }
    A.restore(*fa); B.restore(*fb); A.run(lo); B.run(lo);
    const std::string was = cmp(A, B, true);
    const u64 at = A.rip; const std::string text = A.disasm(at);
    const auto showFl = [](const char* who, const Flags& f) {
      printf("   %s: lazy %x op %d w %d a %llx b %llx r %llx x %llx s %u %u %u %u | prev lazy %x op %d a %llx b %llx r %llx s %u %u %u %u | bits %llx folded %x sym", who, f.lazy, f.op, f.w,
        (unsigned long long)f.a, (unsigned long long)f.b, (unsigned long long)f.r, (unsigned long long)f.x, f.sa, f.sb, f.sr, f.sx, f.prev.lazy, f.prev.op,
        (unsigned long long)f.prev.a, (unsigned long long)f.prev.b, (unsigned long long)f.prev.r, f.prev.sa, f.prev.sb, f.prev.sr, f.prev.sx, (unsigned long long)f.bits, f.folded);
      for (int p : {0, 2, 4, 6, 7, 11}) printf(" %u", f.sym[p]);
      printf("%c", 10);
    };
    printf("   flags before:%c", 10); showFl("interpreter", A.fl); showFl("native     ", B.fl);
    const u64 j0 = B.jitIns;
    A.run(1); B.run(hi - lo);
    printf("   flags after (%llu of the instructions ran as native code):%c", (unsigned long long)(B.jitIns - j0), 10); showFl("interpreter", A.fl); showFl("native     ", B.fl);
    printf("   instruction %llu of the step, at %llx: %s%c   before it: %s%c   after it:%s%c", (unsigned long long)hi, (unsigned long long)at, text.c_str(), 10, was.empty() ? "same" : was.c_str(), 10, cmp(A, B, true).c_str(), 10);
    A.memDiff(B, stdout, 6);
    fflush(stdout);
  }
  printf("%d functions, %llu steps, %llu instructions (%llu native): %d differ%c", done, (unsigned long long)steps, (unsigned long long)totalIns, (unsigned long long)totalJit, bad, 10);
  return bad != 0;
}
