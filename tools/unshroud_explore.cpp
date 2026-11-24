// Explores functions of a PE image: unshroud_explore <pe> [--time S] [--max N] [--seed V] rva:nargs ...
// One JSON line per function: paths (inputs, stop, rax), refuted / undecided branch sides, statistics. With --py, each
// path also gets "py": Python source of f(x, y, z, w) -> [rax, path condition...] (helpers: unshroud/py/unshroudpy.py).
// Options: --paths (every path, not every edge), --no-addr, --no-simplify, --smt-timeout MS, --confirm MS (time to prove a side
// impossible when tests say so), --verify MS (solver check of simplified outputs; 0: off),
// --spin N (a run stops after N decisions of one instruction; 0: never), --loop N (an endless loop is looked for after N
// instructions with nothing new; 0: never), --tables N (loads from a constant table of at most N entries are one
// expression; 0: the address is fixed and its values enumerated), --free-regs (every register which is not an argument is
// an unknown too: what mutated code reads from its caller), --lazy (operations recorded, built when read).
// Unknown memory is the default (--uc; --no-uc: the arguments are plain numbers and memory nobody mapped reads as zero):
// what the arguments point to and the image's writable data are inputs when read (--no-globals: the arguments only).
// It sets --spin 200 and --havoc unless given otherwise. --havoc / --no-havoc: once the function is
// explored as it is, the calls its paths ended in (a throw, an abort, a fault, an endless loop below the function) are
// left out: such a call returns an input, what it was given to fill in the caller's frame is unknown, and the paths
// after it are marked "assumed" (JSON "left_out": the call sites; "cov_plain": what ran without that assumption).
// --runs N: at most N runs per function; --cover: JSON "cov", every conditional jump executed with its side.
// The image runs in a Windows process (src/win.hpp: TEB / PEB, loader lists, system DLLs, API models, exception dispatch)
// unless --no-env (UNSHROUD_ENV=0): then imports return 0 and a path ends at an exception. --init runs the image's entry point
// (DLL_PROCESS_ATTACH) once before the functions (--init-any: its state is kept even when it ended the process); --no-exc: no exception dispatch; --null N: an access below 0x10000 never
// faults (0, --no-null), is an access violation when a handler is there to take it (1), or both are explored (2, default);
// --decide-sizes: allocation sizes which depend on the inputs are decisions of the path (too big: the allocation fails).
// --relax N: visits of a side which is impossible after its path but possible by itself tried again with a relaxed prefix
// (default 2; 0: as round 2, such sides are listed as refuted). JSON "refuted": sides impossible whatever came before;
// "blocked": impossible after the paths which came to them only.
// JSON per path: "out_exact" (every replacement behind the simplified output is proved), "out_check" with UNSHROUD_CHECK_OUT=MS.
#include "../src/util.hpp"
#include "../src/explore.hpp"
#include "../src/mba.hpp"
#include "../src/pe.hpp"
#include "../src/win.hpp"
#include "../src/jit.hpp"
#include "../src/ctx.hpp"
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <string>
using namespace unshroud;

static std::string hex(u64 v) { char b[24]; snprintf(b, sizeof b, "\"0x%llx\"", (unsigned long long)v); return b; }
static std::string esc(const std::string& s) {
  std::string o;
  for (char c : s) { if (c == '"' || c == 92) { o += (char)92; o += c; } else if (c == '\n') { o += (char)92; o += 'n'; } else o += c; }
  return o;
}

int main(int argc, char** argv) {
  unshroud::limitMemory();
  if (argc < 3) { printf("usage: unshroud_explore <pe> [--time S] [--max N] [--py] [--no-addr] rva:nargs ...\n"); return 1; }
  std::string pe = argv[1]; ExploreConfig cfg; bool py = false, simplify = true; u64 seedv = 0;
  int verifyMs = -1;
  bool freeRegs = false;            // every other register is an unknown too (what the caller left there), not a fixed value
  bool cover = getenv("UNSHROUD_COVER") != nullptr;   // --cover: every conditional jump executed in the image, with its side (JSON "cov")
  bool uc = true;                   // unknown memory: what the arguments point to is input too (the default; --no-uc / UNSHROUD_UC=0: arguments are plain numbers)
  bool spinSet = false, havocSet = false;
  if (const char* e = getenv("UNSHROUD_UC")) uc = *e && *e != 48;
  bool ucGlobals = true;            // ... and the writable data of the image (--no-globals: only what the arguments reach)
  if (const char* e = getenv("UNSHROUD_FREE_REGS")) freeRegs = *e && *e != 48;
  std::vector<std::pair<u64, int>> funcs;
  if (const char* e = getenv("UNSHROUD_LAZY")) cfg.lazy = *e && *e != 48;
  bool useEnv = true, init = false, initAny = false, exc = true, decide = false; int nullFaults = 2; u64 initMax = 200000000;
  if (const char* e = getenv("UNSHROUD_ENV")) useEnv = *e && *e != 48;
  if (const char* e = getenv("UNSHROUD_INIT")) init = *e && *e != 48;
  if (const char* e = getenv("UNSHROUD_API_DECIDE")) decide = *e && *e != 48;
  if (const char* e = getenv("UNSHROUD_FORCE")) cfg.force = atoi(e);                  // forced branches (explore.hpp)
  int envSym = 0; if (const char* e = getenv("UNSHROUD_ENVSYM")) envSym = atoi(e);      // what the environment answers is an input (win.hpp)
  bool places = false; if (const char* e = getenv("UNSHROUD_PLACES")) places = *e && *e != 48;   // globals made pointers point to memory of their own (engine.hpp)
  for (int i = 2; i < argc; i++) {
    if (!strcmp(argv[i], "--time")) cfg.timeLimit = atof(argv[++i]);
    else if (!strcmp(argv[i], "--max")) cfg.maxIns = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--py")) py = true;
    else if (!strcmp(argv[i], "--no-simplify")) simplify = false;
    else if (!strcmp(argv[i], "--no-addr")) cfg.addresses = false;
    else if (!strcmp(argv[i], "--paths")) cfg.pathMode = true;
    else if (!strcmp(argv[i], "--runs")) cfg.maxRuns = (u32)strtoul(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--havoc")) { cfg.havoc = true; havocSet = true; }
    else if (!strcmp(argv[i], "--no-havoc")) { cfg.havoc = false; havocSet = true; }
    else if (!strcmp(argv[i], "--force")) cfg.force = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--spin")) { cfg.spinLimit = (u32)strtoul(argv[++i], nullptr, 0); spinSet = true; }
    else if (!strcmp(argv[i], "--confirm")) cfg.confirmMs = (u32)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--tables")) cfg.tableMax = (u32)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--attempts")) cfg.attempts = (u32)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--relax")) cfg.relax = (u32)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--slice")) cfg.slice = atof(argv[++i]);
    else if (!strcmp(argv[i], "--free-regs")) freeRegs = true;
    else if (!strcmp(argv[i], "--run-pages")) cfg.runPages = (u32)strtoul(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--uc")) uc = true;
    else if (!strcmp(argv[i], "--cover")) cover = true;
    else if (!strcmp(argv[i], "--no-uc")) uc = false;
    else if (!strcmp(argv[i], "--no-globals")) ucGlobals = false;
    else if (!strcmp(argv[i], "--loop")) cfg.loopLimit = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--no-lazy")) cfg.lazy = false;
    else if (!strcmp(argv[i], "--verify")) verifyMs = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--lazy")) cfg.lazy = true;
    else if (!strcmp(argv[i], "--smt-timeout")) cfg.solve.timeoutMs = (u32)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--no-ls")) cfg.solve.localSearch = false;
    else if (!strcmp(argv[i], "--no-mod")) cfg.solve.modular = false;
    else if (!strcmp(argv[i], "--seed")) seedv = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--no-env")) useEnv = false;
    else if (!strcmp(argv[i], "--env")) useEnv = true;
    else if (!strcmp(argv[i], "--init")) init = true;
    else if (!strcmp(argv[i], "--no-init")) init = false;
    else if (!strcmp(argv[i], "--init-any")) init = initAny = true;
    else if (!strcmp(argv[i], "--init-max")) initMax = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--no-exc")) exc = false;
    else if (!strcmp(argv[i], "--no-null")) nullFaults = 0;
    else if (!strcmp(argv[i], "--null")) nullFaults = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--decide-sizes")) decide = true;
    else if (!strcmp(argv[i], "--no-decide-sizes")) decide = false;
    else { char* e; u64 rva = strtoull(argv[i], &e, 16); int n = *e == ':' ? atoi(e + 1) : 4; funcs.push_back({rva, n}); }
  }
  // unknown memory: decisions repeat on unknown data (200 of one instruction say as much as 20000, in a tenth of the
  // time), and the calls a path ended in are left out once the function is explored as it is
  if (uc) { if (!spinSet) cfg.spinLimit = 200; if (!havocSet) cfg.havoc = true; }
  // UNSHROUD_CTX=contexts.jsonl (tools/unshroud_ctx.cpp), UNSHROUD_CTX_BASE=the module's base in the recorded process, UNSHROUD_CTX_MODS=the
  // run's .modules file: a function with a recorded context starts from it (its registers and the memory it read are
  // the inputs' first values; addresses in the recorded modules and stack are moved to where this engine has them)
  std::unordered_map<u64, RealCtx> ctxs; u64 ctxBase = 0; std::map<std::string, std::pair<u64, u64>> ctxMods;
  if (const char* cf = getenv("UNSHROUD_CTX")) loadContexts(cf, ctxs);
  if (const char* cb = getenv("UNSHROUD_CTX_BASE")) ctxBase = strtoull(cb, nullptr, 16);
  if (const char* cm = getenv("UNSHROUD_CTX_MODS")) ctxMods = loadModuleList(cm);
  // UNSHROUD_DEAD=file: jump sides proved impossible by their own code (lines "rva side kind", py/deadsides.py)
  std::vector<std::pair<u64, int>> deadRva;
  if (const char* df = getenv("UNSHROUD_DEAD")) if (FILE* f = fopen(df, "r")) { char ln[128]; while (fgets(ln, sizeof ln, f)) { char* e2; const u64 r = strtoull(ln, &e2, 16); const int sd = atoi(e2); if (r) deadRva.push_back({r, sd}); } fclose(f); }
  // UNSHROUD_SWITCH=file: jump tables (lines "rva target target ...", py/switches.py), forced with --force 2
  std::vector<std::vector<u64>> switchRva;
  if (const char* sf = getenv("UNSHROUD_SWITCH")) if (FILE* f = fopen(sf, "r")) { char ln[8192]; while (fgets(ln, sizeof ln, f)) { std::vector<u64> v; char* p = ln; for (;;) { char* e2; const u64 x = strtoull(p, &e2, 16); if (e2 == p) break; v.push_back(x); p = e2; } if (v.size() >= 2) switchRva.push_back(v); } fclose(f); }
  // the image is mapped once: every function starts from these pages (shared, copied on write)
  Image img;
  std::shared_ptr<State> pristine;
  std::unique_ptr<WinEnv> env;
  {
    Engine base;
    if (!loadPE(base, pe, img)) { printf("{\"error\": \"cannot load\"}\n"); return 1; }
    if (useEnv) {
      env.reset(new WinEnv); env->retAddr = cfg.retAddr; env->exceptions = exc; env->nullFaults = nullFaults; env->decideSizes = decide; env->envSym = envSym;
      if (!env->build(base, img, pe)) { fprintf(stderr, "unshroud: the system DLLs cannot be read, no process environment\n"); env.reset(); }
    }
    if (env && init) {
      env->attach(base);
      auto before = base.snapshot(); std::string info;
      if (!env->runInit(base, initMax, &info)) {
        fprintf(stderr, "unshroud: the entry point did not return (%s): functions start from %s\n", info.c_str(), initAny ? "the state it left" : "the image as mapped");
        if (initAny) env->afterInit(base); else base.restore(*before);
      }
      env->calls.clear(); env->unmodeled.clear(); env->errors.clear();
    }
    if (uc && ucGlobals) for (auto& r : img.writable) base.markUnknown(r.first, r.second);
    if (env && uc && (envSym & 4)) { base.markUnknown(WinEnv::PEB, 8); base.markUnknown(WinEnv::PEB + 0xB8, 8); base.markUnknown(WinEnv::KUSER + 0x2d0, 8); }   // BeingDebugged, NtGlobalFlag, KdDebuggerEnabled
    pristine = base.snapshot();
  }
  for (auto [rva, nargs] : funcs) {
   try {
    auto t0 = std::chrono::steady_clock::now();
    Engine E;
    E.X.maxNodes = 25000000;
    E.profile = getenv("UNSHROUD_PROFILE") != nullptr;
    E.covOn = cover; E.hotOn = getenv("UNSHROUD_HOT") != nullptr; E.placesOn = places; E.cpuidSym = (envSym & 8) != 0;   // (bit 8: cpuid answers too)
    E.restore(*pristine);
    const u64 rsp = env ? WinEnv::RSP0 : 0x7f0000000000ull - 0x1000;
    if (env) { env->attach(E); env->calls.clear(); env->unmodeled.clear(); env->errors.clear(); }
    // a recorded context: the memory the function read (moved where this engine has the modules and the stack)
    const RealCtx* rc = nullptr; Reloc RL;
    if (ctxBase) { auto ci = ctxs.find(rva); if (ci != ctxs.end()) rc = &ci->second; }
    if (rc) {
      RL.add(ctxBase, img.size, img.base);
      if (env) for (auto& kv : ctxMods) { WinModule* m = env->find(kv.first); if (m && !m->sample) RL.add(kv.second.first, kv.second.second, m->base); }
      RL.add(rc->rsp - 0x100000, 0x200000, rsp - 0x100000);
      for (auto& mm : rc->mem) {
        const u64 a = RL(mm.first);
        if (env) { WinModule* m = env->moduleAt(a); if (m && !m->sample) continue; }   // (the system DLLs: this engine's own copies)
        std::vector<u8> b = mm.second;
        for (size_t k = (8 - (a & 7)) & 7; k + 8 <= b.size(); k += 8) { u64 w; memcpy(&w, &b[k], 8); if (RL.inside(w)) { w = RL(w); memcpy(&b[k], &w, 8); } }
        E.writeMem(a, b.data(), b.size());
        if (uc) E.markUnknown(a, b.size());
      }
    }
    E.writeMem(rsp, &cfg.retAddr, 8);
    E.g[RSP] = rsp; E.g[RBP] = rsp;
    const int regs[4] = {RCX, RDX, R8, R9}; const char* names[4] = {"x", "y", "z", "w"};
    std::vector<Input> inputs;
    for (int k = 0; k < nargs; k++) {
      // (without unknown memory: addresses a user program can have, of nothing - what is read there is zero)
      static const char* an[4] = {"rcx", "rdx", "r8", "r9"};
      E.g[regs[k]] = rc && rc->regs.count(an[k]) ? RL(rc->regs.at(an[k])) : seedv ? seedv * (k + 1) : uc ? E.ucFresh() : 0x0000111111111111ull * (k + 1);
      u32 v = E.symbolizeReg(regs[k], names[k]);
      inputs.push_back({(u32)E.X.N(v).k, 0, (u8)regs[k], 8, 0});
    }
    if (freeRegs) {
      static const char* gn[16] = {"g_rax", "g_rcx", "g_rdx", "g_rbx", "g_rsp", "g_rbp", "g_rsi", "g_rdi", "g_r8", "g_r9", "g_r10", "g_r11", "g_r12", "g_r13", "g_r14", "g_r15"};
      for (int r = 0; r < 16; r++) {
        if (r == RSP || E.gs[r]) continue;
        u32 v = E.symbolizeReg(r, gn[r]);
        inputs.push_back({(u32)E.X.N(v).k, 0, (u8)r, 8, 0});
      }
    }
    if (uc) {
      // the arguments on the stack are inputs too (the fifth to the eighth)
      E.lazyMem = true;
      for (int k = 0; k < 4; k++) {
        const u64 a = rsp + 0x28 + 8 * k; u64 sv = E.ucFresh();
        if (rc) E.readMem(a, &sv, 8);                    // (what the recorded caller left there)
        E.writeMem(a, &sv, 8);
        u32 v = E.symbolizeMem(a, 8, "a" + std::to_string(5 + k));
        inputs.push_back({(u32)E.X.N(v).k, 1, 0, 8, a});
      }
    }
    if (rc) {                                           // the other registers as they were
      static const char* gn3[16] = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"};
      for (int r = 0; r < 16; r++) { if (r == RSP || E.gs[r]) continue; auto it = rc->regs.find(gn3[r]); if (it != rc->regs.end()) E.g[r] = RL(it->second); }
    }
    E.rip = img.base + rva;
    if (!env) for (auto& kv : img.stubs) E.hooks[kv.first] = [](Engine& e) -> Stop { e.g[RAX] = 0; e.gs[RAX] = 0; u64 r; e.readMem(e.g[RSP], &r, 8); e.g[RSP] += 8; e.rip = r; return ST_NONE; };
    cfg.addressRanges = {{img.base, img.base + img.size}};
    if (cfg.dead.empty()) for (auto& d : deadRva) cfg.dead.insert(((img.base + d.first) << 1) | (u64)d.second);
    cfg.fnStart = cfg.fnEnd = 0;
    for (auto& f : img.funcs) if (rva >= f.first && rva < f.first + f.second) { cfg.fnStart = img.base + f.first; cfg.fnEnd = img.base + f.first + f.second; }
    if (cfg.force >= 2) for (auto& sw : switchRva) if (!cfg.fnEnd || (img.base + sw[0] >= cfg.fnStart && img.base + sw[0] < cfg.fnEnd)) { auto& tv = E.switchTargets[img.base + sw[0]]; for (size_t k = 1; k < sw.size(); k++) tv.push_back(img.base + sw[k]); }
    auto start = E.snapshot();
    Explorer ex(E, start, inputs, cfg);
    ex.run();
    if (getenv("UNSHROUD_TRACEPATH")) {
      // the first path's constraints: kind, pc, value, expression
      E.restore(*start); E.path.clear(); E.spinReset(); E.run(cfg.maxIns);
      for (auto& c : E.path) fprintf(stderr, "kind %d pc %llx taken %llx narrow %d expr %s cond %s\n", c.kind, (unsigned long long)c.pc, (unsigned long long)c.taken,
        c.expr ? (int)(E.X.range(c.expr).hi - E.X.range(c.expr).lo < 0x10000) : -1, c.expr ? E.X.str(c.expr, 5).c_str() : "-", E.X.str(c.cond, 5).c_str());
    }
    if (E.profile && !E.symHist.empty()) {            // UNSHROUD_PROFILE: which instructions the expressions cost
      std::vector<std::pair<u64, int>> v; u64 tot = 0;
      for (size_t i = 0; i < E.symHist.size(); i++) if (E.symHist[i].n) { v.push_back({E.symHist[i].cyc, (int)i}); tot += E.symHist[i].cyc; }
      std::sort(v.rbegin(), v.rend());
      fprintf(stderr, "symbolic instructions of %llx by mnemonic (share of their cycles; count; lookups, nodes made and cycles per instruction):%c", (unsigned long long)rva, 10);
      for (size_t i = 0; i < v.size() && i < 14; i++) { const auto& h = E.symHist[v[i].second];
        fprintf(stderr, "   %5.1f%%  %-10s %9llu  %5.2f  %5.2f  %6.0f%c", 100.0 * h.cyc / std::max<u64>(1, tot), Engine::mnemonicName(v[i].second), (unsigned long long)h.n, (double)h.lookups / h.n, (double)h.nodes / h.n, (double)h.cyc / h.n, 10); }
    }
    if (E.hotOn) {
      std::vector<std::pair<u64, u64>> hv; u64 tot = 0; for (auto& kv : E.hot) { hv.push_back({kv.second, kv.first}); tot += kv.second; }
      std::sort(hv.rbegin(), hv.rend());
      std::map<u64, u64> byMod; for (auto& h : hv) byMod[h.second >> 28] += h.first;
      fprintf(stderr, "hot %llx: %llu instructions;", (unsigned long long)rva, (unsigned long long)tot);
      for (auto& m : byMod) if (m.second * 50 > tot) fprintf(stderr, " %llx: %.0f%%", (unsigned long long)(m.first << 28), 100.0 * m.second / tot);
      fprintf(stderr, "%c", 10);
      {   // how the instructions spread over the blocks: blocks run at all, and how many of them make half / 90% of the count
        u64 acc = 0; size_t n50 = 0, n90 = 0;
        for (size_t i = 0; i < hv.size(); i++) { acc += hv[i].first; if (!n50 && acc * 2 >= tot) n50 = i + 1; if (!n90 && acc * 10 >= tot * 9) { n90 = i + 1; break; } }
        fprintf(stderr, "   blocks run %zu (decoded %llu): %zu of them make 50%% of the instructions, %zu make 90%%%c", hv.size(), (unsigned long long)E.blocksDecoded, n50, n90, 10);
      }
      for (size_t i = 0; i < hv.size() && i < 12; i++) fprintf(stderr, "   %5.1f%%  %llx  %s%c", 100.0 * hv[i].first / tot, (unsigned long long)hv[i].second, env ? env->apiName(hv[i].second).c_str() : "", 10);
    }
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    // the outputs, simplified: MBA, then conditions which cannot change, then MBA again
    auto ts = std::chrono::steady_clock::now();
    Mba M(E.X, &ex.S);
    std::vector<u32> outs; std::vector<bool> outExact;
    M.o.budget = std::max(0.2, cfg.timeLimit * 0.2 / std::max<size_t>(1, ex.paths.size()));
    if (verifyMs >= 0) M.o.verifyMs = (u32)verifyMs;
    for (auto& p : ex.paths) {
      u32 r = p.rax.s;
      bool exact = true;
      if (r && simplify && E.X.countNodes(r) <= 20000) { r = M.simplify(r); exact = M.lastExact; r = M.foldConditions(r, ex.S); r = M.simplify(r); exact = exact && M.lastExact; }
      outs.push_back(r); outExact.push_back(exact);
    }
    // independent check of each simplified output (UNSHROUD_CHECK_OUT=ms): Bitwuzla on (path conditions, out != rax)
    std::vector<int> outCheck(ex.paths.size(), -1);
    if (const char* ce = getenv("UNSHROUD_CHECK_OUT")) {
      const u32 cms = (u32)atoi(ce);
      for (size_t i = 0; i < ex.paths.size(); i++) {
        const PathInfo& p = ex.paths[i];
        if (!p.rax.s || !outs[i] || outs[i] == p.rax.s) { outCheck[i] = 3; continue; }
        std::vector<u32> q(p.all.begin(), p.all.end()); q.push_back(E.X.ne(outs[i], p.rax.s));
        const SatResult cr = ex.S.smt(q, nullptr, cms);
        outCheck[i] = cr == SR_UNSAT ? 1 : cr == SR_SAT ? 2 : 0;
      }
    }
    double dsimp = std::chrono::duration<double>(std::chrono::steady_clock::now() - ts).count();
    if (getenv("UNSHROUD_MBA_STATS")) {
      fprintf(stderr, "solver %llx: queries %llu  simplify %.3fs  local %.3fs  modular %.3fs  smt %.3fs  proofs %llu (proved %llu) %.3fs  likely-unsat %llu  bad models %llu\n", (unsigned long long)rva,
        (unsigned long long)ex.S.stats.queries, ex.S.stats.tSimp, ex.S.stats.tLs, ex.S.stats.tMod, ex.S.stats.tSmt, (unsigned long long)ex.S.proofs, (unsigned long long)ex.S.proved, ex.S.tProof,
        (unsigned long long)ex.S.stats.likelyUnsat, (unsigned long long)ex.S.stats.badModels);
      fprintf(stderr, "  smt: sat %llu unsat %llu; kept solver %llu checks (%llu past its share, %llu restarts); cores %llu, queries answered by a core %llu, by opposite constraints %llu%c",
        (unsigned long long)ex.S.stats.smtSat, (unsigned long long)ex.S.stats.smtUnsat, (unsigned long long)ex.S.stats.keptCalls, (unsigned long long)ex.S.stats.keptOver, (unsigned long long)ex.S.stats.keptResets,
        (unsigned long long)ex.S.stats.cores, (unsigned long long)ex.S.stats.coreUnsat, (unsigned long long)ex.S.stats.opposite, 10);
      if (ex.S.mba) fprintf(stderr, "  solver mba: nodes %llu pair %llu table %llu cmp %llu/%llu top %.3fs pair %.3fs | exact: nodes %llu pair %llu cmp %llu/%llu top %.3fs pair %.3fs\n",
        (unsigned long long)ex.S.mba->st.nodes, (unsigned long long)ex.S.mba->st.pair, (unsigned long long)ex.S.mba->st.table, (unsigned long long)ex.S.mba->st.cmpProved, (unsigned long long)ex.S.mba->st.cmpTried, ex.S.mba->st.tTop, ex.S.mba->st.tPair,
        (unsigned long long)ex.S.mbaExact->st.nodes, (unsigned long long)ex.S.mbaExact->st.pair, (unsigned long long)ex.S.mbaExact->st.cmpProved, (unsigned long long)ex.S.mbaExact->st.cmpTried, ex.S.mbaExact->st.tTop, ex.S.mbaExact->st.tPair);
    }
    if (getenv("UNSHROUD_MBA_STATS")) fprintf(stderr, "mba %llx: %.4fs nodes %llu const %llu known %llu table %llu pair %llu linear %llu boolean %llu split %llu rejected %llu notfree %llu verified %llu refuted %llu unverified %llu poly %llu/%llu | top %.4fs pair %.4fs split %.4fs check %.4fs poly %.4fs\n", (unsigned long long)rva, dsimp,
      (unsigned long long)M.st.nodes, (unsigned long long)M.st.constant, (unsigned long long)M.st.known, (unsigned long long)M.st.table, (unsigned long long)M.st.pair, (unsigned long long)M.st.linear,
      (unsigned long long)M.st.boolean, (unsigned long long)M.st.splits, (unsigned long long)M.st.rejected, (unsigned long long)M.st.notFree, (unsigned long long)M.st.verified, (unsigned long long)M.st.refuted, (unsigned long long)M.st.unverified, (unsigned long long)M.st.polyProved, (unsigned long long)M.st.polyTried, M.st.tTop, M.st.tPair, M.st.tSplit, M.st.tCheck, M.st.tPoly);
    std::string out = "{\"rva\": " + hex(rva) + ", \"nargs\": " + std::to_string(nargs) + ", \"time\": " + std::to_string(dt);
    out += std::string(", \"env\": ") + (env ? "true" : "false");
    if (cfg.havoc) out += ", \"havoc_sites\": " + std::to_string(ex.st.havocSites) + ", \"assumed_paths\": " + std::to_string(std::count_if(ex.paths.begin(), ex.paths.end(), [](const PathInfo& p2) { return p2.assumed != 0; }));
    if (cfg.havoc) { out += ", \"left_out\": ["; std::vector<u64> hs(E.havocSites.begin(), E.havocSites.end()); std::sort(hs.begin(), hs.end()); for (size_t i = 0; i < hs.size(); i++) out += (i ? ", " : "") + hex(hs[i]); out += "]"; }
    if (E.dropMarks) out += ", \"marks_dropped\": true";         // so many constants made from inputs that they are plain values now (Engine::markLimit)
    if (ex.S.stats.tooBig) out += ", \"smt_too_big\": " + std::to_string(ex.S.stats.tooBig);   // queries too big to give to the SMT solver (Solver::smt)
    if (E.codeFlushes) out += ", \"code_writes\": " + std::to_string(E.codeFlushes);      // stores into decoded instructions (each one drops what was decoded)
    if (uc) out += ", \"uc_vars\": " + std::to_string(E.ucVars.size()) + ", \"uc_calls\": " + std::to_string(E.ucCalls) + ", \"pin_skips\": " + std::to_string(E.pinSkips);
    if (env) {
      auto top = [&](const std::map<std::string, u64>& m) {
        std::vector<std::pair<u64, std::string>> v; for (auto& kv : m) v.push_back({kv.second, kv.first});
        std::sort(v.rbegin(), v.rend()); std::string s = "{";
        for (size_t i = 0; i < v.size() && i < 12; i++) s += (i ? ", \"" : "\"") + esc(v[i].second) + "\": " + std::to_string(v[i].first);
        return s + "}";
      };
      out += ", \"api\": " + top(env->calls) + ", \"unmodeled\": " + top(env->unmodeled) + ", \"model_errors\": " + top(env->errors);
    }
    out += ", \"runs\": " + std::to_string(ex.st.runs) + ", \"ins\": " + std::to_string(ex.st.ins) + ", \"queries\": " + std::to_string(ex.st.queries);
    out += ", \"sat\": " + std::to_string(ex.st.sat) + ", \"unsat\": " + std::to_string(ex.st.unsat) + ", \"unknown\": " + std::to_string(ex.st.unknown);
    out += ", \"prefix_ins\": " + std::to_string(ex.st.prefixIns) + ", \"sym_ins\": " + std::to_string(ex.st.symIns) + ", \"cyc_sym\": " + std::to_string(E.cycSym) + ", \"cyc_con\": " + std::to_string(E.cycCon);
    out += ", \"jit_ins\": " + std::to_string(E.jitIns) + ", \"jit_runs\": " + std::to_string(E.jitRuns);
    if (E.jit && getenv("UNSHROUD_JIT_STATS")) {
      const JitStats& js = jitStats(E.jit);
      fprintf(stderr, "jit %llx: %llu fragments (%llu instructions, %llu bytes, %.4fs, refused %llu, flushes %llu, put off %llu); entered %llu times, %llu instructions; helper %llu (pages %llu, left %llu); exits link %llu interp %llu indirect %llu%c",
        (unsigned long long)rva, (unsigned long long)js.fragments, (unsigned long long)js.insCompiled, (unsigned long long)js.codeBytes, js.tCompile, (unsigned long long)js.refused, (unsigned long long)js.flushes, (unsigned long long)js.deferred,
        (unsigned long long)js.runs, (unsigned long long)js.ins, (unsigned long long)js.helper, (unsigned long long)js.fills, (unsigned long long)js.bails,
        (unsigned long long)js.exits[1], (unsigned long long)js.exits[2], (unsigned long long)js.exits[3], 10);
    }
    if (cfg.force) out += ", \"force_sites\": " + std::to_string(ex.st.forceSites) + ", \"forced_paths\": " + std::to_string(std::count_if(ex.paths.begin(), ex.paths.end(), [](const PathInfo& p2) { return p2.forced != 0; }));
    if (places || envSym) out += ", \"place_repairs\": " + std::to_string(ex.S.placeRepairs) + ", \"env_vars\": " + std::to_string(E.envRets.size());
    out += ", \"t_relax\": " + std::to_string(ex.st.tRelax) + ", \"relaxed\": " + std::to_string(ex.st.relaxed);
    out += ", \"t_run\": " + std::to_string(ex.st.tRun) + ", \"t_solve\": " + std::to_string(ex.st.tSolve) + ", \"nodes\": " + std::to_string(E.X.n.size()) + ", \"t_simplify\": " + std::to_string(dsimp);
    out += ", \"stages\": {"; bool first = true;
    for (auto& kv : ex.st.stages) { out += (first ? "\"" : ", \"") + kv.first + "\": " + std::to_string(kv.second); first = false; }
    out += "}, \"edges\": " + std::to_string(std::count_if(ex.edges.begin(), ex.edges.end(), [](const std::pair<u64, u64>& e2) { return e2.second >= 0x10000; })) + ", \"symsites\": " + std::to_string([&] { std::set<u64> k; for (auto& e : ex.edges) if (e.second >= 0x10000) k.insert(e.first); return k.size(); }()) + ", \"npaths\": " + std::to_string(ex.paths.size());
    out += ", \"edge_list\": ["; { bool f1 = true; for (auto& e2 : ex.edges) { if (e2.second < 0x10000) continue; out += (f1 ? "[" : ", [") + hex(e2.first) + ", " + hex(e2.second) + "]"; f1 = false; } } out += "]";
    out += ", \"refuted\": [";
    first = true; for (auto& kv : ex.refuted) { out += (first ? "[" : ", [") + hex(kv.first.first) + ", " + hex(kv.first.second) + "]"; first = false; }
    out += "], \"blocked\": [";
    first = true; for (auto& kv : ex.blocked) { out += (first ? "[" : ", [") + hex(kv.first) + ", " + hex(kv.second) + "]"; first = false; }
    out += "], \"undecided\": [";
    first = true; for (auto& kv : ex.undecided) { out += (first ? "[" : ", [") + hex(kv.first) + ", " + hex(kv.second) + "]"; first = false; }
    out += "], \"likely\": [";
    first = true; for (auto& kv : ex.likely) { out += (first ? "[" : ", [") + hex(kv.first) + ", " + hex(kv.second) + "]"; first = false; }
    if (cover) {
      out += "], \"cov\": ["; bool f2 = true; char cb[40];
      for (u64 k : E.cov) { const u64 pc = k >> 1; if (pc < img.base || pc >= img.base + img.size) continue; snprintf(cb, sizeof cb, "%s%llu", f2 ? "" : ",", (unsigned long long)(((pc - img.base) << 1) | (k & 1))); out += cb; f2 = false; }
      if (cfg.havoc) {             // the part of it which rests on no call left out
        out += "], \"cov_plain\": ["; f2 = true;
        for (u64 k : E.covPlain) { const u64 pc = k >> 1; if (pc < img.base || pc >= img.base + img.size) continue; snprintf(cb, sizeof cb, "%s%llu", f2 ? "" : ",", (unsigned long long)(((pc - img.base) << 1) | (k & 1))); out += cb; f2 = false; }
      }
    }
    out += "], \"paths\": [";
    for (size_t i = 0; i < ex.paths.size(); i++) {
      const PathInfo& p = ex.paths[i];
      out += i ? ", {" : "{";
      out += "\"inputs\": ["; for (int k = 0; k < nargs; k++) out += (k ? ", " : "") + hex(p.inputs[inputs[k].var]);
      const char* sn[] = {"none", "max", "address", "return", "fault", "unsupported", "exception", "hook", "syscall", "halt"};
      bool ret = p.stop == ST_ADDRESS && p.pc == cfg.retAddr;
      out += "], \"stop\": \"" + std::string(ret ? "return" : sn[p.stop]) + "\", \"info\": \"" + esc(p.info) + "\", \"pc\": " + hex(p.pc) + ", \"ins\": " + std::to_string(p.ins);
      if (p.assumed) out += ", \"assumed\": " + std::to_string(p.assumed);
      if (p.forced) out += ", \"forced\": " + std::to_string(p.forced);
      out += ", \"rax\": " + hex(p.rax.c) + ", \"rax_sym\": " + std::string(p.rax.s ? "true" : "false");
      out += ", \"rax_nodes\": " + std::to_string(p.rax.s ? E.X.countNodes(p.rax.s) : 0) + ", \"conds\": " + std::to_string(p.branch.size());
      out += ", \"rax_str\": \"" + esc(p.rax.s ? E.X.str(p.rax.s, 14) : "") + "\"";
      out += ", \"out_exact\": " + std::string(outExact[i] ? "true" : "false");
      if (outCheck[i] >= 0) out += ", \"out_check\": \"" + std::string(outCheck[i] == 1 ? "proved" : outCheck[i] == 2 ? "cex" : outCheck[i] == 3 ? "same" : "unknown") + "\"";
      out += ", \"out_nodes\": " + std::to_string(outs[i] ? E.X.countNodes(outs[i]) : 0) + ", \"out_str\": \"" + esc(outs[i] ? E.X.str(outs[i], 14) : "") + "\"";
      if (py) { std::vector<u32> roots{outs[i] ? outs[i] : E.X.cst(p.rax.c, 64)}; for (u32 c : p.all) roots.push_back(c); out += ", \"py\": \"" + esc(E.X.py(roots, "f", &p.inputs)) + "\""; }
      out += "}";
    }
    out += "]}";
    printf("%s\n", out.c_str());
    fflush(stdout);
   } catch (const std::bad_alloc&) {
    printf("{\"rva\": \"0x%llx\", \"error\": \"out of memory\", \"paths\": []}\n", (unsigned long long)rva); fflush(stdout);
   }
  }
  return 0;
}
