// Is a conditional jump decided by the code just before it, whatever that code reads? unshroud_opaque <pe> start:site ...
// From `start` (rva) to the jump at `site` (rva) the image runs with every register unknown (an input; the stack pointer
// a place of unknown memory) and the memory it reads unknown too (the image's writable data included; its read-only data
// and code are what they are). At the jump: "constant <side>" (no input reaches the condition), "opaque <side>" (the
// condition depends on inputs but only that side is possible: the solver proves it), "input" (both sides are possible:
// the jump depends on what came before the window), "unreached <why>" (the run did not come to the jump).
#include "../src/util.hpp"
#include "../src/engine.hpp"
#include "../src/pe.hpp"
#include "../src/solver.hpp"
#include <cstdio>
#include <cstring>
#include <string>
using namespace unshroud;

int main(int argc, char** argv) {
  unshroud::limitMemory();
  if (argc < 3) { printf("usage: unshroud_opaque <pe> start:site ...%c", 10); return 1; }
  Image img; std::shared_ptr<State> pristine;
  {
    Engine base;
    if (!loadPE(base, argv[1], img)) { printf("cannot load%c", 10); return 1; }
    for (auto& r : img.writable) base.markUnknown(r.first, r.second);
    base.markUnknown(0x7ffe0000ull, 0x1000);              // the shared user page (KUSER_SHARED_DATA): unknown too
    pristine = base.snapshot();
  }
  static const char* rn[16] = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"};
  for (int i = 2; i < argc; i++) {
    char* e; const u64 start = strtoull(argv[i], &e, 16); const u64 site = *e == ':' ? strtoull(e + 1, nullptr, 16) : 0;
    // eight runs, other first values each time: a jump decided by no input goes the same way in all of them
    int sideSeen = -1; bool constant = true, reached = true; std::string verdict, why;
    for (int k = 0; k < 8 && reached; k++) {
      Engine E; E.X.maxNodes = 2000000; E.restore(*pristine); E.lazyMem = true; E.ucSeedZone = true; E.ucAnywhere = true; E.tableMax = 256; E.cpuidSym = true;
      E.ucNext = 7919ull * k;
      for (int r = 0; r < 16; r++) { E.g[r] = E.ucFresh() + 0x1111ull * k; E.symbolizeReg(r, rn[r]); }
      for (int r = 0; r < 16; r++) { for (int b2 = 0; b2 < 32; b2++) E.v[r][b2] = (u8)(0x5b * (r + 1) + 0x3d * b2 + 0x77 * k); E.symbolizeVec(r, std::string("v") + rn[r]); }
      E.g[RSP] &= ~0xfull; E.g[RSP] += 8;
      E.symbolizeFlags("fl");
      E.gsbase = E.ucFresh(); E.fsbase = E.ucFresh();
      E.rip = img.base + start; E.stops.insert(img.base + site); E.flushBlocks();
      Stop s = E.run(400);
      if (s != ST_ADDRESS || E.rip != img.base + site) { reached = false; why = std::to_string((int)s) + " " + E.stopInfo; break; }
      E.stops.erase(img.base + site); E.flushBlocks();
      const size_t n0 = E.path.size();
      const Insn* J = E.decodeAt(img.base + site); const u64 fall = J ? J->next : 0;
      E.run(1);
      const PathConstraint* c = nullptr;
      for (size_t q = n0; q < E.path.size(); q++) if (E.path[q].pc == img.base + site && E.path[q].kind == 0) c = &E.path[q];
      const int side = E.rip != fall ? 1 : 0;
      if (!c) { if ((sideSeen >= 0 && sideSeen != side) || E.nativeCount) constant = false; sideSeen = side; if (!constant) break; continue; }
      constant = false;
      if (k == 0) {
        Solver S(E.X);
        std::vector<u64> seed(E.X.vars.size()), model; for (size_t q = 0; q < seed.size(); q++) seed[q] = E.X.vars[q].seed;
        std::vector<u32> prefix; for (size_t q = 0; q < n0; q++) if (E.path[q].kind == 0) prefix.push_back(E.path[q].cond);
        SolveOptions o; o.timeoutMs = 3000; const char* stage = "";
        const SatResult r = S.check(prefix, {E.X.not_(c->cond)}, seed, &model, o, &stage);
        verdict = std::string(r == SR_UNSAT ? "opaque " : r == SR_SAT ? "input " : "unknown ") + (c->taken != fall ? "taken" : "fall") + " (" + stage + ")";
      }
      break;
    }
    if (!reached) printf("%llx %llx unreached %s%c", (unsigned long long)site, (unsigned long long)start, why.c_str(), 10);
    else if (constant && sideSeen >= 0) printf("%llx %llx constant %s%c", (unsigned long long)site, (unsigned long long)start, sideSeen ? "taken" : "fall", 10);
    else if (!verdict.empty()) printf("%llx %llx %s%c", (unsigned long long)site, (unsigned long long)start, verdict.c_str(), 10);
    else printf("%llx %llx input (seeds disagree)%c", (unsigned long long)site, (unsigned long long)start, 10);
  }
  return 0;
}
