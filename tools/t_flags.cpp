// What this CPU does with the flags an instruction leaves "undefined": runs instructions (hex bytes) on this CPU from
// random states and prints the operands, the results and the flags, one line per trial (for py/flagfit.py).
// usage: t_flags <trials> <hex> [<hex> ...]
#include "../src/util.hpp"
#include "../src/engine.hpp"
#include <cstdio>
#include <cstring>
#include <random>
using namespace unshroud;
namespace unshroud { Stop nativeExec(Engine& E, const Insn& I); }

int main(int argc, char** argv) {
  unshroud::limitMemory();
  if (argc < 3) { printf("usage: t_flags <trials> <hex> ...%c", 10); return 1; }
  const int trials = atoi(argv[1]);
  std::mt19937_64 rng(777);
  const u64 CODE = 0x10000000ull;
  for (int k = 2; k < argc; k++) {
    std::vector<u8> b; for (const char* p = argv[k]; p[0] && p[1]; p += 2) { unsigned v; sscanf(p, "%2x", &v); b.push_back((u8)v); }
    for (int t = 0; t < trials; t++) {
      Engine N; N.map(CODE, 4096); N.writeMem(CODE, b.data(), b.size());
      const u64 special[] = {0, 1, 2, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0xffff, 0x7fffffff, 0x80000000, 0xffffffff, 0x8000000000000000ull, ~0ull, 63, 64};
      for (int r = 0; r < 16; r++) N.g[r] = (rng() % 4 == 0) ? special[rng() % 16] : (rng() % 3 == 0 ? rng() & 0xff : rng());
      if (rng() % 2) N.g[RCX] &= 0x3f;
      if (rng() % 4 == 0) N.g[RDX] = 0;
      N.g[RSP] = 0x7f0000000000ull;
      if (const char* dv = getenv("TF_DIV")) {       // operands a division accepts: 1 unsigned, 2 signed, 3 8-bit
        if (N.g[RBX] == 0 || (N.g[RBX] & 0xff) == 0) N.g[RBX] |= 0x101;
        if (*dv == '1') N.g[RDX] = 0;
        else if (*dv == '2') { N.g[RAX] &= 0x3fffffff; N.g[RDX] = 0; if ((N.g[RBX] & 0xffffffff) == 0xffffffff) N.g[RBX] = 3; }
        else N.g[RAX] &= 0x7f;
      }
      const u64 fin = rng() & (FL_CF | FL_PF | FL_AF | FL_ZF | FL_SF | FL_OF);
      N.fl = Flags{}; N.fl.bits = fin | 0x202; N.fl.lazy = 0; N.rip = CODE;
      const Insn* I = N.decodeAt(CODE); if (!I) break;
      Insn ins = *I; u64 g0[16]; memcpy(g0, N.g, sizeof g0);
      if (nativeExec(N, ins) != ST_NONE) continue;
      printf("%s %llx %llx %llx %llx %llx %llx %llx %llx %llx%c", argv[k], (unsigned long long)g0[RAX], (unsigned long long)g0[RBX], (unsigned long long)g0[RCX], (unsigned long long)g0[RDX],
             (unsigned long long)N.g[RAX], (unsigned long long)N.g[RBX], (unsigned long long)N.g[RDX], (unsigned long long)fin, (unsigned long long)(N.rflags() & 0x8d5), 10);
    }
  }
  return 0;
}
