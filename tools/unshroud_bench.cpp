// Instructions per second on small loops : concrete, then with symbolic inputs.
#include "../src/util.hpp"
#include "../src/engine.hpp"
#include <chrono>
#include <cstdio>
#include <cstring>
using namespace unshroud;

static std::vector<u8> hexs(const char* s) { std::vector<u8> b; for (const char* p = s; *p;) { if (*p == ' ') { p++; continue; } unsigned v; sscanf(p, "%2x", &v); b.push_back((u8)v); p += 2; } return b; }

int main(int argc, char** argv) {
  unshroud::limitMemory();
  u64 n = argc > 1 ? strtoull(argv[1], nullptr, 0) : 20000000;
  const char* only = argc > 2 ? argv[2] : nullptr;
  struct L { const char* name; const char* code; } loops[] = {
    {"mov r,r", "4889c8 4889d3 4c89c6 4d89ca 4889f7"},
    {"xor/add r,r", "4831d8 4801c8 4c31c2 4c01ce 4829c7"},
    {"inc/test/cmp", "48ffc0 4885c0 4839d8 48ffc9"},
    {"rol/imul/shr", "48c1c00d 480fafc3 48c1e803 48c1ca11"},
    {"lea/movzx", "488d0408 488d1c8d10000000 0fb6c8 480fbed1"},
    {"load/store", "488b0424 4889442408 8b4c2410 48894c2418 48034c2420"},
    {"push/pop", "50 51 59 58"},
    {"sse", "66480f6ec0 66480f6ecb 660fefc1 660f6cc1 660fd4c1 66480f7ec0"},
    {"jcc", "4885c0 7400 4839c0 7500 eb00"},
  };
  printf("%-14s %14s %14s\n", "loop", "concrete/s", "symbolic/s");
  for (auto& l : loops) {
    if (only && !strstr(l.name, only)) continue;
    double rate[2];
    for (int sym = (getenv("SYMONLY") ? 1 : 0); sym < 2; sym++) {
      Engine E; const u64 BASE = 0x400000, STACK = 0x7ff000;
      std::vector<u8> body = hexs(l.code);
      i32 back = -(i32)(body.size() + 5);
      body.push_back(0xe9); for (int i = 0; i < 4; i++) body.push_back((u8)(back >> (8 * i)));
      E.map(BASE, 4096); E.writeMem(BASE, body.data(), body.size());
      E.map(STACK - 0x1000, 0x2000);
      E.g[RSP] = STACK;
      const int regs[] = {RAX, RBX, RCX, RDX, RSI, RDI, R8, R9, R10};
      for (int i = 0; i < 9; i++) E.g[regs[i]] = 0x1234567ull * (i + 3);
      if (sym) {
        for (int i = 0; i < 9; i++) E.symbolizeReg(regs[i], "in" + std::to_string(i));
        for (int i = 0; i < 0x40; i += 8) E.symbolizeMem(STACK + i, 8, "s" + std::to_string(i));
      }
      E.rip = BASE;
      E.lazy = getenv("UNSHROUD_LAZY") != nullptr;
      u64 cnt = sym ? n / 20 : n;
      E.run(cnt / 100);
      auto t0 = std::chrono::steady_clock::now();
      E.run(cnt);
      double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
      rate[sym] = cnt / dt;
    }
    printf("%-14s %14.0f %14.0f\n", l.name, getenv("SYMONLY") ? 0.0 : rate[0], rate[1]);
  }
  return 0;
}
