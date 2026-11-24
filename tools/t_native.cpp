// The single-instruction native path (src/native.cpp) on instructions which must not run on this CPU or which fault on
// it: none may end the process, calls of a hypervisor are invalid-opcode exceptions of the program, and the host's
// MXCSR and direction flag are the host's afterwards.   t_native
#include "../src/util.hpp"
#include "../src/engine.hpp"
#include <cstdio>
#include <intrin.h>
using namespace unshroud;

static std::vector<u8> hexs(const char* s) { std::vector<u8> b; for (const char* p = s; *p;) { if (*p == ' ') { p++; continue; } unsigned v; sscanf(p, "%2x", &v); b.push_back((u8)v); p += 2; } return b; }

int main() {
  unshroud::limitMemory();
  struct T { const char* name; const char* code; int want; };   // want: 0 runs or is refused (no exception of the program), 1 invalid opcode
  const T tests[] = {
    {"vmcall", "0f01c1", 1}, {"vmmcall", "0f01d9", 1}, {"vmfunc", "0f01d4", 1}, {"vmxoff", "0f01c4", 1}, {"vmlaunch", "0f01c2", 1}, {"vmrun", "0f01d8", 1}, {"getsec", "0f37", 1}, {"enclu", "0f01d7", 1},
    {"xbegin", "c7f800000000", 0}, {"xend", "0f01d5", 0}, {"wrgsbase rax", "f3480faed8", 0}, {"rdfsbase rax", "f3480faec0", 0},
    {"wrpkru", "0f01ef", 0}, {"rdpkru", "0f01ee", 0}, {"rdsspq rax", "f3480f1ec8", 0}, {"monitorx", "0f01fa", 0}, {"rdpru", "0f01fd", 0},
    {"vpdpbusd xmm0,xmm1,xmm2 (AVX-VNNI)", "c4e27150c2", 0}, {"sha512msg1 ymm0,xmm1", "c4e27fccc1", 0}, {"vpmadd52luq xmm0,xmm1,xmm2 (AVX-IFMA)", "c4e2f1b4c2", 0},
    {"andn rax,rbx,rcx (runs)", "c4e2e0f2c1", 0}, {"pshufb xmm0,xmm1 (runs)", "660f3800c1", 0},
  };
  const unsigned csr0 = _mm_getcsr();
  int bad = 0, n = 0;
  for (const T& t : tests) {
    Engine E; E.jitOn = false;
    const u64 BASE = 0x400000;
    std::vector<u8> body = hexs(t.code); body.resize(body.size() + 8, 0x90);
    E.map(BASE, 4096); E.writeMem(BASE, body.data(), body.size());
    E.map(0x7fe000, 0x2000); E.g[RSP] = 0x7ff000; E.rip = BASE;
    E.fl.bits |= FL_DF;                               // the guest's direction flag is set: the host's must not be afterwards
    E.mxcsr = 0x7f80;                                 // ... and its rounding mode is not the host's
    const Stop s = E.run(1);
    const bool inval = s == ST_EXCEPTION && E.trapKind == TK_INVALID;
    const bool ok = (t.want == 1 ? inval : !inval) && _mm_getcsr() == csr0 && !(__readeflags() & 0x400);
    printf("%-42s stop %d (%s)%s%s%s\n", t.name, (int)s, E.stopInfo.c_str(), inval ? " invalid opcode" : "", _mm_getcsr() != csr0 ? "  HOST MXCSR CHANGED" : "", (__readeflags() & 0x400) ? "  HOST DF SET" : "");
    if (!ok) { bad++; _mm_setcsr(csr0); __writeeflags(__readeflags() & ~0x400ull); }
    n++;
  }
  printf("%s: %d cases, %d failed\n", bad ? "FAIL" : "ok", n, bad);
  return bad ? 1 : 0;
}
