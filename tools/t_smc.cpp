// Code which writes into its own pages: the interpreter and generated code must give the same results, the right ones,
// and what was decoded must be dropped exactly when a store touches bytes an instruction was decoded from (a store to
// the other bytes of such a page is a store like any other: virtual machines keep their registers next to their code).
// usage: t_smc     (prints one line per case; "ok: ..." when all hold)
#include "../src/util.hpp"
#include "../src/engine.hpp"
#include "../src/jit.hpp"
#include <cstdio>
#include <cstring>
#include <vector>
using namespace unshroud;

static const u64 CODE = 0x10000000ull, STACK = 0x7f0000000000ull;
struct Case { const char* name; std::vector<u8> code; u64 expectRbx; bool rbxKnown; u64 flushMin, flushMax; bool wantNative; };

static void put32(std::vector<u8>& c, size_t at, u32 v) { memcpy(c.data() + at, &v, 4); }

static std::vector<Case> cases() {
  std::vector<Case> cs;
  {   // 1. data next to code: read-modify-write and stores into the code's own page, far from any instruction
    std::vector<u8> c = {0xb9, 0x40, 0x0d, 0x03, 0x00,                 // mov ecx, 200000
                         0x48, 0x8d, 0x35, 0, 0, 0, 0,                 // lea rsi, [rip + data]
                         0x31, 0xdb,                                   // xor ebx, ebx
                         0x48, 0x01, 0x0e,                             // L: add [rsi], rcx
                         0x48, 0x8b, 0x16,                             // mov rdx, [rsi]
                         0x48, 0x01, 0xd3,                             // add rbx, rdx
                         0x48, 0x89, 0x5e, 0x08,                       // mov [rsi + 8], rbx
                         0xff, 0xc9,                                   // dec ecx
                         0x75, 0xef};                                  // jnz L
    put32(c, 8, 0x800 - 12);
    u64 m = 0, rbx = 0; for (u64 k = 200000; k; k--) { m += k; rbx += m; }
    cs.push_back({"data next to code", c, rbx, true, 0, 0, true});
  }
  {   // 2. an instruction changes the immediate of another one on every turn
    std::vector<u8> c = {0xb9, 0xb8, 0x0b, 0x00, 0x00,                 // mov ecx, 3000
                         0x31, 0xdb,                                   // xor ebx, ebx
                         0xb8, 0x01, 0x00, 0x00, 0x00,                 // L: mov eax, 1          (its immediate is at +8)
                         0x01, 0xc3,                                   // add ebx, eax
                         0xfe, 0x05, 0xf4, 0xff, 0xff, 0xff,           // inc byte [rip - 12]    (+8)
                         0xff, 0xc9,                                   // dec ecx
                         0x75, 0xef};                                  // jnz L
    u64 rbx = 0; for (u64 i = 0; i < 3000; i++) rbx += (1 + i) & 0xff;
    cs.push_back({"immediate rewritten on every turn", c, rbx & 0xffffffffull, true, 3000, 3000, false});
  }
  {   // 3. data becomes code: a small function is written (three stores), called, written again
    std::vector<u8> c = {0xb9, 0xd0, 0x07, 0x00, 0x00,                 // mov ecx, 2000
                         0x48, 0x8d, 0x3d, 0, 0, 0, 0,                 // lea rdi, [rip + buf]
                         0x31, 0xdb,                                   // xor ebx, ebx
                         0xc6, 0x07, 0xb8,                             // L: mov byte [rdi], 0xb8      (mov eax, imm32)
                         0x89, 0x4f, 0x01,                             // mov [rdi + 1], ecx
                         0xc6, 0x47, 0x05, 0xc3,                       // mov byte [rdi + 5], 0xc3     (ret)
                         0xff, 0xd7,                                   // call rdi
                         0x01, 0xc3,                                   // add ebx, eax
                         0xff, 0xc9,                                   // dec ecx
                         0x75, 0xee};                                  // jnz L
    put32(c, 8, 0x400 - 12);
    cs.push_back({"code written, called, written again", c, 2000ull * 2001 / 2, true, 1999, 3 * 2000, false});
  }
  {   // 4. the same with one 8-byte store which starts on data bytes and ends on the function's bytes
    std::vector<u8> c = {0xb9, 0xd0, 0x07, 0x00, 0x00,                 // mov ecx, 2000
                         0x48, 0x8d, 0x3d, 0, 0, 0, 0,                 // lea rdi, [rip + buf]
                         0x31, 0xdb,                                   // xor ebx, ebx
                         0x89, 0xc8,                                   // L: mov eax, ecx
                         0x48, 0xc1, 0xe0, 0x18,                       // shl rax, 24
                         0x48, 0xba, 0x00, 0x00, 0xb8, 0x00, 0x00, 0x00, 0x00, 0xc3,   // mov rdx, 0xc300000000b80000
                         0x48, 0x09, 0xd0,                             // or rax, rdx
                         0x48, 0x89, 0x47, 0xfe,                       // mov [rdi - 2], rax
                         0xff, 0xd7,                                   // call rdi
                         0x01, 0xc3,                                   // add ebx, eax
                         0xff, 0xc9,                                   // dec ecx
                         0x75, 0xe1};                                  // jnz L
    put32(c, 8, 0x400 - 12);
    cs.push_back({"one store over data and code bytes", c, 2000ull * 2001 / 2, true, 1999, 2000, false});
  }
  {   // 5. code reads its own bytes (a checksum): loads are not stores
    std::vector<u8> c = {0xbd, 0x20, 0x4e, 0x00, 0x00,                 // mov ebp, 20000
                         0x31, 0xdb,                                   // xor ebx, ebx
                         0xb9, 0x40, 0x00, 0x00, 0x00,                 // O: mov ecx, 0x40
                         0x48, 0x8d, 0x35, 0xed, 0xff, 0xff, 0xff,     // lea rsi, [rip - 19]   (the start)
                         0x0f, 0xb6, 0x16,                             // L: movzx edx, byte [rsi]
                         0x01, 0xd3,                                   // add ebx, edx
                         0x48, 0xff, 0xc6,                             // inc rsi
                         0xff, 0xc9,                                   // dec ecx
                         0x75, 0xf4,                                   // jnz L
                         0xff, 0xcd,                                   // dec ebp
                         0x75, 0xe4};                                  // jnz O
    c.resize(0x40, 0x90);
    u64 sum = 0; for (u8 b : c) sum += b;
    cs.push_back({"code read as data", c, (sum * 20000) & 0xffffffffull, true, 0, 0, true});
  }
  return cs;
}

struct Result { Stop stop; u64 g[16], rip, icount, flags, hash, flushes, native; };

static Result runCase(const Case& c, bool native) {
  Engine E; E.jitOn = native; E.jitHot = 1;
  E.map(CODE, 8192); E.map(STACK - 0x10000, 0x10000);
  E.writeMem(CODE, c.code.data(), c.code.size()); E.flushBlocks();
  memset(E.g, 0, sizeof E.g); memset(E.gs, 0, sizeof E.gs);
  E.g[RSP] = STACK - 0x100; E.rip = CODE; E.stops.insert(CODE + c.code.size());
  E.codeFlushes = 0;
  Result r{};
  r.stop = E.run(50000000);
  memcpy(r.g, E.g, sizeof r.g); r.rip = E.rip; r.icount = E.icount; r.flags = E.rflags(); r.hash = E.memHash();
  r.flushes = E.codeFlushes; r.native = E.jitIns;
  return r;
}

int main() {
  _putenv_s("UNSHROUD_JIT_PAYK", "0");
  unshroud::limitMemory();
  int bad = 0, n = 0;
  for (const Case& c : cases()) {
    const Result a = runCase(c, false), b = runCase(c, true);
    std::string why;
    const u64 end = CODE + c.code.size();
    if (a.stop != ST_ADDRESS || a.rip != end) why += " interpreter did not reach the end;";
    if (b.stop != ST_ADDRESS || b.rip != end) why += " native world did not reach the end;";
    if (memcmp(a.g, b.g, sizeof a.g) || a.rip != b.rip || a.icount != b.icount || a.flags != b.flags) why += " registers / flags / count differ;";
    if (a.hash != b.hash) why += " memory differs;";
    if (c.rbxKnown && a.g[RBX] != c.expectRbx) why += " interpreter: wrong result;";
    if (c.rbxKnown && b.g[RBX] != c.expectRbx) why += " native world: wrong result;";
    if (a.flushes < c.flushMin || a.flushes > c.flushMax) why += " interpreter: decoded code dropped an unexpected number of times;";
    if (b.flushes < c.flushMin || b.flushes > c.flushMax) why += " native world: decoded code dropped an unexpected number of times;";
    if (c.wantNative && b.native * 2 < b.icount) why += " hardly anything ran as native code;";
    printf("%s %-38s rbx %llx (expected %llx), %llu instructions (%llu native), code dropped %llu / %llu times%s%c", why.empty() ? "ok  " : "FAIL", c.name,
           (unsigned long long)b.g[RBX], (unsigned long long)c.expectRbx, (unsigned long long)b.icount, (unsigned long long)b.native,
           (unsigned long long)a.flushes, (unsigned long long)b.flushes, why.c_str(), 10);
    n++; bad += !why.empty();
  }
  printf("%s: %d cases, %d failed%c", bad ? "FAIL" : "ok", n, bad, 10);
  return bad != 0;
}
