// unshroud - native execution (see jit.hpp)
#include "jit.hpp"
#include <Zydis/Zydis.h>
#include <windows.h>
#include <intrin.h>
#include <chrono>
#include <cstdio>
#include <mutex>
#include <random>

namespace unshroud {

Stop nativeExec(Engine& E, const Insn& I);   // native.cpp

namespace {

enum : u64 { M_FLAGS = 1ull << 16, M_VEC = 17 };                  // the inputs' mask: bits 0-15 GPRs, 16 the flags, 17-32 vector registers
enum : u32 { TLBN = 65536, IBLN = 65536, COVN = 1u << 18, CODE_BYTES = 24u << 20, MAXI = 96, BAIL = 0x80000000u };
enum : u8 { X_NONE = 0, X_LINK, X_INTERP, X_IBL };
enum : u8 { K_INTERP = 0, K_GEN, K_NOP, K_LEA, K_PUSH, K_POP, K_CALL, K_CALLI, K_RET, K_JMP, K_JMPI, K_JCC, K_PUSHF, K_POPF, K_LEAVE };
const u32 A6 = FL_CF | FL_PF | FL_AF | FL_ZF | FL_SF | FL_OF;

// What generated code reads and writes outside the engine's pages. It sits at the start of the Jit's block of memory,
// below 2 GB: the code addresses it relative to rip, and the tables after it with 32-bit absolute addresses.
struct JState {
  u64 g[16];
  u64 rflags, hflags;
  i64 budget;                     // instructions the generated code may still run
  u64 fsbase, gsbase;
  u64 hostRsp;
  u64 exitId;                     // which exit was taken (an index, or BAIL | a site's code)
  u64 target;                     // of an indirect branch
  u64 keyhi;                      // the mask's number << 48, set before an indirect branch looks its target up
  u64 tmpc;                       // the guest's rcx while a lookup uses the register
  u64 faultCode;
  u64 hctx[16];                   // host registers around a call of the helper
  u32 mxcsr, hostMxcsr;
  u8 vecDirty; u8 pad[7];
  alignas(32) u8 v[16][32];
  alignas(32) u8 hv[16][32];
};

struct Asm {
  u8* p = nullptr;
  void b(u8 x) { *p++ = x; }
  void d(u32 x) { memcpy(p, &x, 4); p += 4; }
  void q(u64 x) { memcpy(p, &x, 8); p += 8; }
  void opc(u32 op) { if (op > 0xffff) b((u8)(op >> 16)); if (op > 0xff) b((u8)(op >> 8)); b((u8)op); }
  void rexop(u8 pre, bool w, u32 op, int reg, int index, int base) {
    if (pre) b(pre);
    const u8 r = (u8)(0x40 | (w ? 8 : 0) | ((reg >> 3) & 1) << 2 | (index >= 0 ? (index >> 3) & 1 : 0) << 1 | (base >= 0 ? (base >> 3) & 1 : 0));
    if (r != 0x40) b(r);
    opc(op);
  }
  // [base + index << sc + disp]; base < 0: [index << sc + disp32], an absolute address
  void mem(u8 pre, bool w, u32 op, int reg, int base, int index, int sc, i64 disp) {
    rexop(pre, w, op, reg, index, base);
    if (base < 0) { b((u8)((reg & 7) << 3 | 4)); b((u8)(sc << 6 | (index < 0 ? 4 : index & 7) << 3 | 5)); d((u32)disp); return; }
    const bool sib = index >= 0 || (base & 7) == 4;
    const int mod = (disp == 0 && (base & 7) != 5) ? 0 : (disp >= -128 && disp <= 127) ? 1 : 2;
    b((u8)(mod << 6 | (reg & 7) << 3 | (sib ? 4 : base & 7)));
    if (sib) b((u8)(sc << 6 | (index < 0 ? 4 : index & 7) << 3 | (base & 7)));
    if (mod == 1) b((u8)disp); else if (mod == 2) d((u32)disp);
  }
  void rr(u8 pre, bool w, u32 op, int reg, int rm) { rexop(pre, w, op, reg, -1, rm); b((u8)(0xc0 | (reg & 7) << 3 | (rm & 7))); }
  // [rip + disp32]: an address near the code; tail: bytes of immediate which follow the displacement
  void rip(u8 pre, bool w, u32 op, int reg, const void* t, int tail = 0) {
    rexop(pre, w, op, reg, -1, -1); b((u8)((reg & 7) << 3 | 5));
    d((u32)((const u8*)t - (p + 4 + tail)));
  }
  void movRR(int dst, int src) { rr(0, true, 0x89, src, dst); }
  void movRI(int dst, u64 v) {
    if (v <= 0xffffffffull) { if (dst >= 8) b(0x41); b((u8)(0xb8 + (dst & 7))); d((u32)v); }
    else { b((u8)(0x48 | (dst >> 3))); b((u8)(0xb8 + (dst & 7))); q(v); }
  }
  void load(int r, const void* t) { rip(0, true, 0x8b, r, t); }                  // mov r, [t]
  void store(const void* t, int r) { rip(0, true, 0x89, r, t); }                 // mov [t], r
  void lea(int dst, int base, int index, int sc, i64 disp) { mem(0, true, 0x8d, dst, base, index, sc, disp); }
  void shrx(int dst, int src, int cnt) {                                         // dst = src >> cnt, no flags
    b(0xc4); b((u8)(((~dst >> 3) & 1) << 7 | 0x40 | ((~src >> 3) & 1) << 5 | 0x02)); b((u8)(0x80 | ((~cnt) & 15) << 3 | 3)); b(0xf7);
    b((u8)(0xc0 | (dst & 7) << 3 | (src & 7)));
  }
  void pext(int dst, int src, int mask) {                                        // dst = the bits of src which mask selects, packed; no flags
    b(0xc4); b((u8)(((~dst >> 3) & 1) << 7 | 0x40 | ((~mask >> 3) & 1) << 5 | 0x02)); b((u8)(0x80 | ((~src) & 15) << 3 | 2)); b(0xf5);
    b((u8)(0xc0 | (dst & 7) << 3 | (mask & 7)));
  }
  void movzxW(int dst, int src) { rr(0, false, 0x0fb7, dst, src); }
  void loadIdx(int dst, const void* table, int idx) { mem(0, true, 0x8b, dst, -1, idx, 3, (i64)(uintptr_t)table); }   // mov dst, [table + idx * 8]
  void storeM(int base, int index, int src) { mem(0, true, 0x89, src, base, index, 0, 0); }                         // mov [base + index], src
  void loadM(int dst, int base, int index) { mem(0, true, 0x8b, dst, base, index, 0, 0); }
  void jrcxzOver() { b(0xe3); b(5); }                                            // jumps over the 5-byte jmp which follows
  u8* jmp(const void* t) { b(0xe9); u8* at = p; d((u32)((const u8*)t - (p + 4))); return at; }
  u8* jcc(int cc, const void* t) { b(0x0f); b((u8)(0x80 + cc)); u8* at = p; d((u32)((const u8*)t - (p + 4))); return at; }
  static void patch(u8* at, const void* t) { const u32 r = (u32)((const u8*)t - (at + 4)); memcpy(at, &r, 4); }
  void setD(const void* t, u32 v) { rip(0, false, 0xc7, 0, t, 4); d(v); }        // mov dword [t], v
  void setB(const void* t, u8 v) { rip(0, false, 0xc6, 0, t, 1); b(v); }         // mov byte [t], v
  void setW(const void* t, u16 v) { rip(0x66, false, 0xc7, 0, t, 2); b((u8)v); b((u8)(v >> 8)); }
  void pushI(u32 v) { b(0x68); d(v); }
  void push(int r) { if (r >= 8) b(0x41); b((u8)(0x50 + (r & 7))); }
  void pop(int r) { if (r >= 8) b(0x41); b((u8)(0x58 + (r & 7))); }
  // vector register <-> [t]: all 32 bytes (VEX) or the low 16 (legacy: the rest of the register is left alone)
  void vload(int r, const void* t, bool ymm) {
    if (ymm) { b(0xc5); b((u8)(((~r >> 3) & 1) << 7 | 0x7e)); b(0x6f); b((u8)((r & 7) << 3 | 5)); d((u32)((const u8*)t - (p + 4))); }
    else rip(0xf3, false, 0x0f6f, r, t);
  }
  void vstore(const void* t, int r, bool ymm) {
    if (ymm) { b(0xc5); b((u8)(((~r >> 3) & 1) << 7 | 0x7e)); b(0x7f); b((u8)((r & 7) << 3 | 5)); d((u32)((const u8*)t - (p + 4))); }
    else rip(0xf3, false, 0x0f7f, r, t);
  }
};

struct Frag;
struct Site {                       // one instruction of a fragment
  Frag* f; u64 addr; u64 mask;      // the inputs' mask before it
  u16 index, dirty, vdirty;         // registers written before it
  u8* host;                         // where its code starts
  u8* retry[2]; u8 msz[2]; u8 mkind[2]; bool spill[2];   // its lookups: 1 read, 2 read and write, 3 write only
};
struct Frag {
  u64 rip, mask; u8* entry; u8* head; u8* end; u32 n = 0, site0 = 0;
  u8 t0, t1, t2, sp; bool rcxUsed, loops, vex;
  u16 uAll = 0, wAll = 0, vuAll = 0, vwAll = 0;
  u32 entries = 0; u64 insSum = 0; bool cold = false;
};
struct ExitRec { u8 kind; u64 target, mask; u32 why; u8* patch; };   // why (exits to the interpreter): mnemonic + 4096 * (0 not compiled, 1 an operand holds an expression, 2 not encodable, 3 not code)
struct Key { u64 rip, mask; bool operator==(const Key& o) const { return rip == o.rip && mask == o.mask; } };
struct KeyHash { size_t operator()(const Key& k) const { return (size_t)((k.rip * 0x9E3779B97F4A7C15ull) ^ (k.mask * 0xff51afd7ed558ccdull) ^ (k.rip >> 29)); } };

std::recursive_mutex gLock; std::vector<Jit*> gJits; bool gVeh = false, gCalibrated = false;
bool gNever[ZYDIS_MNEMONIC_MAX_VALUE + 1];         // mnemonics whose undefined flags differ from the interpreter's on this CPU
u8 gZeroTaint[8192];

}  // namespace

class Jit {
public:
  Engine& E; JState* S = nullptr; u8* base = nullptr; size_t reserved = 0;
  u64 *ntagR, *ntagW, *taintT, *dataT, *ibl; u8* covB; u8* code; u8* codeEnd; u8* committed; u8* codeStart;
  Asm a; ZydisDecoder dec;
  u8 *enter, *exitCommon, *exitNoFlags, *bailG, *bailV, *faultStub, *iblStub;
  std::vector<Frag*> frags; std::vector<Site> sites; std::vector<ExitRec> exits;
  std::unordered_map<Key, Frag*, KeyHash> map;       // (address, mask) -> fragment, or null: not worth compiling
  std::vector<u64> masks; std::unordered_map<u64, u16> maskId;
  std::vector<u32> filled, iblFilled; std::vector<u64> covKeys;
  u32 epoch = 1; bool anyVec = false, oom = false, withCov = false;
  u64 lastCode = ~0ull, lastPage = 0; u32 repeats = 0;
  u64 payK = getenv("UNSHROUD_JIT_PAYK") ? strtoull(getenv("UNSHROUD_JIT_PAYK"), nullptr, 0) : 30, payCredit = getenv("UNSHROUD_JIT_CREDIT") ? strtoull(getenv("UNSHROUD_JIT_CREDIT"), nullptr, 0) : 400000;   // (see run())
  std::unordered_map<u32, u64> why;                  // UNSHROUD_JIT_WHY: exits to the interpreter, by cause
  bool whyOn = getenv("UNSHROUD_JIT_WHY") != nullptr; u32 failWhy = 0; u32 faultWhat = 0;
  JitStats st;

  explicit Jit(Engine& E) : E(E) {}
  bool init();
  void genStubs();
  bool commit(u8* upto);
  void flushCode(); void flushTlb(); void drop(u64 pn);
  bool fill(u64 A, unsigned size, int kind);
  u64 bail(u64 code);
  int siteAt(u64 ip);
  u16 idOf(u64 mask);
  Frag* compile(u64 rip, u64 mask);
  u64 run(u64 budget, Block* b);
  bool special(u64 x) const { return E.stops.count(x) || E.hooks.count(x) || (!E.havocSites.empty() && E.havocSites.count(x)) || (!E.forceSites.empty() && E.forceSites.count(x)) || (!E.switchTargets.empty() && E.switchTargets.count(x)) || (E.apiTable && x >= E.apiLo && x < E.apiHi && E.apiTable->count(x)); }
  bool peek(u64 addr, u8* buf, unsigned n);
};

namespace {

u64 __stdcall bailThunk(Jit* j, u64 code) { return j->bail(code); }

LONG CALLBACK veh(EXCEPTION_POINTERS* ep) {
  const u64 ip = ep->ContextRecord->Rip;
  std::lock_guard<std::recursive_mutex> g(gLock);
  for (Jit* j : gJits) {
    if (ip < (u64)j->codeStart || ip >= (u64)j->codeEnd) continue;
    const int s = j->siteAt(ip);
    if (s < 0) return EXCEPTION_CONTINUE_SEARCH;                 // in the stubs: a bug, not a guest fault
    j->S->faultCode = (u64)s * 4 + 2; j->faultWhat = ep->ExceptionRecord->ExceptionCode;
    ep->ContextRecord->Rip = (u64)j->faultStub;                  // the helper leaves native code at that instruction
    return EXCEPTION_CONTINUE_EXECUTION;
  }
  return EXCEPTION_CONTINUE_SEARCH;
}

bool cpuOk() {
  int r[4]; __cpuid(r, 0); if (r[0] < 7) return false;
  __cpuid(r, 1); const u32 c1 = (u32)r[2];
  const u32 need1 = (1u << 0) | (1u << 1) | (1u << 9) | (1u << 12) | (1u << 19) | (1u << 20) | (1u << 22) | (1u << 23) | (1u << 25) | (1u << 27) | (1u << 28) | (1u << 29);
  if ((c1 & need1) != need1) return false;
  if ((_xgetbv(0) & 6) != 6) return false;
  __cpuidex(r, 7, 0); const u32 b7 = (u32)r[1];
  if (!(b7 & (1u << 3)) || !(b7 & (1u << 5)) || !(b7 & (1u << 8))) return false;      // BMI1, AVX2, BMI2
  __cpuid(r, 0x80000001); if (!((u32)r[2] & (1u << 5))) return false;                 // LZCNT
  return true;
}

}  // namespace

bool Jit::init() {
  if (!cpuOk()) return false;
  ZydisDecoderInit(&dec, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_STACK_WIDTH_64);
  const size_t hdr = (sizeof(JState) + 0xffff) & ~(size_t)0xffff;
  const size_t tables = hdr + COVN + 4 * (size_t)TLBN * 8 + (size_t)IBLN * 16;
  reserved = (tables + CODE_BYTES + 0xffff) & ~(size_t)0xffff;
  for (u64 at = 0x10000000ull; at + reserved < 0x7ff00000ull && !base; at += 0x01000000ull)
    base = (u8*)VirtualAlloc((void*)at, reserved, MEM_RESERVE, PAGE_EXECUTE_READWRITE);
  if (!base) return false;
  if (!VirtualAlloc(base, tables, MEM_COMMIT, PAGE_READWRITE)) { VirtualFree(base, 0, MEM_RELEASE); base = nullptr; return false; }
  S = (JState*)base; covB = base + hdr;
  ntagR = (u64*)(covB + COVN); ntagW = ntagR + TLBN; taintT = ntagW + TLBN; dataT = taintT + TLBN; ibl = dataT + TLBN;
  code = codeStart = committed = base + tables; codeEnd = base + reserved;
  if (!commit(code + 65536)) return false;
  genStubs();
  std::lock_guard<std::recursive_mutex> g(gLock);
  if (!gVeh) { AddVectoredExceptionHandler(1, veh); gVeh = true; }
  gJits.push_back(this);
  return true;
}

bool Jit::commit(u8* upto) {
  if (upto <= committed) return true;
  if (upto > codeEnd) return false;
  const size_t n = ((size_t)(upto - committed) + 0xffff) & ~(size_t)0xffff;
  if (!VirtualAlloc(committed, n, MEM_COMMIT, PAGE_EXECUTE_READWRITE)) return false;
  committed += n; return true;
}

// The fixed code at the start of the code area: how native code is entered and left, the call of the helper, the
// lookup of an indirect branch's target.
void Jit::genStubs() {
  a.p = code;
  // ---- void enter(void* entry): saves what the host's code expects kept, loads the guest's flags and MXCSR, jumps
  enter = a.p;
  for (int r : {3, 5, 7, 6, 12, 13, 14, 15}) a.push(r);
  a.b(0x48); a.b(0x81); a.b(0xec); a.d(168);                                   // sub rsp, 168
  for (int i = 0; i < 10; i++) a.mem(0xf3, false, 0x0f7f, 6 + i, 4, -1, 0, 16 * i);       // movdqu [rsp + 16 i], xmm(6 + i)
  a.store(&S->hostRsp, 4);
  a.rip(0, false, 0x0fae, 3, &S->hostMxcsr);                                   // stmxcsr
  a.rip(0, false, 0x0fae, 2, &S->mxcsr);                                       // ldmxcsr
  a.rip(0, false, 0xff, 6, &S->rflags);                                        // push qword [rflags]
  a.b(0x9d);                                                                   // popfq
  a.b(0xff); a.b(0xe1);                                                        // jmp rcx
  // ---- every exit ends here
  exitCommon = a.p;
  a.b(0x9c);                                                                   // pushfq
  a.rip(0, false, 0x8f, 0, &S->rflags);                                        // pop qword [rflags]
  exitNoFlags = a.p;
  a.b(0xfc);                                                                   // cld
  a.rip(0, false, 0x0fae, 3, &S->mxcsr);
  a.rip(0, false, 0x0fae, 2, &S->hostMxcsr);
  a.b(0xc5); a.b(0xf8); a.b(0x77);                                             // vzeroupper
  a.load(4, &S->hostRsp);
  for (int i = 0; i < 10; i++) a.mem(0xf3, false, 0x0f6f, 6 + i, 4, -1, 0, 16 * i);
  a.b(0x48); a.b(0x81); a.b(0xc4); a.d(168);                                   // add rsp, 168
  for (int r : {15, 14, 13, 12, 6, 7, 5, 3}) a.pop(r);
  a.b(0xc3);
  // ---- the helper's call. On the stack: the site's code. All registers and the flags are kept; the helper returns
  // where to go on (the lookup again), or 0: native code is left (the helper has stored the guest's state).
  u8* bailExit = nullptr;
  for (int vec = 0; vec < 2; vec++) {
    (vec ? bailV : bailG) = a.p;
    a.b(0x9c);                                                                 // pushfq
    for (int r = 0; r < 16; r++) if (r != 4) a.store(&S->hctx[r], r);
    a.pop(0); a.store(&S->hflags, 0);                                          // the flags
    if (vec) for (int r = 0; r < 16; r++) a.vstore(S->hv[r], r, true);
    a.b(0xfc);                                                                 // cld
    // the helper is the host's code: it runs with the host's MXCSR (its own arithmetic must not set the guest's
    // status flags, nor run with the guest's rounding mode or unmasked exceptions)
    a.rip(0, false, 0x0fae, 3, &S->mxcsr);                                     // stmxcsr [guest]
    a.rip(0, false, 0x0fae, 2, &S->hostMxcsr);                                 // ldmxcsr [host]
    a.mem(0, true, 0x8b, 2, 4, -1, 0, 0);                                      // mov rdx, [rsp]: the code
    a.movRI(1, (u64)(uintptr_t)this);
    a.b(0x48); a.b(0x83); a.b(0xec); a.b(40);                                  // sub rsp, 40
    a.movRI(0, (u64)(uintptr_t)&bailThunk); a.b(0xff); a.b(0xd0);              // call rax
    a.b(0x48); a.b(0x83); a.b(0xc4); a.b(40);                                  // add rsp, 40
    a.rip(0, false, 0x0fae, 2, &S->mxcsr);                                     // ldmxcsr [guest]
    a.b(0x48); a.b(0x85); a.b(0xc0);                                           // test rax, rax
    a.b(0x0f); a.b(0x84); u8* jz = a.p; a.d(0);                                // jz bailExit
    a.mem(0, true, 0x89, 0, 4, -1, 0, 0);                                      // mov [rsp], rax: where to go on
    if (vec) for (int r = 0; r < 16; r++) a.vload(r, S->hv[r], true);
    for (int r = 0; r < 16; r++) if (r != 4) a.load(r, &S->hctx[r]);
    a.rip(0, false, 0xff, 6, &S->hflags); a.b(0x9d);                           // push qword [hflags]; popfq
    a.b(0xc3);                                                                 // ret
    if (!bailExit) { bailExit = a.p; a.jmp(exitNoFlags); }
    Asm::patch(jz, bailExit);
  }
  // ---- a fault in an instruction (the exception handler points rip here): the helper, with the site's code
  faultStub = a.p;
  a.rip(0, false, 0xff, 6, &S->faultCode);                                     // push qword [faultCode]
  a.jmp(bailV);
  // ---- an indirect branch: target (and keyhi) -> the fragment, if it is known
  iblStub = a.p;
  a.load(0, &S->target);
  a.movRI(2, 48); a.shrx(1, 0, 2);                                             // rcx = target >> 48
  a.jrcxzOver(); u8* m1 = a.jmp(a.p);
  a.movzxW(2, 0); a.lea(2, 2, 2, 0, 0);                                        // rdx = 2 * (target & 0xffff)
  a.load(1, &S->keyhi); a.lea(0, 0, 1, 0, 0);                                  // rax = key
  a.loadIdx(1, ibl, 2); a.lea(1, 1, 0, 0, 1);                                  // rcx = ~stored key + key + 1
  a.jrcxzOver(); u8* m2 = a.jmp(a.p);
  a.mem(0, false, 0xff, 4, -1, 2, 3, (i64)(uintptr_t)(ibl + 1));               // jmp qword [ibl + rdx * 8 + 8]
  Asm::patch(m1, a.p); Asm::patch(m2, a.p);
  a.jmp(exitCommon);                                                           // not known: the exit's number is in exitId
  code = a.p;
  codeStart = code;
}

namespace {

struct JI {                          // one guest instruction of a trace
  ZydisDecodedInstruction zi; ZydisDecodedOperand zo[ZYDIS_MAX_OPERAND_COUNT];
  u64 addr = 0, next = 0, target = 0;
  u8 kind = K_INTERP; i8 mem = -1; u8 msize = 0, mkind = 0, seg = 0;
  u16 rd = 0, wr = 0, full = 0, vr = 0, vw = 0;      // GPRs read (partly written counts), written, written whole and not read; vector registers
  u32 ftest = 0, fwrite = 0; bool ffull = false, vex = false;
};

int gprOf(ZydisRegister r) { return (int)ZydisRegisterGetLargestEnclosing(ZYDIS_MACHINE_MODE_LONG_64, r) - (int)ZYDIS_REGISTER_RAX; }
bool isGpr(ZydisRegisterClass c) { return c == ZYDIS_REGCLASS_GPR8 || c == ZYDIS_REGCLASS_GPR16 || c == ZYDIS_REGCLASS_GPR32 || c == ZYDIS_REGCLASS_GPR64; }
ZydisRegister gprReg(int idx, unsigned bits) {
  if (bits == 64) return (ZydisRegister)(ZYDIS_REGISTER_RAX + idx);
  if (bits == 32) return (ZydisRegister)(ZYDIS_REGISTER_EAX + idx);
  if (bits == 16) return (ZydisRegister)(ZYDIS_REGISTER_AX + idx);
  return (ZydisRegister)(idx < 4 ? ZYDIS_REGISTER_AL + idx : idx < 8 ? ZYDIS_REGISTER_SPL + (idx - 4) : ZYDIS_REGISTER_R8B + (idx - 8));
}

#define MN(m) case ZYDIS_MNEMONIC_##m:
// what the instruction is for generated code (K_INTERP: only the interpreter runs it), with the registers and flags it uses
u8 classify(JI& j) {
  const ZydisDecodedInstruction& zi = j.zi;
  if (zi.address_width != 64 || gNever[zi.mnemonic]) return K_INTERP;
  if (zi.encoding != ZYDIS_INSTRUCTION_ENCODING_LEGACY && zi.encoding != ZYDIS_INSTRUCTION_ENCODING_VEX) return K_INTERP;
  if (zi.attributes & ZYDIS_ATTRIB_IS_PRIVILEGED) return K_INTERP;
  const bool rep = (zi.attributes & (ZYDIS_ATTRIB_HAS_REP | ZYDIS_ATTRIB_HAS_REPE | ZYDIS_ATTRIB_HAS_REPNE)) != 0;
  j.vex = zi.encoding == ZYDIS_INSTRUCTION_ENCODING_VEX;
  if (const ZydisAccessedFlags* f = zi.cpu_flags) { j.ftest = f->tested & A6; j.fwrite = (f->modified | f->set_0 | f->set_1 | f->undefined) & A6; }
  const unsigned nv = zi.operand_count_visible;
  const auto rel = [&]() { u64 t = 0; ZydisCalcAbsoluteAddress(&zi, &j.zo[0], j.addr, &t); return t; };
  const auto regOp = [&](unsigned i) { return i < nv && j.zo[i].type == ZYDIS_OPERAND_TYPE_REGISTER && ZydisRegisterGetClass(j.zo[i].reg.value) == ZYDIS_REGCLASS_GPR64 && gprOf(j.zo[i].reg.value) < 16; };
  u8 kind = K_INTERP; bool gen = false, vecOnly = false;
  switch (zi.mnemonic) {
  MN(NOP) MN(ENDBR64) MN(ENDBR32) MN(PAUSE) MN(LFENCE) MN(MFENCE) MN(SFENCE) MN(PREFETCH) MN(PREFETCHT0) MN(PREFETCHT1) MN(PREFETCHT2)
  MN(PREFETCHNTA) MN(PREFETCHW) MN(CLFLUSH) MN(CLFLUSHOPT)
    return rep && zi.mnemonic != ZYDIS_MNEMONIC_PAUSE ? K_INTERP : K_NOP;
  MN(PUSH)
    if (rep || zi.operand_width != 64) return K_INTERP;
    if (regOp(0)) j.rd |= (u16)(1u << gprOf(j.zo[0].reg.value)); else if (j.zo[0].type != ZYDIS_OPERAND_TYPE_IMMEDIATE) return K_INTERP;
    j.rd |= 1u << RSP; j.wr |= 1u << RSP; return K_PUSH;
  MN(POP)
    if (rep || zi.operand_width != 64 || !regOp(0)) return K_INTERP;
    j.wr |= (u16)(1u << gprOf(j.zo[0].reg.value)); j.full |= (u16)(1u << gprOf(j.zo[0].reg.value)) & ~(1u << RSP);
    j.rd |= 1u << RSP; j.wr |= 1u << RSP; return K_POP;
  MN(PUSHFQ) if (rep) return K_INTERP; j.rd |= 1u << RSP; j.wr |= 1u << RSP; j.ftest = A6; j.fwrite = 0; return K_PUSHF;
  MN(POPFQ) if (rep) return K_INTERP; j.rd |= 1u << RSP; j.wr |= 1u << RSP; j.ftest = 0; j.fwrite = A6; j.ffull = true; return K_POPF;
  MN(LEAVE) if (rep) return K_INTERP; j.rd |= (1u << RSP) | (1u << RBP); j.wr |= (1u << RSP) | (1u << RBP); return K_LEAVE;
  MN(RET)
    if (zi.meta.branch_type != ZYDIS_BRANCH_TYPE_NEAR) return K_INTERP;
    j.rd |= 1u << RSP; j.wr |= 1u << RSP; j.target = nv && j.zo[0].type == ZYDIS_OPERAND_TYPE_IMMEDIATE ? (j.zo[0].imm.value.u & 0xffff) : 0; return K_RET;
  MN(CALL) MN(JMP) {
    const bool call = zi.mnemonic == ZYDIS_MNEMONIC_CALL;
    if (rep || zi.operand_width != 64 || (zi.meta.branch_type != ZYDIS_BRANCH_TYPE_NEAR && zi.meta.branch_type != ZYDIS_BRANCH_TYPE_SHORT)) return K_INTERP;
    if (call) { j.rd |= 1u << RSP; j.wr |= 1u << RSP; }
    if (j.zo[0].type == ZYDIS_OPERAND_TYPE_IMMEDIATE) { j.target = rel(); return call ? K_CALL : K_JMP; }
    kind = call ? K_CALLI : K_JMPI; gen = true; break;               // the operand (a register or memory) is looked at below
  }
  MN(JO) MN(JNO) MN(JB) MN(JNB) MN(JZ) MN(JNZ) MN(JBE) MN(JNBE) MN(JS) MN(JNS) MN(JP) MN(JNP) MN(JL) MN(JNL) MN(JLE) MN(JNLE)
    if (rep || j.zo[0].type != ZYDIS_OPERAND_TYPE_IMMEDIATE) return K_INTERP;
    j.target = rel(); return K_JCC;
  MN(LEA) kind = K_LEA; gen = true; break;
  MN(ADD) MN(SUB) MN(CMP) MN(AND) MN(OR) MN(XOR) MN(TEST) MN(NEG) MN(CMPXCHG) MN(XADD) MN(POPCNT) MN(ANDN) MN(BLSI) MN(BLSR) MN(BLSMSK) MN(BZHI)
    kind = K_GEN; gen = true; j.ffull = true; break;
  MN(SHL) MN(SHR) MN(SAR) MN(SHLD) MN(SHRD) {
    const bool dbl = zi.mnemonic == ZYDIS_MNEMONIC_SHLD || zi.mnemonic == ZYDIS_MNEMONIC_SHRD;
    if (dbl && zi.operand_width == 16) return K_INTERP;
    const ZydisDecodedOperand& c = j.zo[dbl ? 2 : 1];
    j.ffull = c.type == ZYDIS_OPERAND_TYPE_IMMEDIATE && (c.imm.value.u & (zi.operand_width == 64 ? 63 : 31)) != 0;
    kind = K_GEN; gen = true; break;
  }
  MN(BT) MN(BTS) MN(BTR) MN(BTC)
    if (j.zo[0].type == ZYDIS_OPERAND_TYPE_MEMORY && j.zo[1].type != ZYDIS_OPERAND_TYPE_IMMEDIATE) return K_INTERP;     // a bit string
    kind = K_GEN; gen = true; break;
  MN(MOV) MN(MOVZX) MN(MOVSX) MN(MOVSXD) MN(LAHF) MN(SAHF) MN(XCHG) MN(BSWAP) MN(MOVBE) MN(CBW) MN(CWDE) MN(CDQE) MN(CWD) MN(CDQ) MN(CQO)
  MN(CLC) MN(STC) MN(CMC) MN(CLD) MN(STD) MN(ADC) MN(SBB) MN(NOT) MN(INC) MN(DEC) MN(MUL) MN(IMUL) MN(DIV) MN(IDIV) MN(ROL) MN(ROR) MN(RCL) MN(RCR)
  MN(BSF) MN(BSR) MN(TZCNT) MN(LZCNT) MN(RORX) MN(SARX) MN(SHLX) MN(SHRX) MN(MULX) MN(PEXT) MN(PDEP)
  MN(CMOVO) MN(CMOVNO) MN(CMOVB) MN(CMOVNB) MN(CMOVZ) MN(CMOVNZ) MN(CMOVBE) MN(CMOVNBE) MN(CMOVS) MN(CMOVNS) MN(CMOVP) MN(CMOVNP) MN(CMOVL) MN(CMOVNL) MN(CMOVLE) MN(CMOVNLE)
  MN(SETO) MN(SETNO) MN(SETB) MN(SETNB) MN(SETZ) MN(SETNZ) MN(SETBE) MN(SETNBE) MN(SETS) MN(SETNS) MN(SETP) MN(SETNP) MN(SETL) MN(SETNL) MN(SETLE) MN(SETNLE)
    kind = K_GEN; gen = true; break;
  MN(VZEROUPPER) MN(VZEROALL) MN(EMMS) MN(LDMXCSR) MN(STMXCSR) MN(VLDMXCSR) MN(VSTMXCSR) return K_INTERP;
  default: kind = K_GEN; vecOnly = true; break;        // anything else: only with vector registers (what the interpreter runs on this CPU too)
  }
  if (rep) return K_INTERP;
  (void)gen;
  if (vecOnly) {
    switch (zi.meta.category) {
    case ZYDIS_CATEGORY_COND_BR: case ZYDIS_CATEGORY_UNCOND_BR: case ZYDIS_CATEGORY_CALL: case ZYDIS_CATEGORY_RET: case ZYDIS_CATEGORY_SYSCALL:
    case ZYDIS_CATEGORY_INTERRUPT: case ZYDIS_CATEGORY_SYSRET: case ZYDIS_CATEGORY_SYSTEM: case ZYDIS_CATEGORY_IO: case ZYDIS_CATEGORY_IOSTRINGOP:
    case ZYDIS_CATEGORY_STRINGOP: case ZYDIS_CATEGORY_PUSH: case ZYDIS_CATEGORY_POP: case ZYDIS_CATEGORY_X87_ALU: case ZYDIS_CATEGORY_SEMAPHORE:
      return K_INTERP;
    default: break;
    }
    switch (zi.meta.isa_ext) {
    case ZYDIS_ISA_EXT_SSE: case ZYDIS_ISA_EXT_SSE2: case ZYDIS_ISA_EXT_SSE3: case ZYDIS_ISA_EXT_SSSE3: case ZYDIS_ISA_EXT_SSE4: case ZYDIS_ISA_EXT_AVX:
    case ZYDIS_ISA_EXT_AVX2: case ZYDIS_ISA_EXT_AES: case ZYDIS_ISA_EXT_AVXAES: case ZYDIS_ISA_EXT_PCLMULQDQ: case ZYDIS_ISA_EXT_F16C: case ZYDIS_ISA_EXT_FMA:
      break;
    default: return K_INTERP;
    }
  }
  bool anyVec = false;
  const unsigned count = (kind == K_CALLI || kind == K_JMPI) ? nv : zi.operand_count;
  for (unsigned i = 0; i < count; i++) {
    const ZydisDecodedOperand& o = j.zo[i];
    const bool rdA = (o.actions & ZYDIS_OPERAND_ACTION_MASK_READ) != 0, wrA = (o.actions & ZYDIS_OPERAND_ACTION_MASK_WRITE) != 0;
    if (o.type == ZYDIS_OPERAND_TYPE_REGISTER) {
      const ZydisRegisterClass c = ZydisRegisterGetClass(o.reg.value);
      if (isGpr(c)) {
        const int r = gprOf(o.reg.value);
        if (r < 0 || r > 15 || (r == RSP && i >= nv)) return K_INTERP;           // (the stack used implicitly: only the kinds above)
        const u16 bit = (u16)(1u << r);
        const bool part = o.size < 32 || (o.actions & ZYDIS_OPERAND_ACTION_CONDWRITE) != 0;
        if (rdA || (wrA && part)) j.rd |= bit;
        if (wrA) { j.wr |= bit; if (!rdA && !part) j.full |= bit; }
      } else if (c == ZYDIS_REGCLASS_XMM || c == ZYDIS_REGCLASS_YMM) {
        const int r = ZydisRegisterGetId(o.reg.value);
        if (r < 0 || r > 15) return K_INTERP;
        anyVec = true; j.vr |= (u16)(1u << r); if (wrA) j.vw |= (u16)(1u << r);
      } else if (c == ZYDIS_REGCLASS_FLAGS || c == ZYDIS_REGCLASS_IP) {
      } else if (o.reg.value == ZYDIS_REGISTER_MXCSR && i >= nv) {
      } else return K_INTERP;
    } else if (o.type == ZYDIS_OPERAND_TYPE_MEMORY) {
      if (o.mem.type == ZYDIS_MEMOP_TYPE_AGEN) { if (kind != K_LEA) return K_INTERP; }
      else if (o.mem.type == ZYDIS_MEMOP_TYPE_MEM) {
        if (o.visibility != ZYDIS_OPERAND_VISIBILITY_EXPLICIT || j.mem >= 0 || kind == K_LEA) return K_INTERP;
        const unsigned sz = o.size / 8;
        if (sz != 1 && sz != 2 && sz != 4 && sz != 8 && sz != 16 && sz != 32) return K_INTERP;
        j.mem = (i8)i; j.msize = (u8)sz;
        j.mkind = !wrA ? 1 : (rdA || (o.actions & ZYDIS_OPERAND_ACTION_CONDWRITE)) ? 2 : 3;
        j.seg = o.mem.segment == ZYDIS_REGISTER_FS ? 1 : o.mem.segment == ZYDIS_REGISTER_GS ? 2 : 0;
      } else return K_INTERP;
      for (ZydisRegister br : {o.mem.base, o.mem.index}) {
        if (br == ZYDIS_REGISTER_NONE || br == ZYDIS_REGISTER_RIP) continue;
        if (ZydisRegisterGetClass(br) != ZYDIS_REGCLASS_GPR64 || gprOf(br) > 15) return K_INTERP;
        j.rd |= (u16)(1u << gprOf(br));
      }
      if (o.mem.index != ZYDIS_REGISTER_NONE && o.mem.base == ZYDIS_REGISTER_RIP) return K_INTERP;
    } else if (o.type != ZYDIS_OPERAND_TYPE_IMMEDIATE) return K_INTERP;
  }
  if (vecOnly && !anyVec) return K_INTERP;
  if (anyVec) {
    if ((j.rd | j.wr) & (1u << RSP)) { for (unsigned i = 0; i < zi.operand_count; i++) if (j.zo[i].type == ZYDIS_OPERAND_TYPE_REGISTER && isGpr(ZydisRegisterGetClass(j.zo[i].reg.value)) && gprOf(j.zo[i].reg.value) == RSP) return K_INTERP; }
    if (vecOnly) { const ZydisAccessedFlags* f = zi.cpu_flags; j.ffull = f && ((f->modified | f->set_0 | f->set_1) & A6) == A6; }
  }
  if (zi.mnemonic == ZYDIS_MNEMONIC_BSF || zi.mnemonic == ZYDIS_MNEMONIC_BSR) { j.rd |= j.wr; j.full = 0; }     // nothing is written when the source is 0
  if (kind == K_LEA && (zi.operand_width == 16 || (zi.attributes & ZYDIS_ATTRIB_HAS_SEGMENT))) return K_INTERP;
  if ((kind == K_CALLI || kind == K_JMPI) && j.mem < 0 && !regOp(0)) return K_INTERP;
  return kind;
}
#undef MN

}  // namespace

// the bytes of code at addr, without touching anything (0: not mapped, or bytes which hold expressions / are unknown)
bool Jit::peek(u64 addr, u8* buf, unsigned n) {
  memset(buf, 0, n);
  for (unsigned i = 0; i < n;) {
    const u64 x = addr + i; const unsigned off = (unsigned)(x & 4095), k = std::min<unsigned>(n - i, 4096 - off);
    auto it = E.pages.find(x >> 12);
    if (it == E.pages.end() || it->second->nsym || it->second->unk) return false;
    memcpy(buf + i, it->second->d + off, k); i += k;
  }
  return true;
}

u16 Jit::idOf(u64 mask) {
  auto it = maskId.find(mask);
  if (it != maskId.end()) return it->second;
  const u16 id = (u16)masks.size(); masks.push_back(mask); maskId.emplace(mask, id);
  return id;
}

void Jit::flushTlb() { for (u32 i : filled) { ntagR[i] = 0; ntagW[i] = 0; } filled.clear(); }
void Jit::drop(u64 pn) { const u32 i = (u32)(pn & (TLBN - 1)); if (ntagR[i] == ~pn) { ntagR[i] = 0; ntagW[i] = 0; } }

void Jit::flushCode() {
  if (frags.empty() && map.empty()) return;
  if (E.covOn) jitSyncCov(this, E);
  memset(covB, 0, covKeys.size());
  for (Frag* f : frags) delete f;
  frags.clear(); map.clear(); sites.clear(); exits.clear(); covKeys.clear();
  for (u32 i : iblFilled) { ibl[2 * i] = 0; ibl[2 * i + 1] = 0; }
  iblFilled.clear();
  code = codeStart; epoch++; st.flushes++;
  if (masks.size() > 60000) { masks.clear(); maskId.clear(); }
}

// The page of an access native code could not do by itself goes into the table, when the access is one native code
// may do: within one page, no byte of it holding an expression or unknown (a store which only writes makes its bytes
// plain first, as the interpreter's store does). False: the interpreter runs the instruction.
bool Jit::fill(u64 A, unsigned size, int kind) {
  const unsigned off = (unsigned)(A & 4095);
  failWhy = 1; if (off + size > 4096) return false;
  const u64 pn = A >> 12;
  Page* p = kind == 1 ? E.pageR(pn) : E.pageW(pn);
  failWhy = 2; if (!p) return false;
  // a store into bytes instructions were decoded from: the interpreter's (it drops what was decoded)
  failWhy = 3; if (kind != 1 && p->code && E.codeHit(pn, off, size)) return false;
  failWhy = 4;
  // (a page with decoded bytes gets its marks when native code first stores to it; loads need none)
  const bool hasCode = p->code && !E.codeBits.empty() && E.codeBits.count(pn);
  if (p->nsym || p->unk || (hasCode && kind != 1)) {
    if (!p->taint) {
      p->taint = new u8[8192];
      if (p->sh) for (int i = 0; i < 4096; i++) p->taint[i] = p->sh[i].e ? 0xff : 0; else memset(p->taint, 0, 4096);
      if (p->unk) for (int w = 0; w < 512; w++) if ((p->unk[w >> 6] >> (w & 63)) & 1) memset(p->taint + 8 * w, 0xff, 8);
      memcpy(p->taint + 4096, p->taint, 4096);
    }
    u8 any = 0; for (unsigned i = 0; i < size; i++) any |= p->taint[off + i];
    if (any) {
      if (kind != 3) return false;
      if (p->unk) E.unkStore(p, A, size);
      if (p->nsym && p->sh) for (unsigned i = 0; i < size; i++) if (p->sh[off + i].e) { p->sh[off + i].e = 0; p->nsym--; }
      memset(p->taint + off, 0, size); memset(p->taint + 4096 + off, 0, size);
    }
  }
  // the marks stores check: the bytes with expressions, and this engine's decoded bytes as they are now (marks of
  // code which was dropped since go: a page native code may store to is this engine's alone)
  if (p->taint && kind != 1 && p->refs == 1) memcpy(p->taint + 4096, p->taint, 4096);
  if (hasCode && p->taint) E.codeMarks(p, pn, 0, 4096);
  const u32 idx = (u32)(pn & (TLBN - 1));
  if (!ntagR[idx]) filled.push_back(idx);
  ntagR[idx] = ~pn; dataT[idx] = (u64)(uintptr_t)p->d - (pn << 12);
  taintT[idx] = (u64)(uintptr_t)(p->taint ? p->taint : gZeroTaint) - (pn << 12);
  ntagW[idx] = (p->refs == 1 && (!hasCode || p->taint)) ? ~pn : 0;         // (stores check the page's second half of marks)
  st.fills++;
  return true;
}

// Called by generated code (through the stub) when a lookup failed, the budget ran out, or an instruction faulted.
// Returns where the generated code goes on, or 0 after storing the guest's registers: native code is left before the
// site's instruction.
u64 Jit::bail(u64 code) {
  st.helper++;
  Site& s = sites[code >> 2]; const int w = (int)(code & 3); Frag* f = s.f;
  if (w < 2) {
    bool ok = false; const u64 A = S->hctx[f->t0];
    // (the same access failing again right after its page went in: something is wrong with it, the interpreter decides)
    if (code == lastCode && (A >> 12) == lastPage) repeats++; else { lastCode = code; lastPage = A >> 12; repeats = 0; }
    failWhy = 5;
    try { ok = repeats < 3 && fill(A, s.msz[w], s.mkind[w]); } catch (...) { oom = true; }
    if (ok) return (u64)(uintptr_t)s.retry[w];
  }
  st.bails++;
  for (int r = 0; r < 16; r++) if ((f->wAll >> r) & 1) S->g[r] = r == RSP ? S->hctx[f->sp] : (r == RCX && w != 2) ? S->tmpc : S->hctx[r];
  for (int r = 0; r < 16; r++) if ((f->vwAll >> r) & 1) memcpy(S->v[r], S->hv[r], f->vex ? 32 : 16);
  S->rflags = S->hflags;
  S->exitId = BAIL | code;
  return 0;
}

// the instruction of a fragment whose code holds the host address ip, or -1
int Jit::siteAt(u64 ip) {
  size_t lo = 0, hi = frags.size();
  while (lo < hi) { const size_t mid = (lo + hi) / 2; if ((u64)(uintptr_t)frags[mid]->end <= ip) lo = mid + 1; else hi = mid; }
  if (lo >= frags.size() || (u64)(uintptr_t)frags[lo]->entry > ip) return -1;
  Frag* f = frags[lo]; int best = -1;
  for (u32 i = 0; i < f->n; i++) if ((u64)(uintptr_t)sites[f->site0 + i].host <= ip) best = (int)(f->site0 + i);
  return best;
}

// Compiles the trace which starts at rip for inputs with this mask: instructions in a row, through direct jumps, up
// to a conditional or indirect branch, a call, an address the engine watches, or an instruction (or an operand with an
// expression) only the interpreter handles. Null: nothing to run natively there.
Frag* Jit::compile(u64 rip, u64 mask) {
  const auto t0 = std::chrono::steady_clock::now();
  struct Timer { JitStats& st; std::chrono::steady_clock::time_point t0; ~Timer() { st.tCompile += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(); } } timer{st, t0};
  std::vector<JI> tr; std::vector<u64> seen;
  u64 x = rip, m = mask, endTarget = 0; u16 U = 0, W = 0, VU = 0, VW = 0; int endKind = X_LINK; bool vex = false; u32 endWhy = 3 * 4096;
  for (;;) {
    if (tr.size() >= MAXI || special(x) || (E.guardSet && x < (E.guardSet << 12))) { endKind = X_LINK; endTarget = x; break; }
    JI j; j.addr = x; u8 buf[16];
    unsigned have = 15; while (have && !peek(x, buf, have)) have--;          // (fewer at the end of what is mapped)
    if (!have || !ZYAN_SUCCESS(ZydisDecoderDecodeFull(&dec, buf, have, &j.zi, j.zo))) { endKind = X_INTERP; endTarget = x; break; }
    j.next = x + j.zi.length; j.kind = classify(j);
    bool interp = j.kind == K_INTERP || (j.rd & m & 0xffff) || (((u64)j.vr << M_VEC) & m) || ((m & M_FLAGS) && (j.ftest || (j.fwrite && !j.ffull)));
    if (interp) { endKind = X_INTERP; endTarget = x; endWhy = (u32)j.zi.mnemonic + (j.kind == K_INTERP ? 0 : 4096); break; }
    const u16 nu = U | j.rd | j.wr;                    // three scratch registers (and one for the guest's stack pointer) stay free
    if (14 - (int)__popcnt16(nu & ~((1u << RSP) | (1u << RCX))) < 3 + ((nu >> RSP) & 1)) { endKind = X_LINK; endTarget = x; break; }
    U = nu; W |= j.wr; VU |= j.vr | j.vw; VW |= j.vw; if (j.vr | j.vw) vex = vex || j.vex;
    m &= ~(u64)j.full; if (j.fwrite && j.ffull) m &= ~M_FLAGS;
    tr.push_back(j); seen.push_back(x);
    E.markCode(x, (unsigned)j.zi.length);
    if (j.kind == K_JMP) {
      x = j.target;
      if (x == rip || std::find(seen.begin(), seen.end(), x) != seen.end()) { endKind = X_LINK; endTarget = x; break; }
      continue;
    }
    if (j.kind == K_JCC) { endKind = 100; break; }
    if (j.kind == K_CALL) { endKind = X_LINK; endTarget = j.target; break; }
    if (j.kind == K_RET || j.kind == K_JMPI || j.kind == K_CALLI) { endKind = X_IBL; break; }
    x = j.next;
  }
  if (tr.empty()) { st.refused++; return nullptr; }
  if (!commit(code + 8192 + tr.size() * 640) || sites.size() + tr.size() >= (1u << 28) || covKeys.size() + 2 >= COVN) { flushCode(); return nullptr; }
  Frag* f = new Frag; f->rip = rip; f->mask = mask; f->uAll = U; f->wAll = W; f->vuAll = VU; f->vwAll = VW; f->vex = vex;
  f->rcxUsed = (U >> RCX) & 1;
  { int pick[4], n = 0;                                 // scratch registers: the low ones first (no REX prefix needed with ah..bh)
    for (int r : {0, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}) if (!((U >> r) & 1) && n < 4) pick[n++] = r;
    f->t0 = (u8)pick[0]; f->t1 = (u8)pick[1]; f->t2 = (u8)pick[2]; f->sp = (U >> RSP) & 1 ? (u8)pick[3] : 0xff; }
  const int T0 = f->t0, T1 = f->t1, T2 = f->t2, SP = f->sp;
  const auto host = [&](int r) { return r == RSP ? SP : r; };
  const JI& last = tr.back();
  f->loops = m == mask && ((endKind == X_LINK && endTarget == rip) || (endKind == 100 && (last.target == rip || last.next == rip)));
  f->site0 = (u32)sites.size(); sites.resize(sites.size() + tr.size());
  struct Fix { u8* at; u32 code; }; std::vector<Fix> fix;
  const auto slow = [&](u32 codeNo) { a.jrcxzOver(); fix.push_back({a.jmp(a.p), codeNo}); };
  a.p = code; f->entry = a.p;
  for (int r = 0; r < 16; r++) if ((U >> r) & 1) a.load(host(r), &S->g[r]);
  for (int r = 0; r < 16; r++) if ((VU >> r) & 1) a.vload(r, S->v[r], vex);
  if (VW) { a.setB(&S->vecDirty, 1); anyVec = true; }
  if (VU) anyVec = true;
  f->head = a.p;                                        // the budget: n instructions less, or out
  if (f->rcxUsed) a.store(&S->tmpc, RCX);
  a.load(RCX, &S->budget);
  a.b(0x48); a.b(0x8d); a.b(0x89); u8* nfix = a.p; a.d(0);               // lea rcx, [rcx - n]
  a.store(&S->budget, RCX);
  a.movRI(T0, 63); a.shrx(RCX, RCX, T0);
  slow(f->site0 * 4 + 3);
  if (f->rcxUsed) a.load(RCX, &S->tmpc);
  // an access of `size` bytes at the guest address [base + index << sc + disp] (abs: disp alone): afterwards T0 holds
  // the address and T1 what to add to it for the host's; flags and the guest's registers are as before
  const auto lookup = [&](u32 si, int which, int base, int index, int sc, i64 disp, bool abs, int seg, unsigned size, int kind) {
    Site& s = sites[si];
    if (f->rcxUsed) a.store(&S->tmpc, RCX);
    if (abs) a.movRI(T0, (u64)disp); else a.lea(T0, base, index, sc, disp);
    if (seg) { a.load(T1, seg == 1 ? &S->fsbase : &S->gsbase); a.lea(T0, T0, T1, 0, 0); }
    s.retry[which] = a.p; s.msz[which] = (u8)size; s.mkind[which] = (u8)kind;
    a.movRI(RCX, 12);
    if (size > 1) { a.lea(T2, T0, -1, 0, size - 1); a.shrx(T2, T2, RCX); a.shrx(T1, T0, RCX); a.movzxW(T1, T1); }
    else { a.shrx(T2, T0, RCX); a.movzxW(T1, T2); }
    a.loadIdx(RCX, kind == 1 ? ntagR : ntagW, T1);
    a.lea(RCX, RCX, T2, 0, 1);                          // 0: the table's page is the one of the last byte (so of the first too)
    slow(si * 4 + which);
    a.loadIdx(T2, taintT, T1); a.loadIdx(T1, dataT, T1);
    const unsigned half = kind == 1 ? 0 : 4096;         // a store also checks for bytes instructions were decoded from
    for (unsigned o = 0; o < size; o += 8) {            // no byte of the access holds an expression or is unknown
      const unsigned k = std::min(8u, size - o);
      if (k == 8) a.mem(0, true, 0x8b, RCX, T0, T2, 0, half + o); else if (k == 4) a.mem(0, false, 0x8b, RCX, T0, T2, 0, half + o);
      else a.mem(0, false, k == 2 ? 0x0fb7 : 0x0fb6, RCX, T0, T2, 0, half + o);
      slow(si * 4 + which);
    }
    if (f->rcxUsed) a.load(RCX, &S->tmpc);
  };
  const auto memOf = [&](u32 si, int which, const JI& j, unsigned size, int kind) {
    const ZydisDecodedOperand& o = j.zo[j.mem];
    if (o.mem.base == ZYDIS_REGISTER_RIP) { lookup(si, which, -1, -1, 0, (i64)(j.next + (u64)o.mem.disp.value), true, j.seg, size, kind); return; }
    const int base = o.mem.base == ZYDIS_REGISTER_NONE ? -1 : host(gprOf(o.mem.base)), index = o.mem.index == ZYDIS_REGISTER_NONE ? -1 : host(gprOf(o.mem.index));
    const int sc = o.mem.scale == 8 ? 3 : o.mem.scale == 4 ? 2 : o.mem.scale == 2 ? 1 : 0;
    lookup(si, which, base, index, sc, o.mem.disp.value, base < 0 && index < 0, j.seg, size, kind);
  };
  // the instruction again, for this CPU: the stack pointer's register renamed, the memory operand as [T0 + T1]
  const auto encode = [&](const JI& j) -> bool {
    ZydisEncoderRequest req;
    if (!ZYAN_SUCCESS(ZydisEncoderDecodedInstructionToEncoderRequest(&j.zi, j.zo, j.zi.operand_count_visible, &req))) return false;
    req.prefixes &= ~(ZydisInstructionAttributes)ZYDIS_ATTRIB_HAS_SEGMENT;
    ZydisMnemonic want = j.zi.mnemonic;
    if (j.mem >= 0) switch (want) {
      case ZYDIS_MNEMONIC_MOVDQA: want = ZYDIS_MNEMONIC_MOVDQU; break; case ZYDIS_MNEMONIC_MOVAPS: want = ZYDIS_MNEMONIC_MOVUPS; break;
      case ZYDIS_MNEMONIC_MOVAPD: want = ZYDIS_MNEMONIC_MOVUPD; break; case ZYDIS_MNEMONIC_VMOVDQA: want = ZYDIS_MNEMONIC_VMOVDQU; break;
      case ZYDIS_MNEMONIC_VMOVAPS: want = ZYDIS_MNEMONIC_VMOVUPS; break; case ZYDIS_MNEMONIC_VMOVAPD: want = ZYDIS_MNEMONIC_VMOVUPD; break;
      default: break;
    }
    req.mnemonic = want;
    const auto ren = [&](ZydisRegister r) {
      if (r == ZYDIS_REGISTER_NONE || !isGpr(ZydisRegisterGetClass(r)) || gprOf(r) != RSP) return r;
      return gprReg(SP, (unsigned)ZydisRegisterGetWidth(ZYDIS_MACHINE_MODE_LONG_64, r));
    };
    for (unsigned i = 0; i < req.operand_count; i++) {
      ZydisEncoderOperand& o = req.operands[i];
      if (o.type == ZYDIS_OPERAND_TYPE_REGISTER) o.reg.value = ren(o.reg.value);
      else if (o.type == ZYDIS_OPERAND_TYPE_MEMORY) {
        if ((int)i == j.mem) { o.mem.base = gprReg(T0, 64); o.mem.index = gprReg(T1, 64); o.mem.scale = 1; o.mem.displacement = 0; }
        else { o.mem.base = ren(o.mem.base); o.mem.index = ren(o.mem.index); }
      }
    }
    u8 out[16]; ZyanUSize len = sizeof out;
    if (!ZYAN_SUCCESS(ZydisEncoderEncodeInstruction(&req, out, &len))) return false;
    // what was encoded is decoded and compared: the same instruction, the operands meant
    ZydisDecodedInstruction z2; ZydisDecodedOperand o2[ZYDIS_MAX_OPERAND_COUNT];
    if (!ZYAN_SUCCESS(ZydisDecoderDecodeFull(&dec, out, len, &z2, o2)) || z2.length != len) return false;
    const ZydisInstructionAttributes keep = ZYDIS_ATTRIB_HAS_LOCK | ZYDIS_ATTRIB_HAS_REP | ZYDIS_ATTRIB_HAS_REPE | ZYDIS_ATTRIB_HAS_REPNE;
    if (z2.mnemonic != want || z2.encoding != j.zi.encoding || z2.operand_width != j.zi.operand_width || z2.operand_count_visible != j.zi.operand_count_visible ||
        (z2.attributes & keep) != (j.zi.attributes & keep) || (z2.attributes & (ZYDIS_ATTRIB_HAS_SEGMENT_FS | ZYDIS_ATTRIB_HAS_SEGMENT_GS)) || z2.address_width != 64) return false;
    for (unsigned i = 0; i < z2.operand_count_visible; i++) {
      const ZydisDecodedOperand& p = j.zo[i]; const ZydisDecodedOperand& q = o2[i];
      if (p.type != q.type || (p.type != ZYDIS_OPERAND_TYPE_IMMEDIATE && p.size != q.size)) return false;
      if (p.type == ZYDIS_OPERAND_TYPE_REGISTER) { if (q.reg.value != ren(p.reg.value)) return false; }
      else if (p.type == ZYDIS_OPERAND_TYPE_IMMEDIATE) { if (q.imm.value.u != p.imm.value.u) return false; }
      else if ((int)i == j.mem) {
        const ZydisRegister b = gprReg(T0, 64), ix = gprReg(T1, 64);
        if (!((q.mem.base == b && q.mem.index == ix) || (q.mem.base == ix && q.mem.index == b)) || q.mem.scale != 1 || q.mem.disp.value != 0) return false;
      } else if (q.mem.base != ren(p.mem.base) || q.mem.index != ren(p.mem.index) || q.mem.scale != p.mem.scale || q.mem.disp.value != p.mem.disp.value) return false;
    }
    memcpy(a.p, out, len); a.p += len;
    return true;
  };
  const auto stores = [&]() {
    for (int r = 0; r < 16; r++) if ((W >> r) & 1) a.store(&S->g[r], host(r));
    for (int r = 0; r < 16; r++) if ((VW >> r) & 1) a.vstore(S->v[r], r, vex);
  };
  // an exit: to the engine at first; to the target's fragment once there is one (the engine patches the jump)
  const auto exitTo = [&](u8 kind, u64 target, u64 mk, int cov, u32 whyNo = 0) {
    if (cov >= 0) a.setB(covB + cov, 1);
    if (kind == X_LINK && target == rip && mk == mask) { a.jmp(f->head); return; }     // the loop: the registers stay where they are
    stores();
    const u32 id = (u32)exits.size(); exits.push_back({kind, target, mk, whyNo, nullptr});
    if (kind == X_LINK) { exits[id].patch = a.jmp(a.p); Asm::patch(exits[id].patch, a.p); }
    if (kind == X_IBL) a.setW((const u8*)&S->keyhi + 6, idOf(mk));
    a.setD(&S->exitId, id);
    a.jmp(kind == X_IBL ? iblStub : exitCommon);
  };
  u64 mk = mask; u32 n = 0;
  for (; n < tr.size(); n++) {
    const JI& j = tr[n]; const u32 si = f->site0 + n; Site& s = sites[si];
    s = Site{}; s.f = f; s.addr = j.addr; s.mask = mk; s.index = (u16)n; s.host = a.p;
    bool ok = true;
    const auto reg0 = [&]() { return host(gprOf(j.zo[0].reg.value)); };
    switch (j.kind) {
    case K_NOP: case K_JMP: case K_JCC: break;
    case K_GEN: if (j.mem >= 0) memOf(si, 0, j, j.msize, j.mkind); ok = encode(j); break;
    case K_LEA:
      if (j.zo[1].mem.base == ZYDIS_REGISTER_RIP) {
        const u64 v = j.next + (u64)j.zo[1].mem.disp.value;
        a.movRI(reg0(), j.zi.operand_width == 64 ? v : (v & 0xffffffffull));
      } else ok = encode(j);
      break;
    case K_PUSH:
      lookup(si, 0, SP, -1, 0, -8, false, 0, 8, 3);
      if (j.zo[0].type == ZYDIS_OPERAND_TYPE_REGISTER) a.storeM(T0, T1, reg0());
      else { a.mem(0, true, 0xc7, 0, T0, T1, 0, 0); a.d((u32)j.zo[0].imm.value.s); }
      a.movRR(SP, T0);
      break;
    case K_POP:
      lookup(si, 0, SP, -1, 0, 0, false, 0, 8, 1);
      a.loadM(reg0(), T0, T1);
      if (gprOf(j.zo[0].reg.value) != RSP) a.lea(SP, SP, -1, 0, 8);
      break;
    case K_CALL: case K_CALLI:
      if (j.kind == K_CALLI) {
        if (j.mem >= 0) { memOf(si, 0, j, 8, 1); a.loadM(T2, T0, T1); a.store(&S->target, T2); }
        else a.store(&S->target, reg0());
      }
      lookup(si, 1, SP, -1, 0, -8, false, 0, 8, 3);
      a.movRI(T2, j.next); a.storeM(T0, T1, T2); a.movRR(SP, T0);
      break;
    case K_RET:
      lookup(si, 0, SP, -1, 0, 0, false, 0, 8, 1);
      a.loadM(T2, T0, T1); a.lea(SP, SP, -1, 0, 8 + (i64)j.target); a.store(&S->target, T2);
      break;
    case K_JMPI:
      if (j.mem >= 0) { memOf(si, 0, j, 8, 1); a.loadM(T2, T0, T1); a.store(&S->target, T2); }
      else a.store(&S->target, reg0());
      break;
    case K_PUSHF:
      lookup(si, 0, SP, -1, 0, -8, false, 0, 8, 3);
      a.b(0x9c); a.pop(T2); a.storeM(T0, T1, T2); a.movRR(SP, T0);
      break;
    case K_POPF:                                          // the arithmetic flags and DF from the value, nothing else
      lookup(si, 0, SP, -1, 0, 0, false, 0, 8, 1);
      a.loadM(T2, T0, T1);
      // a value which sets the trap, nested-task, alignment-check or identification bit is the interpreter's to load
      // (the single step it arms, the bits a later pushfq shows): the lookup's helper gives up after its retries
      if (f->rcxUsed) a.store(&S->tmpc, RCX);
      a.movRI(RCX, 0x244100); a.pext(RCX, T2, RCX);
      slow(si * 4 + 0);
      if (f->rcxUsed) a.load(RCX, &S->tmpc);
      a.lea(SP, SP, -1, 0, 8);
      a.rr(0, false, 0x81, 4, T2); a.d(0xcd5); a.rr(0, false, 0x81, 1, T2); a.d(0x202);     // and t2d, 0xcd5; or t2d, 0x202
      a.push(T2); a.b(0x9d);
      break;
    case K_LEAVE:
      lookup(si, 0, RBP, -1, 0, 0, false, 0, 8, 1);
      a.loadM(T2, T0, T1); a.lea(SP, RBP, -1, 0, 8); a.movRR(RBP, T2);
      break;
    default: ok = false;
    }
    if (!ok) { a.p = s.host; while (!fix.empty() && fix.back().code / 4 == si) fix.pop_back(); break; }   // only the interpreter after all
    mk &= ~(u64)j.full; if (j.fwrite && j.ffull) mk &= ~M_FLAGS;
  }
  if (n == 0) { sites.resize(f->site0); delete f; st.refused++; return nullptr; }
  if (n < tr.size()) { endKind = X_INTERP; endTarget = tr[n].addr; endWhy = (u32)tr[n].zi.mnemonic + 2 * 4096; sites.resize(f->site0 + n); }
  f->n = n; { const u32 neg = (u32)-(i32)n; memcpy(nfix, &neg, 4); }
  u8* bodyEnd;
  if (endKind == 100) {
    const JI& j = tr[n - 1]; int cov = -1;
    if (E.covOn) { cov = (int)covKeys.size(); covKeys.push_back(j.addr << 1); covKeys.push_back((j.addr << 1) | 1); }
    int cc = 0;
    switch (j.zi.mnemonic) {
    case ZYDIS_MNEMONIC_JO: cc = 0; break; case ZYDIS_MNEMONIC_JNO: cc = 1; break; case ZYDIS_MNEMONIC_JB: cc = 2; break; case ZYDIS_MNEMONIC_JNB: cc = 3; break;
    case ZYDIS_MNEMONIC_JZ: cc = 4; break; case ZYDIS_MNEMONIC_JNZ: cc = 5; break; case ZYDIS_MNEMONIC_JBE: cc = 6; break; case ZYDIS_MNEMONIC_JNBE: cc = 7; break;
    case ZYDIS_MNEMONIC_JS: cc = 8; break; case ZYDIS_MNEMONIC_JNS: cc = 9; break; case ZYDIS_MNEMONIC_JP: cc = 10; break; case ZYDIS_MNEMONIC_JNP: cc = 11; break;
    case ZYDIS_MNEMONIC_JL: cc = 12; break; case ZYDIS_MNEMONIC_JNL: cc = 13; break; case ZYDIS_MNEMONIC_JLE: cc = 14; break; default: cc = 15; break;
    }
    u8* jt = a.jcc(cc, a.p);
    bodyEnd = a.p;
    exitTo(X_LINK, j.next, mk, cov);
    Asm::patch(jt, a.p);
    exitTo(X_LINK, j.target, mk, cov < 0 ? -1 : cov + 1);
  } else { bodyEnd = a.p; exitTo((u8)endKind, endTarget, mk, -1, endWhy); }
  (void)bodyEnd;
  // the calls of the helper, one per site and kind
  std::sort(fix.begin(), fix.end(), [](const Fix& p, const Fix& q) { return p.code < q.code; });
  for (size_t i = 0; i < fix.size();) {
    u8* stub = a.p; a.pushI(fix[i].code); a.jmp(VU ? bailV : bailG);
    size_t k = i; for (; k < fix.size() && fix[k].code == fix[i].code; k++) Asm::patch(fix[k].at, stub);
    i = k;
  }
  f->end = a.p; code = a.p;
  frags.push_back(f);
  st.fragments++; st.insCompiled += n; st.codeBytes += (u64)(f->end - f->entry);
  return f;
}

namespace {
// do the flags hold an expression (or a constant which came from one: the interpreter keeps count of those)?
bool flagsSym(const Flags& f) {
  if (f.folded & A6) return true;
  const u32 lz = f.lazy & A6, pv = f.prev.lazy & A6 & ~lz;
  if (lz && (f.sa | f.sb | f.sr | f.sx)) return true;
  if (pv && (f.prev.sa | f.prev.sb | f.prev.sr | f.prev.sx)) return true;
  static const int pos[6] = {0, 2, 4, 6, 7, 11};
  for (int p : pos) if (!((lz | pv) & (1u << p)) && f.sym[p]) return true;
  return false;
}
}  // namespace

u64 Jit::run(u64 budget, Block* b) {
  if (E.covOn != withCov) { flushCode(); withCov = E.covOn; }
  u64 mask = (u64)(E.vsym & 0xffff) << M_VEC;
  for (int r = 0; r < 16; r++) if (E.gs[r]) mask |= 1ull << r;
  if (flagsSym(E.fl)) mask |= M_FLAGS;
  Frag* f;
  if (b->fragEpoch == epoch && b->fragMask == mask) f = (Frag*)b->frag;
  else {
    auto it = map.find(Key{E.rip, mask});
    if (it != map.end()) f = it->second;
    else {
      // Compiling an instruction costs about as much as interpreting it payK times (measured: 0.8 us against some
      // 100 cycles): code which runs less often than that does not pay it back. Past a credit, new fragments are made
      // only as fast as the instructions run natively so far have paid for the ones compiled: the block is asked
      // again after jitHot more runs.
      if (st.insCompiled * payK > st.ins + payCredit) { b->hits = 0; st.deferred++; return 0; }
      const u32 e0 = epoch; f = compile(E.rip, mask); if (epoch == e0) map[Key{E.rip, mask}] = f;
    }
    b->frag = f; b->fragMask = mask; b->fragEpoch = epoch;
  }
  if (!f || f->cold || budget < f->n || (E.mxcsr & ~0xffffu)) return 0;
  memcpy(S->g, E.g, sizeof S->g);
  S->rflags = ((mask & M_FLAGS) ? (E.fl.bits & FL_DF) : (E.rflags() & (A6 | FL_DF))) | 0x202;
  S->budget = (i64)budget; S->fsbase = E.fsbase; S->gsbase = E.gsbase; S->mxcsr = E.mxcsr; S->vecDirty = 0; S->exitId = 0;
  if (anyVec) memcpy(S->v, E.v, sizeof S->v);
  lastCode = ~0ull;
  ((void (*)(void*))enter)(f->entry);
  const u32 id = (u32)S->exitId;
  u64 rip, now; u32 refund = 0;
  if (id & BAIL) {
    const u32 c = id & ~BAIL; const Site& s = sites[c >> 2];
    if ((c & 3) == 3) { rip = s.f->rip; now = s.f->mask; refund = s.f->n; } else { rip = s.addr; now = s.mask; refund = s.f->n - s.index; }
    if (whyOn) why[(c & 3) == 3 ? 5 * 4096 : 4 * 4096 + ((c & 3) == 2 ? 6 : failWhy)]++;
    if (whyOn && (c & 3) == 2 && why[4 * 4096 + 6] <= 6) fprintf(stderr, "jit fault at %llx: %s (host %llx, code %x)%c", (unsigned long long)s.addr, E.disasm(s.addr).c_str(), (unsigned long long)S->hctx[15], (unsigned)faultWhat, 10);
    st.exits[0]++;
  } else {
    ExitRec& x = exits[id]; now = x.mask; rip = x.kind == X_IBL ? S->target : x.target; st.exits[x.kind]++;
    if (whyOn && x.kind == X_INTERP) why[x.why]++;
    if (x.kind == X_LINK && x.patch) {                  // the target has a fragment by now: the exit jumps there from now on
      auto it = map.find(Key{x.target, x.mask});
      if (it != map.end() && it->second) { Asm::patch(x.patch, it->second->entry); x.patch = nullptr; }
    } else if (x.kind == X_IBL && rip < (1ull << 48)) {
      auto it = map.find(Key{rip, x.mask});
      if (it != map.end() && it->second) {
        const u32 i = (u32)(rip & (IBLN - 1));
        if (!ibl[2 * i]) iblFilled.push_back(i);
        ibl[2 * i] = ~(rip + ((u64)idOf(x.mask) << 48)); ibl[2 * i + 1] = (u64)(uintptr_t)it->second->entry;
      }
    }
  }
  // the guest's state, back in the engine
  memcpy(E.g, S->g, sizeof S->g);
  for (u64 gone = mask & ~now & 0xffff; gone; gone &= gone - 1) { unsigned long r; _BitScanForward64(&r, gone); E.gs[r] = 0; }
  if (!(now & M_FLAGS)) { E.fl = Flags{}; E.fl.bits = (S->rflags & (A6 | FL_DF)) | 0x202; }
  else E.fl.bits = (E.fl.bits & ~(u64)FL_DF) | (S->rflags & FL_DF);
  E.mxcsr = S->mxcsr;
  if (S->vecDirty) memcpy(E.v, S->v, sizeof S->v);
  const u64 done = budget - (u64)S->budget - refund;
  E.icount += done; E.rip = rip; E.jitIns += done; E.jitRuns++;
  st.runs++; st.ins += done;
  f->insSum += done;
  if (++f->entries == 32) { if (f->insSum < 32 * 6) f->cold = true; }     // entering it costs more than it runs
  if (oom) { oom = false; throw std::bad_alloc(); }
  return done;
}

Jit* jitCreate(Engine& E) {
  jitCalibrate();
  Jit* j = new Jit(E);
  if (!j->init()) { delete j; return nullptr; }
  return j;
}

void jitDestroy(Jit* j) {
  if (j->whyOn) {
    std::vector<std::pair<u64, u32>> v; for (auto& kv : j->why) v.push_back({kv.second, kv.first});
    std::sort(v.rbegin(), v.rend());
    static const char* kinds[6] = {"not compiled", "operand with an expression", "not encodable", "not code / watched address", "memory", "budget"};
    static const char* mems[8] = {"", "across pages", "no page", "write to a code page", "bytes with expressions", "again", "fault", ""};
    fprintf(stderr, "jit exits to the interpreter:");
    for (size_t i = 0; i < v.size() && i < 14; i++) fprintf(stderr, " [%s %s: %llu]", kinds[v[i].second / 4096], v[i].second / 4096 == 4 ? mems[v[i].second % 8] : v[i].second / 4096 >= 3 ? "" : ZydisMnemonicGetString((ZydisMnemonic)(v[i].second % 4096)), (unsigned long long)v[i].first);
    fprintf(stderr, "%c", 10);
  }
  { std::lock_guard<std::recursive_mutex> g(gLock); gJits.erase(std::remove(gJits.begin(), gJits.end(), j), gJits.end()); }
  for (Frag* f : j->frags) delete f;
  if (j->base) VirtualFree(j->base, 0, MEM_RELEASE);
  delete j;
}

u64 jitRun(Jit* j, Engine& E, u64 budget, Block* b) { (void)E; return j->run(budget, b); }
void jitFlushCode(Jit* j) { j->flushCode(); }
void jitFlushTlb(Jit* j) { j->flushTlb(); }
void jitDrop(Jit* j, u64 pn) { j->drop(pn); }
const JitStats& jitStats(Jit* j) { return j->st; }
void jitSyncCov(Jit* j, Engine& E) {
  for (size_t i = 0; i < j->covKeys.size(); i++) if (j->covB[i] == 1) { if (E.cov.insert(j->covKeys[i]).second && E.covRec) E.covNewRun.push_back(j->covKeys[i]); if (!E.havocked) E.covPlain.insert(j->covKeys[i]); j->covB[i] = 2; }
}

// The interpreter gives the flags the manuals call undefined the values AMD Zen gives them. Generated code runs on
// whatever CPU this is: an instruction whose flags come out differently here is left to the interpreter.
int jitCalibrate(bool verbose) {
  std::lock_guard<std::recursive_mutex> g(gLock);
  static int bad = 0;
  if (gCalibrated) return bad;
  gCalibrated = true;
  static const struct { const char* hex; int div; } tests[] = {
    {"48d3e0", 0}, {"48d3e8", 0}, {"48d3f8", 0}, {"d3e0", 0}, {"66d3e8", 0}, {"d2e0", 0}, {"48c1e005", 0}, {"48c1e805", 0}, {"48c1f805", 0}, {"48d1e0", 0}, {"48d1e8", 0},
    {"480fa4d805", 0}, {"480facd805", 0}, {"480fa5d8", 0}, {"480fadd8", 0}, {"48d3c0", 0}, {"48d3c8", 0}, {"48d3d0", 0}, {"48d3d8", 0}, {"48c1c005", 0}, {"48c1c805", 0},
    {"48c1d005", 0}, {"48c1d805", 0}, {"48f7e3", 0}, {"48f7eb", 0}, {"480fafc3", 0}, {"486bc307", 0}, {"f6e3", 0}, {"48f7f3", 1}, {"48f7fb", 1}, {"f6f3", 2},
    {"480fbcc3", 0}, {"480fbdc3", 0}, {"f3480fbcc3", 0}, {"f3480fbdc3", 0}, {"f3480fb8c3", 0}, {"480fa3d8", 0}, {"480fabd8", 0}, {"480fb3d8", 0}, {"480fbbd8", 0},
    {"480fbae005", 0}, {"4821d8", 0}, {"4809d8", 0}, {"4831d8", 0}, {"4885d8", 0}, {"4801d8", 0}, {"4829d8", 0}, {"4811d8", 0}, {"4819d8", 0}, {"48f7d8", 0},
    {"48ffc0", 0}, {"48ffc8", 0}, {"4839d8", 0}, {"c4e2e0f2c1", 0}, {"c4e2f8f3cb", 0}, {"c4e2f8f3d3", 0}, {"c4e2f8f3db", 0}, {"c4e2e8f5c3", 0}, {"480fb1d9", 0}, {"480fc1d8", 0},
  };
  std::mt19937_64 rng(4242);
  const u64 CODE = 0x10000000ull;
  Engine B, N; B.jitOn = N.jitOn = false;              // (two engines for all the tests: making one costs more than a test)
  for (Engine* e : {&B, &N}) e->map(CODE, 4096);
  for (const auto& t : tests) {
    std::vector<u8> bytes; for (const char* p = t.hex; p[0] && p[1]; p += 2) { unsigned v; sscanf(p, "%2x", &v); bytes.push_back((u8)v); }
    bytes.resize(16, 0x90);
    for (Engine* e : {&B, &N}) { e->writeMem(CODE, bytes.data(), bytes.size()); e->flushBlocks(); }
    const Insn* ip = B.decodeAt(CODE); if (!ip) continue;
    const Insn ins = *ip;
    for (int k = 0; k < 24; k++) {
      static const u64 special[8] = {0, 1, 0x7f, 0x80, 0xffffffffull, 0x8000000000000000ull, ~0ull, 63};
      u64 gv[16]; for (u64& x : gv) x = (rng() % 4 == 0) ? special[rng() % 8] : rng();
      if (rng() % 2) gv[RCX] &= 0x3f;
      if (t.div) { gv[RDX] = 0; gv[RAX] &= t.div == 2 ? 0x7f : 0x3fffffff; gv[RBX] = (gv[RBX] & 0xffff) | 0x101; }
      gv[RSP] = 0x7f0000000000ull;
      const u64 fin = rng() & A6;
      for (Engine* e : {&B, &N}) { memcpy(e->g, gv, sizeof gv); memset(e->gs, 0, sizeof e->gs); e->fl = Flags{}; e->fl.bits = fin | 0x202; e->rip = CODE; }
      const Stop sb = B.run(1);
      if ((sb != ST_NONE && sb != ST_COUNT) || nativeExec(N, ins) != ST_NONE) continue;
      const u64 diff = (B.rflags() ^ N.rflags()) & A6;
      if (diff && !gNever[ins.mn]) {
        gNever[ins.mn] = true; bad++;
        if (verbose) fprintf(stderr, "unshroud: %s sets flags %llx differently on this CPU: not compiled%c", ZydisMnemonicGetString((ZydisMnemonic)ins.mn), (unsigned long long)diff, 10);
      }
    }
  }
  gNever[ZYDIS_MNEMONIC_BEXTR] = true;                 // (its undefined flags are not modelled after this CPU)
  return bad;
}

}  // namespace unshroud
