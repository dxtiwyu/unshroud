// Instructions which trap, fault or read machine state, one at a time: u64 trap(u64 a, u64 b) runs body a (rax = rcx = b on
// entry) under a vectored handler and returns what the handler saw (exception code, where, the context's rip, the
// parameters) or what the body left in eax. The same DLL runs natively (py/trap_native.py) and in unshroud (py/trap_check.py).
// Nothing here can do harm natively: every body faults at this privilege level or only reads.
#include <windows.h>
#include <intrin.h>
#include <string.h>
typedef unsigned long long u64;
#define EXPORT extern "C" __declspec(dllexport) __declspec(noinline)
enum { S = 32, VALUE = 1 };
struct Body { unsigned char flags, len, b[24]; };
static const Body bodies[] = {
  /* 0 icebp */ {0, 1, {0xf1}}, /* 1 int 1 */ {0, 2, {0xcd, 0x01}}, /* 2 int 3, long form */ {0, 2, {0xcd, 0x03}}, /* 3 int3 */ {0, 1, {0xcc}},
  /* 4 int 2d */ {0, 2, {0xcd, 0x2d}}, /* 5 int 2c */ {0, 2, {0xcd, 0x2c}}, /* 6 int 4 */ {0, 2, {0xcd, 0x04}}, /* 7 int 80 */ {0, 2, {0xcd, 0x80}},
  /* 8 int 2a */ {0, 2, {0xcd, 0x2a}}, /* 9 ud2 */ {0, 2, {0x0f, 0x0b}}, /* 10 ud1 */ {0, 3, {0x0f, 0xb9, 0xc0}}, /* 11 ud0 */ {0, 3, {0x0f, 0xff, 0xc0}},
  /* 12 hlt */ {0, 1, {0xf4}}, /* 13 cli */ {0, 1, {0xfa}}, /* 14 sti */ {0, 1, {0xfb}}, /* 15 in al,dx */ {0, 1, {0xec}}, /* 16 out dx,al */ {0, 1, {0xee}},
  /* 17 in al,40 */ {0, 2, {0xe4, 0x40}}, /* 18 insb */ {0, 1, {0x6c}}, /* 19 rdmsr */ {0, 2, {0x0f, 0x32}}, /* 20 wrmsr */ {0, 2, {0x0f, 0x30}},
  /* 21 mov rax,cr0 */ {0, 3, {0x0f, 0x20, 0xc0}}, /* 22 mov rax,dr0 */ {0, 3, {0x0f, 0x21, 0xc0}}, /* 23 mov cr0,rax */ {0, 3, {0x0f, 0x22, 0xc0}},
  /* 24 lgdt */ {0, 5, {0x0f, 0x01, 0x54, 0x24, 0xe0}}, /* 25 lidt */ {0, 5, {0x0f, 0x01, 0x5c, 0x24, 0xe0}}, /* 26 invlpg [rax] */ {0, 3, {0x0f, 0x01, 0x38}},
  /* 27 swapgs */ {0, 3, {0x0f, 0x01, 0xf8}}, /* 28 sysretq */ {0, 3, {0x48, 0x0f, 0x07}}, /* 29 rdpmc */ {0, 2, {0x0f, 0x33}}, /* 30 xgetbv */ {0, 3, {0x0f, 0x01, 0xd0}},
  /* 31 lock nop */ {0, 2, {0xf0, 0x90}}, /* 32 lock add rax,rbx */ {0, 4, {0xf0, 0x48, 0x01, 0xd8}}, /* 33 clts */ {0, 2, {0x0f, 0x06}}, /* 34 invd */ {0, 2, {0x0f, 0x08}},
  /* 35 wbinvd */ {0, 2, {0x0f, 0x09}}, /* 36 lmsw ax */ {0, 3, {0x0f, 0x01, 0xf0}}, /* 37 ltr ax */ {0, 3, {0x0f, 0x00, 0xd8}}, /* 38 lldt ax */ {0, 3, {0x0f, 0x00, 0xd0}},
  /* 39 mov rax,[8000000000000000] */ {0, 10, {0x48, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0x80}},
  /* 40 trap flag: pushfq; or dword [rsp],100h; popfq; nop; nop */ {0, 11, {0x9c, 0x81, 0x0c, 0x24, 0x00, 0x01, 0x00, 0x00, 0x9d, 0x90, 0x90}},
  /* 41 sidt */ {0, 5, {0x0f, 0x01, 0x4c, 0x24, 0xe0}}, /* 42 sgdt */ {0, 5, {0x0f, 0x01, 0x44, 0x24, 0xe0}}, /* 43 sldt eax */ {VALUE, 3, {0x0f, 0x00, 0xc0}},
  /* 44 str eax */ {VALUE, 3, {0x0f, 0x00, 0xc8}}, /* 45 smsw eax */ {VALUE, 3, {0x0f, 0x01, 0xe0}}, /* 46 rdtsc */ {0, 2, {0x0f, 0x31}}, /* 47 rdtscp */ {0, 3, {0x0f, 0x01, 0xf9}},
  /* 48 cpuid */ {0, 4, {0x53, 0x0f, 0xa2, 0x5b}}, /* 49 mov eax,cs */ {VALUE, 2, {0x8c, 0xc8}}, /* 50 ss */ {VALUE, 2, {0x8c, 0xd0}}, /* 51 ds */ {VALUE, 2, {0x8c, 0xd8}},
  /* 52 es */ {VALUE, 2, {0x8c, 0xc0}}, /* 53 fs */ {VALUE, 2, {0x8c, 0xe0}}, /* 54 gs */ {VALUE, 2, {0x8c, 0xe8}}, /* 55 lsl eax,ecx */ {VALUE, 3, {0x0f, 0x03, 0xc1}},
  /* 56 lar eax,ecx */ {VALUE, 3, {0x0f, 0x02, 0xc1}}, /* 57 verr cx; setz al; movzx eax,al */ {VALUE, 9, {0x0f, 0x00, 0xe1, 0x0f, 0x94, 0xc0, 0x0f, 0xb6, 0xc0}},
  /* 58 flags: push 240cd5h; popfq; pushfq; pop rax; push 202h; popfq */ {VALUE, 14, {0x68, 0xd5, 0x0c, 0x24, 0x00, 0x9d, 0x9c, 0x58, 0x68, 0x02, 0x02, 0x00, 0x00, 0x9d}},
  /* 59 flags: push 0; popfq; pushfq; pop rax; push 202h; popfq */ {VALUE, 11, {0x6a, 0x00, 0x9d, 0x9c, 0x58, 0x68, 0x02, 0x02, 0x00, 0x00, 0x9d}},
  /* 60 mov ax,ss; mov ss,ax; icebp */ {0, 6, {0x66, 0x8c, 0xd0, 0x8e, 0xd0, 0xf1}}, /* 61 long nop */ {0, 9, {0x66, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0}},
  /* 62 prefetchw [rax] */ {0, 3, {0x0f, 0x0d, 0x08}}, /* 63 cmpxchg8b eax */ {0, 3, {0x0f, 0xc7, 0xc8}}, /* 64 aaa */ {0, 1, {0x37}}, /* 65 into */ {0, 1, {0xce}},
  /* 66 salc */ {0, 1, {0xd6}}, /* 67 0f 04 */ {0, 2, {0x0f, 0x04}}, /* 68 push es */ {0, 1, {0x06}}, /* 69 pop ss */ {0, 1, {0x17}}, /* 70 pusha */ {0, 1, {0x60}},
  /* 71 aam */ {0, 2, {0xd4, 0x0a}}, /* 72 far jmp */ {0, 7, {0xea, 0, 0, 0, 0, 0, 0}}, /* 73 rdrand eax */ {0, 3, {0x0f, 0xc7, 0xf0}},
  // never run natively (a real system call, a hypervisor, the end of the process): unshroud only
  /* 74 vmcall */ {0, 3, {0x0f, 0x01, 0xc1}}, /* 75 vmmcall */ {0, 3, {0x0f, 0x01, 0xd9}}, /* 76 int 2e */ {0, 2, {0xcd, 0x2e}}, /* 77 syscall */ {0, 2, {0x0f, 0x05}},
  /* 78 sysenter */ {0, 2, {0x0f, 0x34}}, /* 79 int 29 */ {0, 2, {0xcd, 0x29}},
};
static volatile u64 rec_code, rec_addr, rec_rip, rec_np, rec_i0, rec_i1, rec_n, stub_base;
static LONG CALLBACK vh(EXCEPTION_POINTERS* p) {
  const EXCEPTION_RECORD* r = p->ExceptionRecord;
  if (!stub_base) return EXCEPTION_CONTINUE_SEARCH;
  if (rec_n++ == 0) {
    rec_code = r->ExceptionCode; rec_addr = (u64)r->ExceptionAddress - stub_base; rec_rip = p->ContextRecord->Rip - stub_base;
    rec_np = r->NumberParameters; rec_i0 = rec_np > 0 ? r->ExceptionInformation[0] : 0; rec_i1 = rec_np > 1 ? r->ExceptionInformation[1] : 0;
  }
  p->ContextRecord->Rip = stub_base + S - 1;          // the body's ret
  p->ContextRecord->EFlags &= ~0x100u;                // no more single steps
  return EXCEPTION_CONTINUE_EXECUTION;
}
static unsigned char* page; static void* handler;
EXPORT u64 trap(u64 a, u64 b) {
  if (!page) { page = (unsigned char*)VirtualAlloc(0, 4096, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE); handler = AddVectoredExceptionHandler(1, vh); }
  if (!page || a >= sizeof bodies / sizeof bodies[0]) return ~0ull;
  const Body& y = bodies[a];
  unsigned char* s = page + a * S;
  static unsigned char made[128];                                     // written once: run again and again, a body is hot code
  if (!made[a]) {
    made[a] = 1;
    memset(s, 0x90, S); s[0] = 0x48; s[1] = 0x89; s[2] = 0xc8;       // mov rax, rcx
    memcpy(s + 3, y.b, y.len); s[S - 1] = 0xc3;
  }
  rec_n = 0; rec_code = rec_addr = rec_rip = rec_np = rec_i0 = rec_i1 = 0;
  stub_base = (u64)s;
  const u64 r = ((u64 (*)(u64))s)(b);
  stub_base = 0;
  if (!rec_n) return 0x1000000000000000ull | ((y.flags & VALUE) ? (r & 0xffffffffull) : 0);
  return rec_code | (rec_addr & 0xff) << 32 | (rec_rip & 0xff) << 40 | (rec_np & 0xf) << 48 | (rec_i0 & 0xf) << 52 | (u64)(rec_i1 == ~0ull) << 56 | (rec_n > 3 ? 3 : rec_n) << 57;
}
// body a, n times (rax alternates between 0 and 5): what it returns each time, folded
EXPORT u64 hot(u64 a, u64 n) {
  u64 acc = 0;
  for (u64 i = 0; i < n; i++) acc = acc * 31 + trap(a, (i & 1) ? 5 : 0);
  return acc;
}

// ---- trap2: bodies which go on after their exceptions (the handler resumes them where the context says): the trap flag as
// handlers, iretq and mov ss leave it, the flags a handler runs with and sees. The result: up to 4 events (3 bits what,
// 6 bits the context's rip in the body), how many there were, the first event's context TF / DF / RF and the handler's own
// TF / DF, the last event's context TF / RF, and the low 16 bits of rax at the end.
enum { S2 = 64, TRACE = 2, ARM = 4 };    // TRACE: the handler keeps TF on for b more single steps; ARM: it sets TF at the first other exception
struct Body2 { unsigned char flags, off, len, n, b[48]; };   // off / len: an instruction which leaves rip on itself (it is skipped)
#define TFON 0x9c, 0x81, 0x0c, 0x24, 0x00, 0x01, 0x00, 0x00, 0x9d        /* pushfq; or dword [rsp],100h; popfq */
#define FRAME(fl0, fl1, cs) 0x48, 0x89, 0xe2, 0x6a, 0x2b, 0x52, 0x68, fl0, fl1, 0x00, 0x00, 0x6a, cs, 0x48, 0x8d, 0x05, 0x03, 0x00, 0x00, 0x00, 0x50, 0x48, 0xcf
static const Body2 bodies2[] = {
  /* 0 TF traced: TFON; nop; pushfq; popfq; inc eax; nop; inc eax; nop */ {TRACE, 0, 0, 18, {TFON, 0x90, 0x9c, 0x9d, 0xff, 0xc0, 0x90, 0xff, 0xc0, 0x90}},
  /* 1 TFON; ud2; nop; nop */ {0, 9, 2, 13, {TFON, 0x0f, 0x0b, 0x90, 0x90}},
  /* 2 pushfq; or; push qword [rsp]; popfq; popfq; nop; nop; nop */ {0, 0, 0, 16, {0x9c, 0x81, 0x0c, 0x24, 0x00, 0x01, 0x00, 0x00, 0xff, 0x34, 0x24, 0x9d, 0x9d, 0x90, 0x90, 0x90}},
  /* 3 std; ud2; cld */ {0, 1, 2, 4, {0xfd, 0x0f, 0x0b, 0xfc}},
  /* 4 int3 (the handler sets TF); nop; nop; nop */ {ARM, 0, 1, 4, {0xcc, 0x90, 0x90, 0x90}},
  /* 5 TFON; int3; nop; nop */ {0, 9, 1, 12, {TFON, 0xcc, 0x90, 0x90}},
  /* 6 xor eax,eax; mov rax,[rax] */ {0, 2, 3, 5, {0x31, 0xc0, 0x48, 0x8b, 0x00}},
  /* 7 TFON; pushfq; and qword [rsp],~100h; popfq; nop; nop */ {TRACE, 0, 0, 21, {TFON, 0x9c, 0x48, 0x81, 0x24, 0x24, 0xff, 0xfe, 0xff, 0xff, 0x9d, 0x90, 0x90}},
  /* 8 iretq to the next instruction with flags 8d5h; pushfq; pop rax */ {0, 0, 0, 25, {FRAME(0xd5, 0x08, 0x33), 0x9c, 0x58}},
  /* 9 iretq with TF in the frame (302h); nop; nop; nop; xor eax,eax */ {0, 0, 0, 28, {FRAME(0x02, 0x03, 0x33), 0x90, 0x90, 0x90, 0x31, 0xc0}},
  /* 10 iretq to cs 2bh; mov rsp,rdx; xor eax,eax */ {0, 21, 2, 28, {FRAME(0x02, 0x02, 0x2b), 0x48, 0x89, 0xd4, 0x31, 0xc0}},
  /* 11 mov ax,ss; TFON; mov ss,ax; nop; nop; nop */ {0, 0, 0, 17, {0x66, 0x8c, 0xd0, TFON, 0x8e, 0xd0, 0x90, 0x90, 0x90}},
  /* 12 xor ecx,ecx; mov ss,[rcx] */ {0, 2, 2, 4, {0x31, 0xc9, 0x8e, 0x11}},
  /* 13 mov dx,ss; mov eax,ecx; mov ss,ax; mov eax,ss; mov ss,dx */ {0, 5, 2, 11, {0x66, 0x8c, 0xd2, 0x89, 0xc8, 0x8e, 0xd0, 0x8c, 0xd0, 0x8e, 0xd2}},
  /* 14 mov ax,ss; push 302h; popfq (TF); mov ss,ax; pushfq; pop rax */ {0, 0, 0, 13, {0x66, 0x8c, 0xd0, 0x68, 0x02, 0x03, 0x00, 0x00, 0x9d, 0x8e, 0xd0, 0x9c, 0x58}},
  /* 15 int 4 */ {0, 0, 2, 4, {0xcd, 0x04, 0x90, 0x90}},
  /* 16 int 2c */ {0, 0, 2, 4, {0xcd, 0x2c, 0x90, 0x90}},
  /* 17 int 1 (cd 01) */ {0, 0, 2, 4, {0xcd, 0x01, 0x90, 0x90}},
  /* 18 icebp */ {0, 0, 1, 3, {0xf1, 0x90, 0x90}},
  /* 19 hlt */ {0, 0, 1, 3, {0xf4, 0x90, 0x90}},
  /* 20 xor ecx,ecx; div ecx */ {0, 2, 2, 6, {0x31, 0xc9, 0xf7, 0xf1, 0x90, 0x90}},
  /* 21 int 3 (cd 03): its rip is one byte back from its end */ {0, 1, 1, 4, {0xcd, 0x03, 0x90, 0x90}},
  /* 22 int 2d (rax 0) */ {0, 0, 2, 5, {0xcd, 0x2d, 0x90, 0x90, 0x90}},
  /* 23 int3 */ {0, 0, 1, 3, {0xcc, 0x90, 0x90}},
};
static volatile u64 s2_base, s2_ev, s2_n, s2_first, s2_last, s2_budget; static volatile unsigned char s2_flags, s2_off, s2_len, s2_armed;
static u64 kindOf(DWORD c) {
  switch (c) {
  case 0x80000004: return 1; case 0x80000003: return 2; case 0xC000001D: return 3; case 0xC0000005: return 4; case 0xC0000096: return 5;
  case 0xC0000094: case 0xC0000095: return 6; default: return 7;
  }
}
static LONG CALLBACK vh2(EXCEPTION_POINTERS* p) {
  if (!s2_base) return EXCEPTION_CONTINUE_SEARCH;
  CONTEXT* c = p->ContextRecord; const DWORD code = p->ExceptionRecord->ExceptionCode;
  const u64 hf = __readeflags();
  const u64 at = c->Rip - s2_base, off = at < S2 ? at : 63, n = s2_n++, cf = c->EFlags;
  if (n < 4) s2_ev |= (kindOf(code) | off << 3) << (9 * n);
  if (n == 0) s2_first = (cf >> 8 & 1) | (cf >> 10 & 1) << 1 | (cf >> 16 & 1) << 2 | (hf >> 8 & 1) << 3 | (hf >> 10 & 1) << 4;
  s2_last = (cf >> 8 & 1) | (cf >> 16 & 1) << 1;
  if (n >= 12) { c->EFlags &= ~0x100u; if (at < S2) c->Rip = s2_base + S2 - 1; return EXCEPTION_CONTINUE_EXECUTION; }   // (a storm)
  if (code == 0x80000004) {
    if ((s2_flags & TRACE) && s2_budget) { s2_budget = s2_budget - 1; c->EFlags |= 0x100u; } else c->EFlags &= ~0x100u;
  } else {
    if (s2_len && at == 3u + s2_off) c->Rip += s2_len;
    if ((s2_flags & ARM) && !s2_armed) { s2_armed = 1; c->EFlags |= 0x100u; }
  }
  return EXCEPTION_CONTINUE_EXECUTION;
}
static unsigned char* page2;
EXPORT u64 trap2(u64 a, u64 b) {
  if (!page2) { page2 = (unsigned char*)VirtualAlloc(0, 4096, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE); AddVectoredExceptionHandler(1, vh2); }
  if (!page2 || a >= sizeof bodies2 / sizeof bodies2[0]) return ~0ull;
  const Body2& y = bodies2[a];
  unsigned char* s = page2 + a * S2;
  static unsigned char made2[64];
  if (!made2[a]) {
    made2[a] = 1;
    memset(s, 0x90, S2); s[0] = 0x48; s[1] = 0x89; s[2] = 0xc8;       // mov rax, rcx
    memcpy(s + 3, y.b, y.n); s[S2 - 1] = 0xc3;
  }
  s2_ev = s2_n = s2_first = s2_last = 0; s2_armed = 0; s2_flags = y.flags; s2_off = y.off; s2_len = y.len; s2_budget = b;
  s2_base = (u64)s;
  const u64 r = ((u64 (*)(u64))s)(b);
  s2_base = 0;
  return s2_ev | (s2_n > 15 ? 15 : s2_n) << 36 | s2_first << 40 | s2_last << 45 | (r & 0xffff) << 48;
}
// body a of trap2, n times (b = 0): what it returns each time, folded
EXPORT u64 hot2(u64 a, u64 n) {
  u64 acc = 0;
  for (u64 i = 0; i < n; i++) acc = acc * 31 + trap2(a, 0);
  return acc;
}

// ---- trap3: hardware breakpoints. The handler arms DR0-3 / DR7 (the body's) at the first int3 of the body, disarms them at
// its last byte (an int3), and records every exception: what, where (the context's rip and the record's address), RF, and
// the context's DR6 / DR7 / DR0 / DR1. rdx points at 16 bytes of data (zeros) which the bodies use.
// trap3(a, b, k): k = 0: the events (as trap2) and rax; 1..6: event k-1 (what, rip, address, RF, DR6 low, DR7);
// 7..12: event k-7 (DR6 high, DR0 and DR1 as where they point); 13: what GetThreadContext gave after SetThreadContext
enum { S3 = 64, RFSKIP = 1, DISARM = 2, TFARM = 4, SETCTX = 8 };
struct Dr3 { unsigned char area, off; };      // area: 0 none, 1 the data (+off), 2 the body (+off), 3 a kernel address
struct Body3 { unsigned char flags, n; unsigned dr7; Dr3 dr[4]; unsigned char b[40]; };
static const Body3 bodies3[] = {
  /* 0 write, len 1: int3; mov byte [rdx],1; nop; int3 */ {0, 6, 0x00010001, {{1, 0}}, {0xcc, 0xc6, 0x02, 0x01, 0x90, 0xcc}},
  /* 1 write, len 4; mov word [rdx+2],1 */ {0, 9, 0x000d0001, {{1, 0}}, {0xcc, 0x66, 0xc7, 0x42, 0x02, 0x01, 0x00, 0x90, 0xcc}},
  /* 2 write only; mov al,[rdx] */ {0, 5, 0x00010001, {{1, 0}}, {0xcc, 0x8a, 0x02, 0x90, 0xcc}},
  /* 3 read/write; mov al,[rdx] */ {0, 5, 0x00030001, {{1, 0}}, {0xcc, 0x8a, 0x02, 0x90, 0xcc}},
  /* 4 write, len 8; mov byte [rdx+7],1 */ {0, 7, 0x00090001, {{1, 0}}, {0xcc, 0xc6, 0x42, 0x07, 0x01, 0x90, 0xcc}},
  /* 5 write, len 4 at +3; mov byte [rdx],1 */ {0, 6, 0x000d0001, {{1, 3}}, {0xcc, 0xc6, 0x02, 0x01, 0x90, 0xcc}},
  /* 6 execute (inc eax), the handler sets RF */ {RFSKIP, 6, 0x00000001, {{2, 2}}, {0xcc, 0x90, 0xff, 0xc0, 0x90, 0xcc}},
  /* 7 execute, the handler disarms */ {DISARM, 6, 0x00000001, {{2, 2}}, {0xcc, 0x90, 0xff, 0xc0, 0x90, 0xcc}},
  /* 8 execute, the handler does nothing */ {0, 6, 0x00000001, {{2, 2}}, {0xcc, 0x90, 0xff, 0xc0, 0x90, 0xcc}},
  /* 9 two at once; mov word [rdx],101h */ {0, 8, 0x00110005, {{1, 0}, {1, 1}}, {0xcc, 0x66, 0xc7, 0x02, 0x01, 0x01, 0x90, 0xcc}},
  /* 10 single step and a write in one instruction */ {TFARM, 6, 0x00010001, {{1, 0}}, {0xcc, 0xc6, 0x02, 0x01, 0x90, 0xcc}},
  /* 11 global enable only */ {0, 6, 0x00010002, {{1, 0}}, {0xcc, 0xc6, 0x02, 0x01, 0x90, 0xcc}},
  /* 12 a kernel address in DR0 */ {0, 4, 0x00010001, {{3, 0}}, {0xcc, 0x90, 0x90, 0xcc}},
  /* 13 DR7 555503ffh, DR0-3 zero */ {0, 4, 0x555503ff, {}, {0xcc, 0x90, 0x90, 0xcc}},
  /* 14 DR0 set, no enable */ {0, 4, 0x00000000, {{1, 0}}, {0xcc, 0x90, 0x90, 0xcc}},
  /* 15 mov word [rdx],2bh; int3; mov ss,[rdx] (read/write, len 2); nop; nop; int3 */
  {0, 11, 0x00070001, {{1, 0}}, {0x66, 0xc7, 0x02, 0x2b, 0x00, 0xcc, 0x8e, 0x12, 0x90, 0x90, 0xcc}},
  /* 16 the same with int3 after mov ss (unshroud only: the CPU delivers the held #DB in the kernel's int3 entry) */
  {0, 11, 0x00070001, {{1, 0}}, {0x66, 0xc7, 0x02, 0x2b, 0x00, 0xcc, 0x8e, 0x12, 0xcc, 0x90, 0xcc}},
  /* 17 armed by SetThreadContext (write, len 1): mov byte [rdx],1; nop; int3 */ {SETCTX, 5, 0, {}, {0xc6, 0x02, 0x01, 0x90, 0xcc}},
  /* 18 write at +3 inside rep stosb: int3; mov rdi,rdx; mov ecx,8; xor eax,eax; rep stosb; nop; int3 */
  {0, 15, 0x00010001, {{1, 3}}, {0xcc, 0x48, 0x89, 0xd7, 0xb9, 0x08, 0x00, 0x00, 0x00, 0x31, 0xc0, 0xf3, 0xaa, 0x90, 0xcc}},
};
static unsigned char *page3, *dpage3;
static volatile u64 s3_base, s3_n, s3_ctx; static const Body3* volatile s3_body; static volatile unsigned char s3_armed;
static u64 e3[6][2];
static u64 rel3(u64 x) {
  if (!x) return 0;
  if (x >= (u64)dpage3 && x < (u64)dpage3 + 4096) return 0x100000 | (x - (u64)dpage3);
  if (x >= (u64)page3 && x < (u64)page3 + 4096) return 0x200000 | (x - (u64)page3);
  return 0xffffff;
}
static void disarm3(CONTEXT* c) { c->ContextFlags |= CONTEXT_DEBUG_REGISTERS; c->Dr0 = c->Dr1 = c->Dr2 = c->Dr3 = 0; c->Dr6 = 0; c->Dr7 = 0; }
static LONG CALLBACK vh3(EXCEPTION_POINTERS* p) {
  if (!s3_base) return EXCEPTION_CONTINUE_SEARCH;
  CONTEXT* c = p->ContextRecord; const DWORD code = p->ExceptionRecord->ExceptionCode; const Body3& y = *s3_body;
  const u64 at = c->Rip - s3_base, off = at < S3 ? at : 63, ea = (u64)p->ExceptionRecord->ExceptionAddress - s3_base, eoff = ea < S3 ? ea : 63;
  const u64 n = s3_n++;
  if (n < 6) {
    e3[n][0] = kindOf(code) | off << 3 | eoff << 9 | (u64)(c->EFlags >> 16 & 1) << 15 | (c->Dr6 & 0xffff) << 16 | (c->Dr7 & 0xffffffffull) << 32;
    e3[n][1] = (c->Dr6 >> 16 & 0xffff) | rel3(c->Dr0) << 16 | rel3(c->Dr1) << 40;
  }
  if (n >= 12) { disarm3(c); c->EFlags &= ~0x100u; if (at < S3) c->Rip = s3_base + S3 - 1; return EXCEPTION_CONTINUE_EXECUTION; }   // (a storm)
  if (code == 0x80000003) {
    if (at == 3u + y.n - 1) disarm3(c);
    else if (!s3_armed) {
      s3_armed = 1; c->ContextFlags |= CONTEXT_DEBUG_REGISTERS;
      DWORD64* d[4] = {&c->Dr0, &c->Dr1, &c->Dr2, &c->Dr3};
      for (int i = 0; i < 4; i++) *d[i] = y.dr[i].area == 1 ? (u64)dpage3 + 0x100 + y.dr[i].off : y.dr[i].area == 2 ? s3_base + 3 + y.dr[i].off : y.dr[i].area == 3 ? 0xfffff80000000000ull + y.dr[i].off : 0;
      c->Dr7 = y.dr7;
      if (y.flags & TFARM) c->EFlags |= 0x100u;
    }
    c->Rip += 1;
    return EXCEPTION_CONTINUE_EXECUTION;
  }
  if (code == 0x80000004) {
    c->EFlags &= ~0x100u;
    if (y.flags & RFSKIP) c->EFlags |= 0x10000u;
    if (y.flags & DISARM) disarm3(c);
    return EXCEPTION_CONTINUE_EXECUTION;
  }
  disarm3(c); if (at < S3) c->Rip = s3_base + S3 - 1;
  return EXCEPTION_CONTINUE_EXECUTION;
}
EXPORT u64 trap3(u64 a, u64 b, u64 k) {
  if (!page3) {
    page3 = (unsigned char*)VirtualAlloc(0, 4096, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
    dpage3 = (unsigned char*)VirtualAlloc(0, 4096, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    AddVectoredExceptionHandler(1, vh3);
  }
  if (!page3 || !dpage3 || a >= sizeof bodies3 / sizeof bodies3[0]) return ~0ull;
  const Body3& y = bodies3[a];
  unsigned char* s = page3 + a * S3;
  static unsigned char made3[64];
  if (!made3[a]) {
    made3[a] = 1;
    memset(s, 0x90, S3); s[0] = 0x48; s[1] = 0x89; s[2] = 0xc8;       // mov rax, rcx
    memcpy(s + 3, y.b, y.n); s[S3 - 1] = 0xc3;
  }
  memset(dpage3 + 0x100, 0, 16);
  s3_n = 0; s3_armed = 0; s3_ctx = 0; memset(e3, 0, sizeof e3); s3_body = &y;
  s3_base = (u64)s;
  if (y.flags & SETCTX) {
    CONTEXT c; memset(&c, 0, sizeof c); c.ContextFlags = CONTEXT_DEBUG_REGISTERS; c.Dr0 = (u64)dpage3 + 0x100; c.Dr7 = 0x00010001;
    SetThreadContext(GetCurrentThread(), &c);
    CONTEXT g; memset(&g, 0, sizeof g); g.ContextFlags = CONTEXT_DEBUG_REGISTERS;
    if (GetThreadContext(GetCurrentThread(), &g)) s3_ctx = rel3(g.Dr0) | (g.Dr7 & 0xffffffffull) << 32;
  }
  const u64 r = ((u64 (*)(u64, u64))s)(b, (u64)dpage3 + 0x100);
  s3_base = 0;
  if (k == 0) {
    u64 ev = 0;
    for (u64 i = 0; i < 4 && i < s3_n && i < 6; i++) ev |= (e3[i][0] & 0x1ff) << (9 * i);
    return ev | (s3_n > 15 ? 15 : s3_n) << 36 | (r & 0xffff) << 48;
  }
  if (k <= 6) return e3[k - 1][0];
  if (k <= 12) return e3[k - 7][1];
  return s3_ctx;
}
// body a of trap3, n times (what it returns with k = 0 each time, folded): hot code while breakpoints come and go
EXPORT u64 hot3(u64 a, u64 n) {
  u64 acc = 0;
  for (u64 i = 0; i < n; i++) acc = acc * 31 + trap3(a, 0, 0);
  return acc;
}
