// Exception tests for unshroud's Windows process layer: each test is u64 tNN(u64 a, u64 b) and returns a value which
// records the way taken (T(d) appends a hex digit). The same DLL runs natively (py/exc_native.py) and in unshroud
// (py/exc_check.py); the results must be equal. Built by build.py (clang-cl and cl, static CRT).
#include <windows.h>
#include <intrin.h>
#include <setjmp.h>
typedef unsigned long long u64;
typedef long long s64;
#define EXPORT extern "C" __declspec(dllexport) __declspec(noinline)
#define NOINLINE __declspec(noinline)
static volatile u64 g;                  // the trace of the current test
static volatile u64 armed;              // what the vectored handler does now
// instructions no compiler writes inside a function: called as code
#pragma section(".text")
__declspec(allocate(".text")) static const unsigned char code_ud2[] = {0x0f, 0x0b, 0xc3};      // ud2; ret
__declspec(allocate(".text")) static const unsigned char code_hlt[] = {0xf4, 0xc3};            // hlt; ret
__declspec(allocate(".text")) static const unsigned char code_int3[] = {0x90, 0xcc, 0xc3};     // nop; int3; ret
typedef void (*code_t)(void);
#define T(d) (g = g * 16 + (d))
// what a test uses after a handler ran lives in memory: clang keeps other values in registers which a fault does not preserve
#define KEEP volatile u64 vb = b; volatile u64 va = a; (void)va

// ---------------------------------------------------------------------------------------- __try / __except
EXPORT u64 t01_av_write(u64 a, u64 b) {       // a write to address 0 when a == 1
  KEEP;
  g = 1;
  __try { if (a == 1) *(volatile int*)0 = 1; T(2); }
  __except (EXCEPTION_EXECUTE_HANDLER) { T(3); }
  return g + vb;
}
static int av_filter(EXCEPTION_POINTERS* p, u64 want) {
  const EXCEPTION_RECORD* r = p->ExceptionRecord;
  T(4);
  if (r->ExceptionCode != EXCEPTION_ACCESS_VIOLATION || r->NumberParameters != 2) return EXCEPTION_CONTINUE_SEARCH;
  T(r->ExceptionInformation[0] & 15);         // 0 read, 1 write
  return r->ExceptionInformation[1] == want ? EXCEPTION_EXECUTE_HANDLER : EXCEPTION_CONTINUE_SEARCH;
}
EXPORT u64 t02_av_read_filter(u64 a, u64 b) { // a read below 0x10000 (address a & 0xfff8); the filter checks the record
  KEEP;
  g = 1; volatile u64 v = 7; const u64 addr = a & 0xfff8;
  __try { v = *(volatile u64*)addr; T(2); }
  __except (av_filter(GetExceptionInformation(), addr)) { T(3); }
  return g * 256 + v + vb;
}
NOINLINE static u64 inner_search(u64 a) {
  __try { if (a & 1) *(volatile int*)8 = 1; T(2); }
  __except (T(5), EXCEPTION_CONTINUE_SEARCH) { T(6); }
  return a * 3;
}
EXPORT u64 t03_search_outer(u64 a, u64 b) {   // the inner filter declines, the caller's handler takes it
  KEEP;
  g = 1; volatile u64 r = 0;
  __try { r = inner_search(a); T(7); }
  __except (GetExceptionCode() == EXCEPTION_ACCESS_VIOLATION ? EXCEPTION_EXECUTE_HANDLER : EXCEPTION_CONTINUE_SEARCH) { T(8); }
  return g * 256 + r + vb;
}
EXPORT u64 t04_continue(u64 a, u64 b) {       // a continuable software exception: the filter continues when a == 7
  KEEP;
  g = 1;
  __try { T(2); RaiseException(0xE0000001, 0, 0, 0); T(3); }
  __except (T(4), a == 7 ? EXCEPTION_CONTINUE_EXECUTION : EXCEPTION_EXECUTE_HANDLER) { T(5); }
  return g + vb;
}
static int code_filter(EXCEPTION_POINTERS* p, volatile u64* out) {
  const EXCEPTION_RECORD* r = p->ExceptionRecord;
  *out = r->ExceptionCode;
  if (r->NumberParameters == 3) *out += r->ExceptionInformation[0] + r->ExceptionInformation[1] * 3 + r->ExceptionInformation[2] * 5;
  return EXCEPTION_EXECUTE_HANDLER;
}
EXPORT u64 t05_raise_args(u64 a, u64 b) {     // RaiseException with arguments: the filter reads them back
  g = 1; volatile u64 seen = 0; ULONG_PTR args[3] = {a, b, a ^ b};
  __try { RaiseException(0xE0001234, EXCEPTION_NONCONTINUABLE, 3, args); T(2); }
  __except (code_filter(GetExceptionInformation(), &seen)) { T(3); }
  return g * 0x100000000ull + seen;
}
EXPORT u64 t06_divide(u64 a, u64 b) {         // divide by zero (b == 0), overflow (a == 1 << 63, b == -1)
  g = 1; volatile s64 q = 0; volatile u64 code = 0; volatile s64 n = (s64)a, dv = (s64)b;
  __try { q = n / dv; T(2); }
  __except (code_filter(GetExceptionInformation(), &code)) { T(3); }
  return g * 0x100000000ull + (code ? code : (u64)q);
}
// ---------------------------------------------------------------------------------------- __try / __finally
NOINLINE static u64 fin_inner(u64 a) {
  volatile u64 r = a + 1;
  __try { T(2); if (a & 1) *(volatile int*)16 = 1; T(3); }
  __finally { T(AbnormalTermination() ? 4 : 5); r += 100; }
  return r;
}
NOINLINE static u64 fin_middle(u64 a) {
  volatile u64 r = 0;
  __try { r = fin_inner(a); T(6); }
  __finally { T(AbnormalTermination() ? 7 : 8); }
  return r * 2;
}
EXPORT u64 t07_finally(u64 a, u64 b) {        // two frames of termination handlers under a handler
  KEEP;
  g = 1; volatile u64 r = 0;
  __try { r = fin_middle(a); T(9); }
  __except (T(10), EXCEPTION_EXECUTE_HANDLER) { T(11); }
  return g * 0x10000 + r + vb;
}
EXPORT u64 t08_nested(u64 a, u64 b) {         // a handler inside a finally inside a handler; the second fault is in the first handler
  KEEP;
  g = 1;
  __try {
    __try {
      __try { if (a & 1) *(volatile int*)0 = 1; T(2); }
      __except (EXCEPTION_EXECUTE_HANDLER) { T(3); if (a & 2) *(volatile int*)0 = 2; T(4); }
    } __finally { T(5); }
  } __except (EXCEPTION_EXECUTE_HANDLER) { T(6); }
  return g + vb;
}
// ---------------------------------------------------------------------------------------- vectored handlers
static LONG CALLBACK veh(EXCEPTION_POINTERS* p) {
  const DWORD code = p->ExceptionRecord->ExceptionCode;
  if (!armed) return EXCEPTION_CONTINUE_SEARCH;
  T(12);
  if (armed == 1 && code == EXCEPTION_BREAKPOINT) { p->ContextRecord->Rip += 1; return EXCEPTION_CONTINUE_EXECUTION; }        // int3: skipped
  if (armed == 2 && code == EXCEPTION_ILLEGAL_INSTRUCTION) { p->ContextRecord->Rip += 2; return EXCEPTION_CONTINUE_EXECUTION; }   // ud2: skipped
  if (armed == 3) return EXCEPTION_CONTINUE_SEARCH;                                                                           // seen, not taken
  if (armed == 4 && code == 0xE0000002) { T(13); return EXCEPTION_CONTINUE_EXECUTION; }
  return EXCEPTION_CONTINUE_SEARCH;
}
static LONG CALLBACK veh2(EXCEPTION_POINTERS* p) { if (armed) T(14); return EXCEPTION_CONTINUE_SEARCH; }
EXPORT u64 t09_int3_skipped(u64 a, u64 b) {   // int3 skipped by a vectored handler (a & 1), else taken by __except
  KEEP;
  g = 1; armed = (a & 1) ? 1 : 3;
  void* volatile h = AddVectoredExceptionHandler(1, veh);
  __try { T(2); __debugbreak(); T(3); }
  __except (EXCEPTION_EXECUTE_HANDLER) { T(4); }
  armed = 0; RemoveVectoredExceptionHandler(h);
  return g + vb;
}
EXPORT u64 t10_ud2_skipped(u64 a, u64 b) {    // ud2 skipped by a vectored handler; two handlers, order: first = veh2 when a & 2
  KEEP;
  g = 1; armed = (a & 1) ? 2 : 3;
  void* volatile h = AddVectoredExceptionHandler(1, veh);
  void* volatile h2 = AddVectoredExceptionHandler((a & 2) ? 1 : 0, veh2);
  __try { T(2); ((code_t)(ULONG_PTR)code_ud2)(); T(3); }
  __except (EXCEPTION_EXECUTE_HANDLER) { T(4); }
  armed = 0; RemoveVectoredExceptionHandler(h); RemoveVectoredExceptionHandler(h2);
  return g + vb;
}
EXPORT u64 t11_veh_continue_raise(u64 a, u64 b) {   // a software exception continued by the vectored handler: the frame handler never sees it
  KEEP;
  g = 1; armed = 4;
  void* volatile h = AddVectoredExceptionHandler(1, veh);
  __try { T(2); RaiseException((a & 1) ? 0xE0000002 : 0xE0000003, 0, 0, 0); T(3); }
  __except (EXCEPTION_EXECUTE_HANDLER) { T(4); }
  armed = 0; RemoveVectoredExceptionHandler(h);
  return g + vb;
}
// ---------------------------------------------------------------------------------------- C++
struct Err { u64 v; };
struct Guard { u64 tag; ~Guard() { T(tag); } };
NOINLINE static u64 thrower(u64 a) {
  Guard gd{2};
  if (a == 1) throw 42;
  if (a == 2) throw Err{a * 1000};
  if (a == 3) throw "text";
  return a + 5;
}
EXPORT u64 t12_cpp_catch(u64 a, u64 b) {      // try / catch by type; a destructor runs while the frames are undone
  g = 1; u64 r = 0;
  try { r = thrower(a); T(3); }
  catch (int e) { T(4); r = (u64)e; }
  catch (const Err& e) { T(5); r = e.v; }
  catch (...) { T(6); r = 9; }
  return g * 0x100000 + r + b;
}
EXPORT u64 t13_cpp_nested_rethrow(u64 a, u64 b) {   // the inner catch rethrows, the outer one takes it by type
  g = 1; u64 r = 0;
  try {
    try { Guard gd{7}; r = thrower(a); T(3); }
    catch (...) { T(8); if (a & 1) throw; r = 1; }
    T(9);
  }
  catch (int e) { T(10); r = (u64)e + 1; }
  catch (...) { T(11); r = 77; }
  return g * 0x100000 + r + b;
}
NOINLINE static u64 mid(u64 a) { Guard gd{12}; u64 r = thrower(a); T(13); return r; }
NOINLINE static u64 mid2(u64 a) { Guard gd{14}; try { return mid(a); } catch (const Err& e) { T(15); if (e.v == 2000) throw Err{e.v + 1}; return 0; } }
EXPORT u64 t14_cpp_deep(u64 a, u64 b) {       // three frames; a catch block throws a new exception
  g = 1; u64 r = 0;
  try { r = mid2(a); T(3); }
  catch (const Err& e) { T(4); r = e.v; }
  catch (int e) { T(5); r = (u64)e; }
  catch (...) { T(6); }
  return g * 0x100000 + r + b;
}
EXPORT u64 t15_cpp_values(u64 a, u64 b) {     // values computed before the throw are used after the catch
  g = 1; u64 x = a * 3 + b, y = (a ^ b) + 17, r;
  try { if (a & 1) throw Err{x}; r = y; }
  catch (const Err& e) { r = e.v + x * 2 + y; T(2); }
  return r + g;
}
// ---------------------------------------------------------------------------------------- others
static jmp_buf jb;
NOINLINE static void jumper(u64 a) { Guard gd{3}; if (a & 1) longjmp(jb, (int)(a & 0xff) + 1); T(4); }
EXPORT u64 t16_longjmp(u64 a, u64 b) {        // longjmp: RtlUnwindEx with a jump buffer
  g = 1; volatile u64 r = b;
  const int k = setjmp(jb);
  if (k == 0) { T(2); jumper(a); T(5); } else { T(6); r += (u64)k; }
  return g * 256 + r;
}
typedef u64 (*fn_t)(u64);
EXPORT u64 t17_null_call(u64 a, u64 b) {      // a call through a null pointer
  KEEP;
  g = 1; volatile fn_t f = (a & 1) ? (fn_t)0 : thrower; volatile u64 r = 0;
  __try { r = f(8); T(2); }
  __except (GetExceptionCode() == EXCEPTION_ACCESS_VIOLATION ? EXCEPTION_EXECUTE_HANDLER : EXCEPTION_CONTINUE_SEARCH) { T(3); }
  return g * 256 + r + vb;
}
NOINLINE static u64 dyn_frame(u64 a) {        // a frame pointer (alloca): the unwinder must use it
  volatile char* p = (volatile char*)_alloca((a & 0xff) + 16); p[0] = (char)a;
  if (a & 1) RaiseException(0xE0000005, 0, 0, 0);
  return (u64)p[0] + 1;
}
EXPORT u64 t18_alloca_frame(u64 a, u64 b) {
  KEEP;
  g = 1; volatile u64 r = 0;
  __try { r = dyn_frame(a); T(2); }
  __except (EXCEPTION_EXECUTE_HANDLER) { T(3); }
  return g * 256 + r + vb;
}
EXPORT u64 t21_privileged(u64 a, u64 b) {     // hlt in user mode; then an int3 reached by a call
  KEEP;
  g = 1; volatile u64 code = 0;
  __try { T(2); if (a & 1) ((code_t)(ULONG_PTR)code_hlt)(); else ((code_t)(ULONG_PTR)code_int3)(); T(3); }
  __except (code = GetExceptionCode(), EXCEPTION_EXECUTE_HANDLER) { T(4); }
  return g * 0x100000000ull + code + vb;
}
EXPORT u64 t19_unhandled_filter(u64 a, u64 b) {     // no handler takes it: only run in unshroud (natively the process would end)
  g = 1; if (a == 0x777) *(volatile int*)0 = 1; return g + a + b;
}
static LONG WINAPI top_filter(EXCEPTION_POINTERS* p) {
  if (p->ExceptionRecord->ExceptionCode == EXCEPTION_BREAKPOINT) { T(9); p->ContextRecord->Rip += 1; return EXCEPTION_CONTINUE_EXECUTION; }
  return EXCEPTION_CONTINUE_SEARCH;
}
EXPORT u64 t20_top_filter(u64 a, u64 b) {     // SetUnhandledExceptionFilter: only run in unshroud (a debugger-free process is needed natively)
  g = 1; LPTOP_LEVEL_EXCEPTION_FILTER old = SetUnhandledExceptionFilter(top_filter);
  T(2); if (a & 1) __debugbreak(); T(3);
  SetUnhandledExceptionFilter(old);
  return g + b;
}
