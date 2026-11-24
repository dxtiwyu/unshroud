// unshroud - models of system functions (see win.hpp). A model reads its arguments, answers from the process in emulated
// memory, and returns to the caller. What it keeps between calls is in emulated memory (WinEnv::STATE).
#include "win.hpp"
#include <cstdio>

namespace unshroud {

namespace {
const u64 STATE = WinEnv::STATE, BIG = WinEnv::BIG, KUSER = WinEnv::KUSER;
u64 M64(u64 v) { return v; }

// n bytes from src to dst, expressions included
void copyMem(Engine& E, u64 dst, u64 src, u64 n) {
  if (dst < 0x10000 || src < 0x10000) return;
  u8 b[4096]; Cell c[4096];
  if (dst > src && dst < src + n) {            // overlapping, forward: from the end
    for (u64 left = n; left;) { const unsigned k = (unsigned)std::min<u64>(left, 4096); left -= k; const bool any = E.loadCells(src + left, k, b, c); E.storeCells(dst + left, k, b, any ? c : nullptr); }
    return;
  }
  for (u64 o = 0; o < n;) { const unsigned k = (unsigned)std::min<u64>(n - o, 4096); const bool any = E.loadCells(src + o, k, b, c); E.storeCells(dst + o, k, b, any ? c : nullptr); o += k; }
}
void fillMem(Engine& E, u64 dst, u8 v, u64 n) {
  if (dst < 0x10000) return;
  u8 b[4096]; memset(b, v, sizeof b);
  for (u64 o = 0; o < n;) { const unsigned k = (unsigned)std::min<u64>(n - o, 4096); E.storeCells(dst + o, k, b, nullptr); o += k; }
}
u64 strLen(Api& a, u64 p, bool wideChars, u64 limit = 1u << 20) {
  if (p < 0x10000) return 0;
  u64 n = 0;
  for (; n < limit; n++) { u16 c = 0; a.E.readMem(p + n * (wideChars ? 2 : 1), &c, wideChars ? 2 : 1); if (!c) break; }
  return n;
}
// the size of an allocation decides whether it succeeds: when it depends on the inputs, both answers are explored (a
// decision of the path, keyed by the call site; its "targets" 1 / 2 are not addresses and are not counted as edges)
bool fits(Api& a, Val size) {
  const bool ok = size.c <= BIG;
  if (size.s && a.W.decideSizes) {
    Ctx& X = a.E.X; const u32 c = X.ule(X.force(size.s), X.cst(BIG, 64));
    a.E.addConstraint(ok ? c : X.not_(c), a.q(a.E.g[RSP]), ok ? 1 : 2, ok ? 2 : 1, 0);
  }
  return ok;
}
// a block with its size in front of it (HeapSize, HeapReAlloc)
u64 heapBlock(Api& a, u64 size) {
  const u64 at = a.alloc(size + 16);
  if (!at) return 0;
  a.putq(at + 8, size);
  return at + 16;
}
u64 blockSize(Api& a, u64 p) { if (p < WinEnv::ALLOC_BASE + 16 || p >= WinEnv::ALLOC_BASE + (1ull << 40)) return 0; return a.q(p - 8); }

// the clock of the process: interrupt time, system time, tick count on the shared page
void advance(Api& a, u64 units) {                       // 100 ns
  const u64 it = a.q(KUSER + 0x08) + units, st = a.q(KUSER + 0x14) + units;
  a.putq(KUSER + 0x08, it); a.putd(KUSER + 0x10, (u32)(it >> 32));
  a.putq(KUSER + 0x14, st); a.putd(KUSER + 0x1c, (u32)(st >> 32));
  a.putq(KUSER + 0x320, it / 156250); a.putd(KUSER + 0x328, (u32)((it / 156250) >> 32));
}
u64 tickMs(Api& a) { return a.q(KUSER + 0x08) / 10000; }

unsigned ctype1(unsigned c) {
  unsigned t = 0;
  if (c >= 'A' && c <= 'Z') t |= 0x101; if (c >= 'a' && c <= 'z') t |= 0x102; if (c >= '0' && c <= '9') t |= 0x84;
  if ((c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f')) t |= 0x80;
  if (c == ' ' || (c >= 9 && c <= 13)) t |= 0x08; if (c == ' ' || c == 9) t |= 0x40;
  if (c < 32 || c == 127) t |= 0x20;
  if ((c >= 33 && c <= 47) || (c >= 58 && c <= 64) || (c >= 91 && c <= 96) || (c >= 123 && c <= 126)) t |= 0x10;
  if (c < 128) t |= 0x200;
  return t;
}
}  // namespace

#define API(n) model(#n, [this](Api& a)

void WinEnv::defaults() {
  // ---------------------------------------------------------------------------------------------- modules
  API(GetModuleHandleW) { const u64 p = a.arg(0); if (p < 0x10000) return a.ret(handleOf(a.E, nullptr)); const std::string n = a.text(p, a.wide); a.ret(handleOf(a.E, &n)); });
  alias("GetModuleHandleA", "GetModuleHandleW");
  API(GetModuleHandleExW) {
    const u64 flags = a.arg(0), name = a.arg(1), out = a.arg(2); u64 h;
    if (flags & 4) { WinModule* m = moduleAt(name); h = m ? m->base : 0; }
    else if (name < 0x10000) h = handleOf(a.E, nullptr);
    else { const std::string n = a.text(name, a.wide); h = handleOf(a.E, &n); }
    a.putq(out, h); a.ret(h ? 1 : 0);
  });
  alias("GetModuleHandleExA", "GetModuleHandleExW");
  API(LoadLibraryW) { const std::string n = a.text(a.arg(0), a.wide); WinModule* m = n.empty() ? nullptr : load(a.E, n); a.ret(m ? m->base : 0); });
  for (const char* n : {"LoadLibraryA", "LoadLibraryExA", "LoadLibraryExW"}) alias(n, "LoadLibraryW");
  API(GetProcAddress) {
    const u64 h = a.arg(0), n = a.arg(1); WinModule* m = moduleAt(h);
    if (!m || n < 0x10000) return a.ret(0);
    a.ret(resolve(a.E, m->name, a.text(n, false)));
  });
  API(LdrLoadDll) { std::string n; WinModule* m = a.ustring(a.arg(2), n) ? load(a.E, n) : nullptr; if (m) a.putq(a.arg(3), m->base); a.ret(m ? 0 : 0xC0000135); });
  API(LdrGetDllHandle) { std::string n; const u64 h = a.ustring(a.arg(2), n) ? handleOf(a.E, &n) : 0; if (h) a.putq(a.arg(3), h); a.ret(h ? 0 : 0xC0000135); });
  API(LdrGetProcedureAddress) {
    WinModule* m = moduleAt(a.arg(0)); std::string n; const u64 p = m && a.astring(a.arg(1), n) ? resolve(a.E, m->name, n) : 0;
    if (p) a.putq(a.arg(3), p);
    a.ret(p ? 0 : 0xC0000139);
  });
  for (const char* n : {"LdrGetProcedureAddressForCaller", "LdrGetProcedureAddressEx"}) alias(n, "LdrGetProcedureAddress");
  API(GetModuleFileNameW) {
    const u64 h = a.arg(0), buf = a.arg(1), size = a.arg(2) & 0xffffffff; WinModule* m = h ? moduleAt(h) : host;
    const std::string path = !m ? "" : m->sample ? "C:\\Users\\user\\" + m->name : m->path;
    const u64 n = std::min<u64>(path.size(), size ? size - 1 : 0);
    if (size) for (u64 i = 0; i <= n; i++) { const u16 c = i < n ? (u8)path[i] : 0; a.put(buf + i * (a.wide ? 2 : 1), &c, a.wide ? 2 : 1); }
    a.ret(n);
  });
  alias("GetModuleFileNameA", "GetModuleFileNameW");
  // ---------------------------------------------------------------------------------------------- memory
  API(VirtualAlloc) { const u64 addr = a.arg(0); if (!fits(a, a.argv(1))) return a.ret(0); a.ret(addr ? addr : a.alloc(a.arg(1), 0x10000)); });
  API(VirtualAllocEx) { const u64 addr = a.arg(1); if (!fits(a, a.argv(2))) return a.ret(0); a.ret(addr ? addr : a.alloc(a.arg(2), 0x10000)); });
  API(NtAllocateVirtualMemory) {
    const u64 pbase = a.arg(1), psize = a.arg(3); u64 base = a.q(pbase); Val size = a.E.load(psize < 0x10000 ? STATE + 0x3f0 : psize, 8);
    if (psize < 0x10000 || pbase < 0x10000) return a.ret(0xC000000D);
    if (!fits(a, size)) return a.ret(0xC0000017);
    if (!base) base = a.alloc(size.c, 0x10000);
    a.putq(pbase, base); a.ret(0);
  });
  alias("ZwAllocateVirtualMemory", "NtAllocateVirtualMemory");
  API(VirtualProtect) { if (a.arg(3)) a.putd(a.arg(3), 0x40); a.ret(1); });
  API(VirtualProtectEx) { if (a.arg(4)) a.putd(a.arg(4), 0x40); a.ret(1); });
  API(NtProtectVirtualMemory) { if (a.arg(4)) a.putd(a.arg(4), 0x40); a.ret(0); });
  alias("ZwProtectVirtualMemory", "NtProtectVirtualMemory");
  API(HeapAlloc) { if (!fits(a, a.argv(2))) return a.ret(0); a.ret(heapBlock(a, a.arg(2))); });
  alias("RtlAllocateHeap", "HeapAlloc");
  API(HeapReAlloc) {
    const u64 old = a.arg(2), size = a.arg(3);
    if (!fits(a, a.argv(3))) return a.ret(0);
    const u64 p = heapBlock(a, size);
    if (p && old >= 0x10000) copyMem(a.E, p, old, std::min<u64>({size, blockSize(a, old) ? blockSize(a, old) : size, 1u << 20}));
    a.ret(p);
  });
  alias("RtlReAllocateHeap", "HeapReAlloc");
  API(HeapFree) { a.ret(1); });
  alias("RtlFreeHeap", "HeapFree");
  API(HeapSize) { const u64 n = blockSize(a, a.arg(2)); a.ret(n ? n : 0x100); });
  alias("RtlSizeHeap", "HeapSize");
  API(malloc) { if (!fits(a, a.argv(0))) return a.ret(0); a.ret(heapBlock(a, a.arg(0))); });
  API(calloc) { const u64 n = a.arg(0) * a.arg(1); if ((a.arg(1) && n / a.arg(1) != a.arg(0)) || n > BIG) return a.ret(0); a.ret(heapBlock(a, n)); });
  API(realloc) {
    const u64 old = a.arg(0), size = a.arg(1);
    if (!fits(a, a.argv(1))) return a.ret(0);
    const u64 p = heapBlock(a, size);
    if (p && old >= 0x10000) copyMem(a.E, p, old, std::min<u64>({size, blockSize(a, old) ? blockSize(a, old) : size, 1u << 20}));
    a.ret(p);
  });
  API(_msize) { a.ret(blockSize(a, a.arg(0))); });
  alias("_malloc_base", "malloc");
  model("LocalAlloc", [this](Api& a) { if (!fits(a, a.argv(1))) return a.ret(0); a.ret(heapBlock(a, a.arg(1))); });
  alias("GlobalAlloc", "LocalAlloc");
  alias("_calloc_base", "calloc"); alias("_realloc_base", "realloc");
  API(GetProcessHeap) { a.ret(HEAP_HANDLE); });
  API(GetSystemInfo) {
    u8 si[48] = {}; auto w = [&](int o, u64 v, int n) { memcpy(si + o, &v, n); };
    w(0, 9, 2); w(4, 0x1000, 4); w(8, 0x10000, 8); w(16, 0x7ffffffeffffull, 8); w(24, 0xff, 8); w(32, 8, 4); w(36, 8664, 4); w(40, 0x10000, 4); w(44, 6, 2); w(46, 0x3a09, 2);
    a.put(a.arg(0), si, sizeof si); a.ret(0);
  });
  alias("GetNativeSystemInfo", "GetSystemInfo");
  // what is at an address: the section of a module, memory the program wrote, or nothing
  auto query = [this](Api& a, u64 addr, u64 buf) {
    u64 mbi[6] = {addr & ~0xfffull, 0, 0, 0x1000, 0x10000, 0};          // BaseAddress, AllocationBase, AllocationProtect, RegionSize, State | Protect, Type
    u32 state = 0x10000, protect = 1, type = 0, aprot = 0;
    if (WinModule* m = moduleAt(addr)) {
      const u64 nt = m->base + a.d(m->base + 0x3c), sec = nt + 0x18 + a.h(nt + 0x14); const unsigned ns = a.h(nt + 6);
      u64 lo = m->base, hi = m->base + 0x1000; protect = 2;
      for (unsigned i = 0; i < ns && i < 96; i++) {
        const u64 va = m->base + a.d(sec + 40 * i + 12), vs = (std::max(a.d(sec + 40 * i + 8), a.d(sec + 40 * i + 16)) + 0xfffull) & ~0xfffull; const u32 ch = a.d(sec + 40 * i + 36);
        if (addr >= va && addr < va + vs) { lo = va; hi = va + vs; protect = (ch & 0x20000000) ? ((ch & 0x80000000) ? 0x40 : 0x20) : (ch & 0x80000000) ? 0x04 : 0x02; }
      }
      mbi[1] = m->base; mbi[3] = hi - (addr & ~0xfffull); state = 0x1000; type = 0x1000000; aprot = 0x80;
    } else if (addr >= 0x10000 && a.E.isMapped(addr)) {
      u64 n = 1; while (n < 256 && a.E.isMapped((addr & ~0xfffull) + n * 0x1000)) n++;
      mbi[1] = addr & ~0xffffull; mbi[3] = n * 0x1000; state = 0x1000; protect = 4; type = 0x20000; aprot = 4;
    }
    mbi[2] = aprot; mbi[4] = state | ((u64)protect << 32); mbi[5] = type;
    a.put(buf, mbi, sizeof mbi);
  };
  model("VirtualQuery", [query](Api& a) { if (a.arg(2) < 0x30) return a.ret(0); query(a, a.arg(0), a.arg(1)); a.ret(0x30); });
  model("VirtualQueryEx", [query](Api& a) { if (a.arg(3) < 0x30) return a.ret(0); query(a, a.arg(1), a.arg(2)); a.ret(0x30); });
  model("NtQueryVirtualMemory", [query](Api& a) {
    if (a.arg(2) != 0 || a.arg(4) < 0x30) return a.ret(0xC0000004);
    query(a, a.arg(1), a.arg(3)); if (a.arg(5)) a.putq(a.arg(5), 0x30); a.ret(0);
  });
  alias("ZwQueryVirtualMemory", "NtQueryVirtualMemory");
  API(memcpy) { copyMem(a.E, a.arg(0), a.arg(1), std::min<u64>(a.arg(2), 1u << 26)); a.ret(a.arg(0)); });
  for (const char* n : {"memmove", "RtlMoveMemory", "RtlCopyMemory"}) alias(n, "memcpy");
  API(memset) { fillMem(a.E, a.arg(0), (u8)a.arg(1), std::min<u64>(a.arg(2), 1u << 26)); a.ret(a.arg(0)); });
  API(RtlFillMemory) { fillMem(a.E, a.arg(0), (u8)a.arg(2), std::min<u64>(a.arg(1), 1u << 26)); a.ret(0); });
  API(RtlZeroMemory) { fillMem(a.E, a.arg(0), 0, std::min<u64>(a.arg(1), 1u << 26)); a.ret(0); });
  API(strlen) { a.ret(strLen(a, a.arg(0), false)); });
  API(wcslen) { a.ret(strLen(a, a.arg(0), true)); });
  alias("lstrlenA", "strlen"); alias("lstrlenW", "wcslen");
  // ---------------------------------------------------------------------------------------------- thread / process
  API(GetLastError) { a.ret(a.d(a.teb() + 0x68)); });
  alias("RtlGetLastWin32Error", "GetLastError");
  API(SetLastError) { a.lastError((u32)a.arg(0)); a.ret(0); });
  alias("RtlSetLastWin32Error", "SetLastError");
  API(TlsAlloc) { const u64 k = a.q(STATE + 8); a.putq(STATE + 8, k + 1); a.ret(k < 64 ? k : 0xffffffff); });
  API(TlsGetValue) { const u64 k = a.arg(0) & 0xffffffff; a.lastError(0); if (k < 64) a.retv(a.E.load(a.teb() + 0x1480 + 8 * k, 8)); else a.ret(0); });
  API(TlsSetValue) { const u64 k = a.arg(0) & 0xffffffff; if (k < 64) a.E.store(a.teb() + 0x1480 + 8 * k, 8, a.argv(1)); a.ret(k < 64 ? 1 : 0); });
  API(FlsAlloc) { const u64 k = a.q(STATE + 0x10); a.putq(STATE + 0x10, k + 1); a.ret(k < 256 ? k : 0xffffffff); });
  API(FlsGetValue) { const u64 k = a.arg(0) & 0xffffffff; if (k < 256) a.retv(a.E.load(a.teb() + (FLS - TEB) + 8 * k, 8)); else a.ret(0); });
  for (const char* n : {"FlsGetValue2", "RtlFlsGetValue2"}) alias(n, "FlsGetValue");
  API(FlsSetValue) { const u64 k = a.arg(0) & 0xffffffff; if (k < 256) a.E.store(a.teb() + (FLS - TEB) + 8 * k, 8, a.argv(1)); a.ret(k < 256 ? 1 : 0); });
  API(GetCurrentProcess) { a.ret(~0ull); });
  API(GetCurrentThread) { a.ret(~0ull - 1); });
  API(GetCurrentProcessId) { a.ret(PID); });
  API(EncodePointer) { a.retv(a.argv(0)); });
  for (const char* n : {"DecodePointer", "RtlEncodePointer", "RtlDecodePointer"}) alias(n, "EncodePointer");
  API(CheckRemoteDebuggerPresent) { a.putd(a.arg(1), 0); a.ret(1); });
  API(NtQueryInformationProcess) {
    const u64 cls = a.arg(1) & 0xffffffff, buf = a.arg(2), n = a.arg(3) & 0xffffffff, out = a.arg(4);
    if (buf >= 0x10000 && n < 0x10000) { std::vector<u8> z(n, 0); a.put(buf, z.data(), n); }
    if (out >= 0x10000) a.putd(out, (u32)n);
    if (cls == 0 && n >= 0x30) { a.putq(buf, 0x103); a.putq(buf + 8, PEB); a.putq(buf + 0x10, 0xff); a.putq(buf + 0x18, 8); a.putq(buf + 0x20, PID); a.putq(buf + 0x28, PID - 0x400); }
    if (cls == 0x1f && n >= 4) a.putd(buf, 1);                        // ProcessDebugFlags: no debugger
    if (cls == 0x1e) return a.ret(0xC0000353);                       // ProcessDebugObjectHandle: none
    a.ret(0);
  });
  alias("ZwQueryInformationProcess", "NtQueryInformationProcess");
  API(IsProcessorFeaturePresent) { const u64 f = a.arg(0) & 0xffffffff; a.ret(f < 64 && features[f] ? 1 : 0); });
  API(GetCommandLineW) { a.ret(commandW); });
  API(GetCommandLineA) { a.ret(commandA); });
  API(GetEnvironmentStringsW) { a.ret(environmentW); });
  API(FreeEnvironmentStringsW) { a.ret(1); });
  model("Ok1", [](Api& a) { a.ret(1); });
  model("Zero", [](Api& a) { a.ret(0); });
  for (const char* n : {"InitializeCriticalSectionAndSpinCount", "InitializeCriticalSectionEx", "TlsFree", "FlsFree", "VirtualFree", "VirtualFreeEx", "CloseHandle",
                        "TryAcquireSRWLockExclusive", "TryAcquireSRWLockShared", "TryEnterCriticalSection", "RtlTryEnterCriticalSection", "FreeLibrary", "AreFileApisANSI",
                        "IsValidCodePage", "HeapValidate", "InitOnceComplete", "FlushInstructionCache", "DisableThreadLibraryCalls", "SetEvent", "ResetEvent",
                        "ReleaseMutex", "HeapSetInformation", "SetHandleInformation", "FlushFileBuffers", "FindClose", "SetConsoleCtrlHandler"}) alias(n, "Ok1");
  for (const char* n : {"EnterCriticalSection", "LeaveCriticalSection", "InitializeCriticalSection", "DeleteCriticalSection", "RtlEnterCriticalSection",
                        "RtlLeaveCriticalSection", "RtlInitializeCriticalSection", "RtlDeleteCriticalSection", "InitializeSListHead", "IsDebuggerPresent", "NtClose",
                        "free", "_free_base", "AcquireSRWLockExclusive", "ReleaseSRWLockExclusive", "AcquireSRWLockShared", "ReleaseSRWLockShared",
                        "RtlAcquireSRWLockExclusive", "RtlReleaseSRWLockExclusive", "RtlAcquireSRWLockShared", "RtlReleaseSRWLockShared", "InitializeSRWLock",
                        "WakeAllConditionVariable", "WakeConditionVariable", "OutputDebugStringA", "OutputDebugStringW", "LocalFree", "GlobalFree",
                        "NtSetInformationThread", "ZwSetInformationThread"}) alias(n, "Zero");
  API(InitOnceBeginInitialize) {
    const u64 once = a.arg(0), pending = a.arg(2), ctx = a.arg(3), v = a.q(once);
    a.putd(pending, (v & 2) ? 0 : 1); if (ctx >= 0x10000 && (v & 2)) a.putq(ctx, v & ~3ull);
    a.ret(1);
  });
  model("InitOnceComplete", [](Api& a) { a.putq(a.arg(0), (a.arg(2) & ~3ull) | 2); a.ret(1); });
  // the initialization runs once: its function is entered in place of this call (what it returns is what the caller gets)
  API(InitOnceExecuteOnce) {
    const u64 once = a.arg(0), fn = a.arg(1), v = a.q(once);
    if ((v & 2) || fn < 0x10000) { if (a.arg(3) >= 0x10000) a.putq(a.arg(3), v & ~3ull); return a.ret(1); }
    a.putq(once, 2); a.E.rip = fn; a.done = true;                    // rcx = once, rdx = parameter, r8 = context: as they are
  });
  alias("RtlRunOnceExecuteOnce", "InitOnceExecuteOnce");
  auto leave = [](Api& a) { a.E.stopInfo = a.name; a.stop = ST_HALT; a.done = true; };
  for (const char* n : {"ExitProcess", "RtlExitUserProcess", "ExitThread", "RtlExitUserThread", "abort", "_exit", "exit", "quick_exit", "_Exit", "FatalExit", "FatalAppExitA", "FatalAppExitW"}) model(n, leave);
  model("TerminateProcess", [leave](Api& a) { if (a.arg(0) == ~0ull) return leave(a); a.ret(1); });
  model("NtTerminateProcess", [leave](Api& a) { if (a.arg(0) == ~0ull || a.arg(0) == 0) return leave(a); a.ret(0); });
  alias("ZwTerminateProcess", "NtTerminateProcess");
  API(GetStartupInfoW) { u8 si[0x68] = {}; si[0] = 0x68; a.put(a.arg(0), si, sizeof si); a.ret(0); });
  alias("GetStartupInfoA", "GetStartupInfoW");
  // ---------------------------------------------------------------------------------------------- random numbers
  // (a generator whose state is in emulated memory: the same bytes on every run from the same state)
  auto randomBytes = [](Api& a, u64 buf, u64 n) {
    u64 s = a.q(STATE + 0x3e0); if (!s) s = 0x9E3779B97F4A7C15ull;
    for (u64 i = 0; i < n && i < (1u << 20); i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; const u8 b = (u8)(s >> 24); a.put(buf + i, &b, 1); }
    a.putq(STATE + 0x3e0, s);
  };
  model("SystemFunction036", [randomBytes](Api& a) { randomBytes(a, a.arg(0), a.arg(1) & 0xffffffff); a.ret(1); });       // RtlGenRandom
  model("ProcessPrng", [randomBytes](Api& a) { randomBytes(a, a.arg(0), a.arg(1)); a.ret(1); });
  model("BCryptGenRandom", [randomBytes](Api& a) { randomBytes(a, a.arg(1), a.arg(2) & 0xffffffff); a.ret(0); });
  model("CryptGenRandom", [randomBytes](Api& a) { randomBytes(a, a.arg(2), a.arg(1) & 0xffffffff); a.ret(1); });
  model("rand_s", [randomBytes](Api& a) { randomBytes(a, a.arg(0), 4); a.ret(0); });
  // ---------------------------------------------------------------------------------------------- time
  API(QueryPerformanceCounter) { advance(a, 100); a.putq(a.arg(0), a.q(KUSER + 0x08) - 26000000000ull); a.ret(1); });   // 0x2540be400 at the start
  for (const char* n : {"NtQueryPerformanceCounter", "RtlQueryPerformanceCounter"}) alias(n, "QueryPerformanceCounter");
  API(QueryPerformanceFrequency) { a.putq(a.arg(0), 10000000); a.ret(1); });
  alias("RtlQueryPerformanceFrequency", "QueryPerformanceFrequency");
  API(GetTickCount) { advance(a, 100); a.ret(a.name == "GetTickCount" ? (u32)tickMs(a) : tickMs(a)); });
  alias("GetTickCount64", "GetTickCount");
  API(GetSystemTimeAsFileTime) { advance(a, 100); a.putq(a.arg(0), a.q(KUSER + 0x14)); a.ret(0); });
  alias("GetSystemTimePreciseAsFileTime", "GetSystemTimeAsFileTime");
  API(NtQuerySystemTime) { advance(a, 100); a.putq(a.arg(0), a.q(KUSER + 0x14)); a.ret(0); });
  API(Sleep) { advance(a, std::max<u64>(1, a.arg(0) & 0xffffffff) * 10000); a.ret(0); yield(a); });
  alias("SleepEx", "Sleep");
  API(NtDelayExecution) { const u64 p = a.arg(1); const i64 t = p >= 0x10000 ? (i64)a.q(p) : 0; advance(a, t < 0 ? (u64)-t : 10000); a.ret(0); yield(a); });
  alias("ZwDelayExecution", "NtDelayExecution");
  API(SleepConditionVariableSRW) { advance(a, 10000); a.ret(1); yield(a); });
  alias("SleepConditionVariableCS", "SleepConditionVariableSRW");
  // ---------------------------------------------------------------------------------------------- system
  API(GetVersion) { a.ret(((u64)(verBuild & 0x7fff) << 16) | (verMinor << 8) | verMajor); });
  API(GetVersionExW) {
    const u64 p = a.arg(0);
    a.putd(p + 4, verMajor); a.putd(p + 8, verMinor); a.putd(p + 12, verBuild); a.putd(p + 16, 2);
    a.ret(a.name == "RtlGetVersion" ? 0 : 1);
  });
  alias("GetVersionExA", "GetVersionExW"); alias("RtlGetVersion", "GetVersionExW");
  API(RtlGetNtVersionNumbers) { a.putd(a.arg(0), verMajor); a.putd(a.arg(1), verMinor); a.putd(a.arg(2), verBuild | 0xf0000000u); a.ret(0); });
  auto dir = [](Api& a, const std::string& s, u64 buf, u64 size) {
    if (size <= s.size()) return a.ret(s.size() + 1);
    for (size_t i = 0; i <= s.size(); i++) { const u16 c = i < s.size() ? (u8)s[i] : 0; a.put(buf + i * (a.wide ? 2 : 1), &c, a.wide ? 2 : 1); }
    a.ret(s.size());
  };
  model("GetSystemDirectoryW", [this, dir](Api& a) { dir(a, systemDir, a.arg(0), a.arg(1) & 0xffffffff); });
  model("GetWindowsDirectoryW", [this, dir](Api& a) { dir(a, rootDir, a.arg(0), a.arg(1) & 0xffffffff); });
  model("GetCurrentDirectoryW", [dir](Api& a) { dir(a, "C:\\Users\\user", a.arg(1), a.arg(0) & 0xffffffff); });
  alias("GetSystemDirectoryA", "GetSystemDirectoryW"); alias("GetWindowsDirectoryA", "GetWindowsDirectoryW"); alias("GetCurrentDirectoryA", "GetCurrentDirectoryW");
  API(GetEnvironmentVariableW) {
    std::string want = a.text(a.arg(0), a.wide); for (char& c : want) if (c >= 'a' && c <= 'z') c -= 32;
    for (u64 p = environmentW; p && a.h(p);) {
      const std::string v = a.text(p, true, 4096); const size_t eq = v.find('=', 1);
      std::string key = v.substr(0, eq); for (char& c : key) if (c >= 'a' && c <= 'z') c -= 32;
      if (eq != std::string::npos && key == want) {
        const std::string val = v.substr(eq + 1); const u64 buf = a.arg(1), size = a.arg(2) & 0xffffffff;
        if (size <= val.size()) return a.ret(val.size() + 1);
        for (size_t i = 0; i <= val.size(); i++) { const u16 c = i < val.size() ? (u8)val[i] : 0; a.put(buf + i * (a.wide ? 2 : 1), &c, a.wide ? 2 : 1); }
        return a.ret(val.size());
      }
      p += 2 * (v.size() + 1);
    }
    a.lastError(203); a.ret(0);
  });
  alias("GetEnvironmentVariableA", "GetEnvironmentVariableW");
  API(GetACP) { a.ret(1252); });
  API(GetOEMCP) { a.ret(437); });
  API(GetCPInfo) { u8 ci[20] = {}; ci[0] = 1; ci[4] = '?'; a.put(a.arg(1), ci, sizeof ci); a.ret(1); });
  API(GetUserDefaultLCID) { a.ret(0x409); });
  for (const char* n : {"GetSystemDefaultLCID", "GetThreadLocale", "GetUserDefaultLangID", "GetSystemDefaultLangID", "GetUserDefaultUILanguage", "GetSystemDefaultUILanguage"}) alias(n, "GetUserDefaultLCID");
  API(RtlInitUnicodeString) {
    const u64 d = a.arg(0), s = a.arg(1), n = std::min<u64>(strLen(a, s, true), 0x7ffe) * 2;
    const u16 v[2] = {(u16)n, (u16)(s >= 0x10000 ? n + 2 : 0)}; a.put(d, v, 4); a.putq(d + 8, s); a.ret(0);
  });
  API(RtlInitAnsiString) {
    const u64 d = a.arg(0), s = a.arg(1), n = std::min<u64>(strLen(a, s, false), 0xfffe);
    const u16 v[2] = {(u16)n, (u16)(s >= 0x10000 ? n + 1 : 0)}; a.put(d, v, 4); a.putq(d + 8, s); a.ret(0);
  });
  // ---------------------------------------------------------------------------------------------- text
  API(MultiByteToWideChar) {
    const u64 src = a.arg(2), dst = a.arg(4); i64 n = (i32)a.arg(3); const i64 room = (i32)a.arg(5);
    if (src < 0x10000) return a.ret(0);
    if (n < 0) n = (i64)strLen(a, src, false) + 1;
    if (room == 0) return a.ret((u64)n);
    if (room < n || n > (1 << 20)) { a.lastError(122); return a.ret(0); }
    for (i64 i = 0; i < n; i++) { u8 b[2] = {0, 0}; Cell c[2] = {}; const bool any = a.E.loadCells(src + i, 1, b, c); c[1] = Cell{0, 0}; a.E.storeCells(dst + 2 * i, 2, b, any ? c : nullptr); }
    a.ret((u64)n);
  });
  API(WideCharToMultiByte) {
    const u64 src = a.arg(2), dst = a.arg(4); i64 n = (i32)a.arg(3); const i64 room = (i32)a.arg(5);
    if (src < 0x10000) return a.ret(0);
    if (n < 0) n = (i64)strLen(a, src, true) + 1;
    if (room == 0) return a.ret((u64)n);
    if (room < n || n > (1 << 20)) { a.lastError(122); return a.ret(0); }
    for (i64 i = 0; i < n; i++) {
      u8 b[2]; Cell c[2]; const bool any = a.E.loadCells(src + 2 * i, 2, b, c);
      if (b[1]) { b[0] = '?'; a.E.storeCells(dst + i, 1, b, nullptr); } else a.E.storeCells(dst + i, 1, b, any ? c : nullptr);
    }
    if (a.arg(7) >= 0x10000) a.putd(a.arg(7), 0);
    a.ret((u64)n);
  });
  API(GetStringTypeW) {
    const u64 src = a.arg(1), out = a.arg(3); i64 n = (i32)a.arg(2);
    if (src < 0x10000 || out < 0x10000) return a.ret(0);
    if (n < 0) n = (i64)strLen(a, src, true) + 1;
    for (i64 i = 0; i < n && i < (1 << 20); i++) { const u16 t = (a.arg(0) & 0xffffffff) == 1 ? (u16)ctype1(a.h(src + 2 * i)) : 0; a.put(out + 2 * i, &t, 2); }
    a.ret(1);
  });
  API(LCMapStringW) {
    const u64 flags = a.arg(1), src = a.arg(2), dst = a.arg(4); i64 n = (i32)a.arg(3); const i64 room = (i32)a.arg(5);
    if (src < 0x10000) return a.ret(0);
    if (n < 0) n = (i64)strLen(a, src, true) + 1;
    if (room == 0) return a.ret((u64)n);
    if (room < n || n > (1 << 20)) { a.lastError(122); return a.ret(0); }
    for (i64 i = 0; i < n; i++) {
      u16 c = a.h(src + 2 * i);
      if ((flags & 0x100) && c >= 'A' && c <= 'Z') c += 32; else if ((flags & 0x200) && c >= 'a' && c <= 'z') c -= 32;
      a.put(dst + 2 * i, &c, 2);
    }
    a.ret((u64)n);
  });
  alias("LCMapStringEx", "LCMapStringW");
  auto compare = [](Api& a, bool wideChars, bool fold, u64 limit) {
    const u64 p = a.arg(0), q = a.arg(1);
    for (u64 i = 0; i < limit; i++) {
      unsigned x = 0, y = 0; a.E.readMem(p + i * (wideChars ? 2 : 1), &x, wideChars ? 2 : 1); a.E.readMem(q + i * (wideChars ? 2 : 1), &y, wideChars ? 2 : 1);
      if (fold) { if (x >= 'A' && x <= 'Z') x += 32; if (y >= 'A' && y <= 'Z') y += 32; }
      if (x != y) return a.ret(x < y ? ~0ull : 1);
      if (!x) break;
    }
    a.ret(0);
  };
  model("strcmp", [compare](Api& a) { compare(a, false, false, 1u << 20); });
  model("wcscmp", [compare](Api& a) { compare(a, true, false, 1u << 20); });
  model("_stricmp", [compare](Api& a) { compare(a, false, true, 1u << 20); });
  model("_wcsicmp", [compare](Api& a) { compare(a, true, true, 1u << 20); });
  model("strncmp", [compare](Api& a) { compare(a, false, false, a.arg(2)); });
  model("wcsncmp", [compare](Api& a) { compare(a, true, false, a.arg(2)); });
  model("_strnicmp", [compare](Api& a) { compare(a, false, true, a.arg(2)); });
  model("_wcsnicmp", [compare](Api& a) { compare(a, true, true, a.arg(2)); });
  alias("lstrcmpA", "strcmp"); alias("lstrcmpW", "wcscmp"); alias("lstrcmpiA", "_stricmp"); alias("lstrcmpiW", "_wcsicmp");
  API(memcmp) {
    const u64 p = a.arg(0), q = a.arg(1), n = std::min<u64>(a.arg(2), 1u << 26);
    for (u64 i = 0; i < n; i++) { u8 x = 0, y = 0; a.E.readMem(p + i, &x, 1); a.E.readMem(q + i, &y, 1); if (x != y) return a.ret(x < y ? ~0ull : 1); }
    a.ret(0);
  });
  API(RtlCompareMemory) {
    const u64 p = a.arg(0), q = a.arg(1), n = std::min<u64>(a.arg(2), 1u << 26); u64 i = 0;
    for (; i < n; i++) { u8 x = 0, y = 0; a.E.readMem(p + i, &x, 1); a.E.readMem(q + i, &y, 1); if (x != y) break; }
    a.ret(i);
  });
}

}  // namespace unshroud
