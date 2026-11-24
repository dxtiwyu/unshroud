// unshroud - threads of the process (see win.hpp). One thread runs at a time; the others wait in CONTEXT records in emulated
// memory. A thread gives way when it sleeps, waits or yields (cooperative: no time slices), and when it ends. A thread a
// run creates lives in that run's memory only: every run of the explorer starts from the threads of the saved state.
#include "win.hpp"
#include <cstdio>

namespace unshroud {

namespace {
const u64 STATE = WinEnv::STATE, TEB0 = WinEnv::TEB, STEP = 0x10000000ull;
// STATE + 0x400: the running thread, + 0x408: how many; then 0x40 bytes per thread:
enum : u64 { T_CUR = 0x400, T_COUNT = 0x408, T_TAB = 0x410, T_SIZE = 0x40, T_STATE = 0, T_TEB = 8, T_CTX = 0x10, T_HANDLE = 0x18, T_EXIT = 0x20, T_WAIT = 0x28, T_MAX = 8 };
enum : u64 { TS_NONE = 0, TS_READY = 1, TS_DONE = 2, TS_WAITING = 3, TS_SUSPENDED = 4 };
u64 rec(u64 k) { return STATE + T_TAB + T_SIZE * k; }
u64 count(Api& a) { const u64 n = a.q(STATE + T_COUNT); return n ? std::min<u64>(n, T_MAX) : 1; }   // (a state saved before any thread was made: the first one only)
u64 current(Api& a) { return a.q(STATE + T_CUR) % T_MAX; }
u64 stateOf(Api& a, u64 k) { return k == 0 && !a.q(STATE + T_COUNT) ? (u64)TS_READY : a.q(rec(k) + T_STATE); }
int byHandle(Api& a, u64 h) { for (u64 k = 1; k < count(a); k++) if (a.q(rec(k) + T_HANDLE) == h) return (int)k; return -1; }
}  // namespace

// the first thread's record, when the first other thread is made
static void ensureMain(Api& a) {
  if (a.q(STATE + T_COUNT)) return;
  a.putq(STATE + T_COUNT, 1); a.putq(STATE + T_CUR, 0);
  a.putq(rec(0) + T_STATE, TS_READY); a.putq(rec(0) + T_TEB, TEB0); a.putq(rec(0) + T_CTX, TEB0 + 0x4e0000); a.putq(rec(0) + T_HANDLE, 0x7fc);
}

// The thread which runs next: the first one after `from` which is ready (a thread waiting for one which ended is ready).
static int nextReady(Api& a, u64 from) {
  const u64 n = count(a);
  for (u64 i = 1; i <= n; i++) {
    const u64 k = (from + i) % n; const u64 s = stateOf(a, k);
    if (s == TS_WAITING) { const u64 t = a.q(rec(k) + T_WAIT) & 0xff; if (t < n && stateOf(a, t) == TS_DONE) { a.putq(rec(k) + T_STATE, TS_READY); return (int)k; } }
    if (s == TS_READY && k != from) return (int)k;
  }
  return -1;
}

// The running thread (already back in its caller, with its result in rax) gives way to thread `to`.
void WinEnv::switchThread(Api& a, int to, bool saveCurrent) {
  const u64 cur = current(a);
  if (saveCurrent) saveContext(a.E, a.q(rec(cur) + T_CTX));
  loadContext(a.E, a.q(rec(to) + T_CTX));
  a.E.gsbase = a.q(rec(to) + T_TEB);
  a.putq(STATE + T_CUR, (u64)to);
  a.done = true;
}

u64 WinEnv::createThread(Api& a, u64 start, u64 arg, bool suspended, u64* tid) {
  ensureMain(a);
  const u64 k = a.q(STATE + T_COUNT);
  if (k >= T_MAX || start < 0x10000) return 0;
  Engine& E = a.E;
  const u64 teb = TEB0 + k * STEP, top = STACK_TOP - k * STEP, tls = teb + (TLS - TEB0), ctx = teb + 0x4e0000;
  // the thread's blocks: TEB, stack, its copy of the TLS template (as the first thread's)
  const std::pair<u64, u64> f[] = {{0x08, top}, {0x10, top - STACK_SIZE}, {0x20, 0x1e00}, {0x30, teb}, {0x40, PID}, {0x48, TID + 4 * k}, {0x58, tls}, {0x60, PEB}, {0x1478, top - STACK_SIZE}};
  { std::vector<u8> z(0x1800, 0); E.writeMem(teb, z.data(), z.size()); }
  for (auto& kv : f) a.putq(teb + kv.first, kv.second);
  a.putd(teb + 0x108, 0x409);
  if (sample && sample->hasTls) {
    const u64 n = sample->tlsEnd > sample->tlsStart ? std::min<u64>(sample->tlsEnd - sample->tlsStart, 1u << 24) : 0;
    std::vector<u8> t((size_t)n + sample->tlsFill + 0x40, 0); if (n) E.readMem(sample->tlsStart, t.data(), (size_t)n);
    E.writeMem(tls + 0x1000, t.data(), t.size()); a.putq(tls, tls + 0x1000);
  }
  E.map(top - STACK_SIZE, STACK_SIZE);
  // its first context: start(arg), returning to the address where a thread ends
  const u64 sp = top - 0x10000 - 0x28;
  { std::vector<u8> z(0x4d0, 0); E.writeMem(ctx, z.data(), z.size()); }
  a.putq(sp, magic(6));
  a.putd(ctx + 0x30, 0x10001f); a.putd(ctx + 0x34, 0x1f80); a.putd(ctx + 0x44, 0x202);   // (debug registers: none, a new thread has no breakpoint)
  a.putq(ctx + 0x78 + 8 * RCX, arg); a.putq(ctx + 0x78 + 8 * RSP, sp); a.putq(ctx + 0xf8, start);
  const u64 h = 0x800 + 4 * k;
  a.putq(rec(k) + T_STATE, suspended ? TS_SUSPENDED : TS_READY); a.putq(rec(k) + T_TEB, teb); a.putq(rec(k) + T_CTX, ctx); a.putq(rec(k) + T_HANDLE, h);
  a.putq(rec(k) + T_EXIT, 259); a.putq(STATE + T_COUNT, k + 1);
  if (tid) *tid = TID + 4 * k;
  return h;
}

// The running thread sleeps, waits or yields: another one which is ready runs. Nobody else ready: a thread whose wait
// has a time limit wakes with WAIT_TIMEOUT; else the running one goes on. Call it after the model returned to the caller.
void WinEnv::yield(Api& a) {
  if (a.q(STATE + T_COUNT) < 2 || a.stop != ST_NONE) return;
  const u64 cur = current(a);
  int to = nextReady(a, cur);
  if (to < 0) {
    for (u64 k = 0; k < count(a) && to < 0; k++)
      if (k != cur && stateOf(a, k) == TS_WAITING && (a.q(rec(k) + T_WAIT) & 0x100)) { a.putq(rec(k) + T_STATE, TS_READY); a.putq(a.q(rec(k) + T_CTX) + 0x78, 0x102); to = (int)k; }
  }
  if (to >= 0) switchThread(a, to, true);
}

void WinEnv::threadModels() {
  auto wait = [this](Api& a, u64 h, bool finite) {
    const int k = byHandle(a, h);
    a.ret(0);
    if (k < 0 || stateOf(a, (u64)k) == TS_DONE) { if (k < 0) yield(a); return; }
    const u64 cur = current(a);
    a.putq(rec(cur) + T_STATE, TS_WAITING); a.putq(rec(cur) + T_WAIT, (u64)k | (finite ? 0x100 : 0));
    const int to = nextReady(a, cur);
    if (to < 0) { a.putq(rec(cur) + T_STATE, TS_READY); a.E.g[RAX] = 0x102; return; }       // nobody can run: the wait gives up
    switchThread(a, to, true);
  };
  model("WaitForSingleObject", [wait](Api& a) { wait(a, a.arg(0), (a.arg(1) & 0xffffffff) != 0xffffffff); });
  alias("WaitForSingleObjectEx", "WaitForSingleObject");
  model("NtWaitForSingleObject", [wait](Api& a) { wait(a, a.arg(0), a.arg(2) >= 0x10000); });
  alias("ZwWaitForSingleObject", "NtWaitForSingleObject");
  for (const char* n : {"WaitForMultipleObjects", "WaitForMultipleObjectsEx", "NtWaitForMultipleObjects", "SwitchToThread", "NtYieldExecution", "ZwYieldExecution"})
    model(n, [this](Api& a) { a.ret(0); yield(a); });
  auto create = [this](Api& a, u64 start, u64 arg, bool suspended, u64 pHandle, u64 pTid, bool status) {
    u64 tid = 0; const u64 h = createThread(a, start, arg, suspended, &tid);
    if (h && pHandle >= 0x10000) a.putq(pHandle, h);
    if (h && pTid >= 0x10000) a.putd(pTid, (u32)tid);
    a.ret(status ? (h ? 0 : 0xC000009A) : h);
  };
  model("CreateThread", [create](Api& a) { create(a, a.arg(2), a.arg(3), (a.arg(4) & 4) != 0, 0, a.arg(5), false); });
  model("CreateRemoteThread", [create](Api& a) { create(a, a.arg(3), a.arg(4), (a.arg(5) & 4) != 0, 0, a.arg(6), false); });
  alias("CreateRemoteThreadEx", "CreateRemoteThread");
  model("NtCreateThreadEx", [create](Api& a) { create(a, a.arg(4), a.arg(5), (a.arg(6) & 1) != 0, a.arg(0), 0, true); });
  alias("ZwCreateThreadEx", "NtCreateThreadEx");
  model("RtlCreateUserThread", [create](Api& a) { create(a, a.arg(6), a.arg(7), (a.arg(2) & 0xff) != 0, a.arg(8), 0, true); });
  model("_beginthreadex", [create](Api& a) { create(a, a.arg(2), a.arg(3), (a.arg(4) & 4) != 0, 0, a.arg(5), false); });
  model("_beginthread", [create](Api& a) { create(a, a.arg(0), a.arg(2), false, 0, 0, false); });
  // a thread ends: its start routine returned (magic address) or it said so
  auto end = [this](Api& a, u64 code) {
    const u64 cur = current(a);
    if (a.q(STATE + T_COUNT) < 2 || cur == 0) { a.E.stopInfo = a.name[0] == '@' ? "thread end" : a.name; a.stop = ST_HALT; a.done = true; return; }
    a.putq(rec(cur) + T_STATE, TS_DONE); a.putq(rec(cur) + T_EXIT, code & 0xffffffff);
    const int to = nextReady(a, cur);
    if (to < 0) { a.E.stopInfo = "no thread can run"; a.stop = ST_HALT; a.done = true; return; }
    switchThread(a, to, false);
  };
  model("@magic6", [end](Api& a) { end(a, a.E.g[RAX]); });
  for (const char* n : {"ExitThread", "RtlExitUserThread", "_endthreadex", "_endthread"}) model(n, [end](Api& a) { end(a, a.arg(0)); });
  model("GetExitCodeThread", [](Api& a) { const int k = byHandle(a, a.arg(0)); if (k < 0) return a.ret(0); a.putd(a.arg(1), (u32)a.q(rec((u64)k) + T_EXIT)); a.ret(1); });
  model("ResumeThread", [](Api& a) {
    const int k = byHandle(a, a.arg(0)); if (k < 0) return a.ret(0xffffffff);
    const bool was = stateOf(a, (u64)k) == TS_SUSPENDED; if (was) a.putq(rec((u64)k) + T_STATE, TS_READY);
    a.ret(was ? 1 : 0);
  });
  alias("NtResumeThread", "ResumeThread");
  model("TerminateThread", [](Api& a) { const int k = byHandle(a, a.arg(0)); if (k > 0 && (u64)k != current(a)) { a.putq(rec((u64)k) + T_STATE, TS_DONE); a.putq(rec((u64)k) + T_EXIT, a.arg(1) & 0xffffffff); } a.ret(1); });
  model("GetThreadId", [](Api& a) { const int k = byHandle(a, a.arg(0)); a.ret(k < 0 ? 0 : TID + 4 * (u64)k); });
  model("GetCurrentThreadId", [](Api& a) { a.ret(a.d(a.teb() + 0x48)); });
}

}  // namespace unshroud
