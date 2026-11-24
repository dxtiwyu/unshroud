// unshroud - a Windows process for an image to run in: what a running process has and a file does not.
// win.cpp: the thread and process blocks (TEB, PEB), the loader's lists of modules with the system DLLs of this machine
// mapped (relocated, with their export tables), the process parameters, the shared system page, TLS.
// winapi.cpp: models of system functions. Every import stub of the image and every export of the mapped DLLs is hooked: a
// call there runs the model of that name and returns to the caller; a function without a model returns 0.
// winexc.cpp: exceptions. int3 / ud2 / access violations / divide errors / RaiseException build the EXCEPTION_RECORD and
// CONTEXT and are dispatched as ntdll does: vectored handlers, then the handlers of the frames (found with the images'
// .pdata, run as the code they are, with a DISPATCHER_CONTEXT), RtlUnwindEx, the top-level filter.
// Nothing of the system is ever run natively. What the models change lives in emulated memory (allocation cursor,
// TLS / FLS indexes, handler lists): a state saved and restored takes it along.
#pragma once
#include "engine.hpp"
#include "pe.hpp"
#include <functional>
#include <map>
#include <memory>
#include <string>

namespace unshroud {

struct WinModule {
  std::string name, path;
  u64 base = 0, size = 0, entry = 0, preferred = 0; u32 timestamp = 0;
  std::unordered_map<std::string, u32> exports;             // name -> rva
  std::unordered_map<std::string, std::string> forwards;    // name -> "dll.symbol"
  std::vector<u8> image;                                    // relocated bytes (empty: the explored image, mapped by loadPE)
  u64 ldr = 0;                                              // its LDR_DATA_TABLE_ENTRY
  u32 pdata = 0, pdataSize = 0;                             // exception directory (rva, bytes)
  bool hasTls = false; u64 tlsStart = 0, tlsEnd = 0, tlsIndex = 0, tlsCallbacks = 0; u32 tlsFill = 0;
  bool sample = false;
  bool contains(u64 a) const { return a >= base && a < base + size; }
};

class WinEnv;

// what a model sees: the call being made
struct Api {
  Engine& E; WinEnv& W; const std::string& name; bool wide;
  Stop stop = ST_NONE;                 // a model which ends the run sets it (ExitProcess)
  bool done = false;                   // the model returned to the caller or moved rip itself
  u64 arg(int k) const;                // k-th argument (Windows x64 convention), concrete
  Val argv(int k) const;               // ... with its expression
  u64 q(u64 a) const { u64 v = 0; E.readMem(a, &v, 8); return v; }
  u32 d(u64 a) const { u32 v = 0; E.readMem(a, &v, 4); return v; }
  u16 h(u64 a) const { u16 v = 0; E.readMem(a, &v, 2); return v; }
  void put(u64 a, const void* p, size_t n) { if (a >= 0x10000) E.writeMem(a, p, n); }
  void putq(u64 a, u64 v) { put(a, &v, 8); }
  void putd(u64 a, u32 v) { put(a, &v, 4); }
  std::string text(u64 a, bool wideChars, size_t limit = 520) const;   // a string of the program ("" when a < 0x10000)
  bool ustring(u64 a, std::string& out) const;                         // UNICODE_STRING at a
  bool astring(u64 a, std::string& out) const;                         // ANSI_STRING at a
  void ret(u64 value = 0);             // back to the caller, rax = value
  void retv(Val value);                // ... a value with its expression
  u64 alloc(u64 size, u64 align = 16); // bump allocator (its cursor is in emulated memory); 0 when the block is too big
  u64 teb() const;
  void lastError(u32 e);
};
using Model = std::function<void(Api&)>;

class WinEnv {
public:
  // the layout of the process
  static constexpr u64 STACK_TOP = 0x7f0000000000ull, STACK_SIZE = 0x100000, RSP0 = STACK_TOP - 0x10000;
  static constexpr u64 TEB = 0x7fd000000000ull, PEB = TEB + 0x100000, LDR = TEB + 0x200000, PARAMS = TEB + 0x300000, TLS = TEB + 0x400000,
                       FLS = TEB + 0x480000, STATE = TEB + 0x4f0000, APISET = TEB + 0x500000, KUSER = 0x7ffe0000ull;
  static constexpr u64 HOST_BASE = 0x7ff610000000ull, DLL_BASE = 0x7ff810000000ull, DLL_STEP = 0x10000000ull, HEAP_HANDLE = 0x7fb000000000ull;
  static constexpr u64 ALLOC_BASE = 0x7e0000000000ull, BIG = 1ull << 30, MAGIC = 0x7ffd00000000ull;
  static constexpr u32 PID = 0x1a2c, TID = 0x1f40;
  // STATE: +0 allocation cursor, +8 next TLS index, +0x10 next FLS index, +0x18 top-level exception filter,
  // +0x20 vectored exception handlers (count, then 16 entries), +0xa8 vectored continue handlers (count, 16 entries),
  // +0x130 dynamic function tables (count, then 8 x (table, entries, base)), +0x1000 scratch CONTEXT
  WinEnv();
  ~WinEnv();
  // Builds the process in E (the image is mapped already, by loadPE): to be called once, before the state every run
  // starts from is saved. False when the system DLLs cannot be read (the environment is then left out).
  bool build(Engine& E, const Image& img, const std::string& path);
  // An engine which runs in the process (after restore() of a state build() was part of): hooks, traps.
  void attach(Engine& E);
  // Runs the image's TLS callbacks and entry point (DllMain: DLL_PROCESS_ATTACH) in E, concretely. True when it returned.
  bool runInit(Engine& E, u64 maxIns, std::string* info = nullptr);
  // The state an entry point which did not return left is to be used all the same (what it initialized is there): the
  // threads it made are forgotten, the first thread runs again.
  void afterInit(Engine& E);

  // ---- models
  void model(const std::string& name, Model m);             // adds or replaces the model of a function, by name
  void alias(const std::string& name, const std::string& as);
  bool hasModel(const std::string& name) const;
  std::map<std::string, u64> calls, unmodeled, errors;      // counters, by name (cleared by the caller)
  bool trace = false;                                       // every call on stderr

  // ---- options
  bool exceptions = true;              // exceptions go to the program's handlers (else: a path ends at the instruction, as without a process)
  // An access below 0x10000: 0 never faults (zeros are read, a write maps the page: as without a process); 1 an access
  // violation when some handler is there to take it (nobody: as 0); 2 as 1, and whether the handlers get it is a decision
  // of the path (Engine::oracle) which an explorer flips: both the handler and the code after the access are explored.
  int nullFaults = 2;
  // What the environment answers is an input (UNSHROUD_ENVSYM, bits): 1 the result of a model (a pointer: there or NULL, a
  // decision; anything else: a value whose seed is the model's), 2 what a model wrote for the caller (small outputs: one
  // input per word, call site and occurrence, seeded with what was written), 4 the debugger fields of the PEB and the
  // shared page (unshroud_explore). Deterministic helpers (strings, memory, unwinding, TLS, locks) keep their answers.
  int envSym = 0;
  bool decideSizes = false;            // the size of an allocation which depends on the inputs is a decision of the path (too big: it fails); costly queries
  u64 retAddr = 0xdead0000ull;         // where the explored function returns: the walk of the frames ends there

  // ---- modules
  std::vector<std::unique_ptr<WinModule>> order;
  WinModule* host = nullptr; WinModule* sample = nullptr;
  WinModule* find(const std::string& name);
  WinModule* moduleAt(u64 address);
  WinModule* load(Engine& E, const std::string& name);       // mapped if it was not (an API set: the DLL which implements it)
  u64 resolve(Engine& E, const std::string& dll, const std::string& name, int depth = 0);   // an export, forwarders followed; 0: none
  bool listed(Engine& E, WinModule* m);
  u64 handleOf(Engine& E, const std::string* name);          // GetModuleHandle
  std::string systemDir, rootDir;
  u64 commandW = 0, commandA = 0, environmentW = 0;
  u8 features[64] = {};
  u32 verMajor = 10, verMinor = 0, verBuild = 19045;

  // ---- exceptions (winexc.cpp)
  int onTrap(Engine& E, Stop s);                             // Engine::trap
  // A system call made by the program itself (syscall with the service number in eax, the first argument in r10): the
  // number is looked up in this machine's ntdll (its Nt functions load it into eax) and the function's model runs.
  Stop onSyscall(Engine& E);                                 // Engine::sysCall
  std::unordered_map<u32, std::string> sysNames; bool sysReady = false; u64 sysCalls = 0;
  u64 lookupFunctionEntry(Engine& E, u64 pc, u64* imageBase);
  // ---- threads (winthread.cpp): cooperative, one runs at a time
  u64 createThread(Api& a, u64 start, u64 arg, bool suspended, u64* tid = nullptr);   // its handle (0: no more threads)
  void yield(Api& a);                                        // after the model returned: another ready thread runs
  static u64 magic(int k) { return MAGIC + 0x10 * (u64)k; }
  std::string apiName(u64 address) const;

private:
  friend struct Api;
  friend struct Exc;
  std::unordered_map<std::string, WinModule*> modules;       // by key (lower case, no .dll)
  std::unordered_map<u64, u32> apiAt;                        // hooked address -> name id
  std::vector<std::string> names; std::unordered_map<std::string, u32> nameId; std::vector<Model> models;
  std::unordered_map<std::string, std::string> apiset; std::vector<u8> schema;
  std::unordered_map<u64, u64> cursor;
  u64 nextBase = DLL_BASE; bool ready = false;
  u32 idOf(const std::string& name);
  WinModule* add(Engine& E, const std::string& path, u64 base);
  void hookModule(WinModule* m);
  void entry(Engine& E, WinModule* m); void link(Engine& E, u64 head, u64 node); void enlist(Engine& E, WinModule* m);
  u64 allocIn(u64 region, u64 size); u64 wideStr(Engine& E, u64 region, const std::string& text, u64* bytes = nullptr);
  void ustr(Engine& E, u64 address, u64 region, const std::string& text);
  void teb(Engine& E); void peb(Engine& E); void ldr(Engine& E); void params(Engine& E); void kuser(Engine& E); void tls(Engine& E);
  Stop call(Engine& E, u32 id);
  u64 sysSite = 0;                                           // a system call's site (the instruction after it) for call()
  void answer(Engine& E, u64 site, bool outputs);
  void defaults();                                           // winapi.cpp
  void threadModels();                                       // winthread.cpp
  void switchThread(Api& a, int to, bool saveCurrent);
  void saveContext(Engine& E, u64 context); void loadContext(Engine& E, u64 context);   // a CONTEXT record in memory <-> the registers (winexc.cpp)
  void excModels();                                          // winexc.cpp
};

bool envKeeps(const std::string& name);
bool envAllocates(const std::string& name);

static inline std::string winKey(const std::string& name) {
  size_t s = name.find_last_of("/\\"); std::string b = s == std::string::npos ? name : name.substr(s + 1);
  for (char& c : b) if (c >= 'A' && c <= 'Z') c += 32;
  if (b.size() > 4 && b.compare(b.size() - 4, 4, ".dll") == 0) b.resize(b.size() - 4);
  return b;
}

}  // namespace unshroud
