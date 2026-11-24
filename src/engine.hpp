// unshroud - x86-64 concolic engine: concrete values everywhere, expressions only where inputs flow.
#pragma once
#include "expr.hpp"
#include <cstdio>
#include <functional>
#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>

namespace unshroud {

struct Val { u64 c; u32 s; };          // concrete value, expression (0: concrete only)
struct Cell { u32 e; u32 off; };       // a byte of memory or of a vector register: byte `off` of expression e (e == 0: concrete)

enum : u8 { RK_NONE = 0, RK_GPR, RK_VEC, RK_RIP, RK_FS, RK_GS, RK_SEG0, RK_FLAGS, RK_OTHER, RK_SYS };   // RK_SYS: control and debug registers
enum : u8 { OT_NONE = 0, OT_REG, OT_MEM, OT_IMM };

struct Opnd {
  u8 type = OT_NONE;
  u8 size = 0;          // bytes
  u8 rk = 0;            // register kind (OT_REG)
  u8 reg = 0;           // register index
  u8 roff = 0;          // byte offset in the register (ah..bh: 1)
  u8 base = 0xff, index = 0xff, scale = 0, seg = 0;   // memory: base/index GPR (16 = rip), segment kind
  i64 disp = 0;         // displacement, or immediate value
};

struct Insn {
  u64 addr = 0, next = 0;
  u16 mn = 0;           // ZydisMnemonic
  u8 len = 0, nops = 0;
  u8 opsz = 0;          // operand width in bytes
  u8 asz = 8;           // address width in bytes
  u8 rep = 0;           // 1: rep/repe, 2: repne
  u8 vex = 0;           // VEX/EVEX encoded
  u8 vl = 0;            // vector length in bytes (VEX)
  Opnd op[4];
};

struct Block { u64 addr; u32 epoch; bool special; std::vector<Insn> ins;
  u32 hits = 0; void* frag = nullptr; u64 fragMask = ~0ull; u32 fragEpoch = 0;     // native code for it (jit.hpp), by the inputs' mask
  // the blocks which ran after this one (two of them: both ways of a branch): found without a lookup. They live as
  // long as this block does (all blocks are dropped together).
  u64 nextA[2] = {~0ull, ~0ull}; Block* nextB[2] = {nullptr, nullptr}; u8 nextK = 0; };

// RFLAGS bits
enum : u32 { FL_CF = 1u << 0, FL_PF = 1u << 2, FL_AF = 1u << 4, FL_ZF = 1u << 6, FL_SF = 1u << 7, FL_DF = 1u << 10, FL_OF = 1u << 11,
             FL_ARITH = FL_CF | FL_PF | FL_AF | FL_ZF | FL_SF | FL_OF };
// operations whose flags are computed when read
enum : u8 { LF_NONE = 0, LF_ADD, LF_SUB, LF_ADC, LF_SBB, LF_LOGIC, LF_INC, LF_DEC, LF_NEG, LF_SHL, LF_SHR, LF_SAR, LF_MUL, LF_IMUL, LF_ROL, LF_ROR, LF_IMUL2 };

struct LazyRec { u8 op = 0, w = 64; u32 lazy = 0; u64 a = 0, b = 0, r = 0, x = 0; u32 sa = 0, sb = 0, sr = 0, sx = 0; };
struct Flags {
  u8 op = LF_NONE, w = 64;
  u32 lazy = 0;                         // flags taken from the lazy operation
  u64 a = 0, b = 0, r = 0, x = 0;       // operands, result, extra (carry in, shift count, high half of a product)
  u32 sa = 0, sb = 0, sr = 0, sx = 0;
  LazyRec prev;                         // the flags an instruction which sets only some of them left to the one before
  u64 bits = 0x202;                     // flags not covered by `lazy` (RFLAGS layout, bit 1 and IF set)
  u32 sym[12] = {};                     // their expressions (1 bit), by bit position
  u32 folded = 0;                       // flags (RFLAGS bits) set from a value which depends on the inputs and is a constant by the rules
};

struct Page {
  u32 refs = 1;
  u32 nsym = 0;                         // symbolic cells on the page
  bool code = false;
  bool lazy = false;                    // some cells hold recorded (not built) expressions
  Cell* sh = nullptr;                   // 4096 cells or null
  u64* unk = nullptr;                   // 8 words of bits, or null: 8-byte words which are unknown memory (an input each, made when first read)
  // 8192 bytes or null, made when native code first touches a page which needs them (it checks them before every
  // access) and kept exact from then on. [0, 4096): non-zero where a byte holds an expression or is unknown memory
  // (what a load checks). [4096, 8192): those, and the bytes instructions were decoded from (what a store checks).
  u8* taint = nullptr;
  alignas(64) u8 d[4096];
  ~Page() { delete[] sh; delete[] unk; delete[] taint; }
};

struct PathConstraint {
  u32 cond;                             // 1-bit expression, true on the path taken
  u32 expr;                             // kinds 1-3: the expression made concrete (its value is `taken`)
  u64 pc;                               // the branch (or the instruction which made it)
  u64 taken, other;                     // targets: taken, the other one (0 if computed)
  u8 kind;                              // 0: branch, 1: address made concrete, 2: computed target, 3: other
  u64 at = 0;                           // instructions run when it was added
};

enum Stop : int { ST_NONE = 0, ST_COUNT, ST_ADDRESS, ST_RETURN, ST_FAULT, ST_UNSUPPORTED, ST_EXCEPTION, ST_HOOK, ST_SYSCALL, ST_HALT };
enum : u8 { TK_NONE = 0, TK_BREAKPOINT, TK_INVALID, TK_DIVZERO, TK_DIVOVF, TK_INT, TK_PRIV, TK_SINGLESTEP, TK_READ, TK_WRITE, TK_EXEC, TK_GP };   // TK_GP: a general protection fault which is no privileged instruction

struct Page;
class Jit;
// (the standard hash of a 64-bit key goes through its bytes one by one: a page lookup is too frequent for that)
struct PageHash { size_t operator()(u64 k) const { return (size_t)((k * 0x9E3779B97F4A7C15ull) >> 32); } };
using PageMap = std::unordered_map<u64, Page*, PageHash>;
// a saved state: registers, flags, memory (pages shared copy-on-write), path
struct State {
  u64 g[16]; u32 gs[16]; u64 rip; u64 fsbase, gsbase; u32 mxcsr; u32 vsym; Flags fl;
  u8 v[16][32]; Cell vc[16][32];
  PageMap pages;
  std::vector<PathConstraint> path;
  u64 icount; u32 epoch;
  u64 id = 0;                           // which state this is (never used again): an engine knows the one it was last set to
  ~State();
};

class Engine {
public:
  Engine();
  ~Engine();
  Ctx X;

  // ---- memory
  void map(u64 addr, u64 size);                         // zero pages
  void writeMem(u64 addr, const void* data, size_t size); // concrete
  void readMem(u64 addr, void* out, size_t size);       // concrete values
  bool autoMap = true;                                  // unmapped memory reads as zero, a write maps a page (else: fault)
  size_t maxPages = 1u << 19;                           // pages written at most (2 GB): past that, writes fault (memory guard)
  // pages a run may make or copy (0: no limit): a fill or a copy of unknown length stops there instead of writing gigabytes
  u32 runPages = 0, runPageLimit = 0;
  bool isMapped(u64 addr);
  Val load(u64 addr, unsigned size);                    // size 1..8
  void store(u64 addr, unsigned size, Val v);
  bool loadCells(u64 addr, unsigned size, u8* bytes, Cell* cells);       // vectors: bytes + cells (filled only if it returns true)
  void storeCells(u64 addr, unsigned size, const u8* bytes, const Cell* cells);
  u32 symbolizeMem(u64 addr, unsigned size, const std::string& name);   // returns the variable's node
  // ---- unknown memory (under-constrained inputs). An 8-byte word marked unknown becomes an input the first time it
  // is read (a variable per address, the same one in every run; its value: runVals, else what the word held); a word
  // written whole before that never is one. The zone is nobody's memory: every word of it is unknown, and holds at
  // first a pointer into the zone, to a place of its own - what an argument or a field points to is then data an
  // explorer chooses, not zeros, and what that data points to is unknown memory again. markUnknown: other memory whose
  // content is not known either (the writable data of an image which never ran).
  bool lazyMem = false;
  bool ucAnywhere = false;                              // (unshroud_opaque) any page nobody mapped is unknown memory, as the zone is
  bool ucSeedZone = false;                              // every unknown word's first value is a place of the zone (not what the image holds)
  static constexpr u64 UC_BASE = 0x100000000000ull, UC_END = 0x700000000000ull, UC_SLOT = 0x100000ull;
  static bool inZone(u64 a) { return a >= UC_BASE && a < UC_END; }
  // a place of its own in the zone, for a new input to point to. The places are at the bottom of the zone, one after
  // the other: what a program adds to such a pointer (another input, scaled) still falls in the zone.
  u64 ucNext = 0;
  // Places (UNSHROUD_PLACES): an unknown word of the image's data (a global) which holds 0 gets a place of its own in the
  // zone, high up (away from ucFresh's): when a model makes the word non-zero, the solver tries that pointer first, so
  // what it points to is unknown memory again (not page 0 or wherever the value 1 points).
  bool placesOn = false; u64 placeNext = 0;
  u64 placeFresh() { return UC_BASE + (UC_END - UC_BASE) / 4 * 3 + (++placeNext % ((UC_END - UC_BASE) / UC_SLOT / 8)) * UC_SLOT + UC_SLOT / 2; }
  u64 ucFresh() { return UC_BASE + (++ucNext % ((UC_END - UC_BASE) / UC_SLOT / 4)) * UC_SLOT + UC_SLOT / 2; }
  std::unordered_map<u64, u32> ucVars;                  // address of an unknown word -> its variable (index)
  u32 ucPagesMade = 0, ucMaxPages = 4096;               // pages of the zone made in this run (restore() resets the count)
  // unknown words a run may turn into inputs: past that, they read as what the memory holds (zeros in the zone) - a
  // scan through unknown memory ends there instead of making millions of inputs
  u32 ucWordsMade = 0, ucMaxWords = 1u << 16;
  void markUnknown(u64 addr, u64 size);                 // the words wholly inside [addr, addr + size)
  Page* known(u64 addr, unsigned size);                 // the unknown words of [addr, addr + size) (one page) become inputs; the page
  void unkStore(Page* p, u64 addr, unsigned size);      // before a write there: words overwritten whole are never inputs
  // A call which lands in the zone is a call of an unknown function: it returns at once, its result is an input
  // (one per call site and occurrence).
  std::unordered_map<u64, u32> ucRets; std::unordered_map<u64, u32> ucSite; u64 ucCalls = 0;
  bool ucCall();
  // Calls which cannot come back (the callee throws, ends the process, faults, never ends). For the call sites an
  // explorer names, whether the call is made is a decision of the path (oracle). Left out - the default once a site is
  // named - the call returns at once: its result is an input of its own, as for an unknown function, and the memory
  // of the caller's frame its first four arguments point to is unknown again (havocOut bytes each: what the callee
  // would have stored there). What the function does after the call can then be explored. `havocked` counts the calls
  // the current run left out: what it finds rests on the assumption that those calls can return.
  std::unordered_set<u64> havocSites; u32 havocked = 0; u32 havocOut = 0x40; u64 havocTop = 0;   // havocTop: where the function's frame ends (its entry rsp)
  std::unordered_map<u64, u32> havocRets, havocSeen;
  // The words a left-out call would have stored: address -> (call site, occurrence, argument register << 8 | word), and the
  // input each one is when read (one per call, argument and word: the same on every path which makes the same calls).
  struct OutId { u64 site; u32 occ; u16 word; bool operator<(const OutId& o) const { return site != o.site ? site < o.site : occ != o.occ ? occ < o.occ : word < o.word; } };
  std::unordered_map<u64, OutId> outKey; std::map<OutId, u32> outVars;
  void markOut(u64 addr, u64 size, OutId id, bool seeded = false);   // seeded: the input's value is what the word holds (else a place in the zone)
  std::unordered_set<u64> outSeed;
  void addHavocSite(u64 callInsn);
  // Forced branches (the explorer's force phase): the first time a run meets a jump of forceSites, whether it goes the
  // way its condition says is a decision of the path (oracle; default yes). Forced the other way, the condition is no
  // constraint of the path and the run counts as assumed (havocked), as for a call left out.
  std::unordered_set<u64> forceSites; std::unordered_map<u64, u32> forceSeen; u32 forced = 0;
  void addForceSite(u64 jumpInsn);
  bool forceBranch(u64 pc);                             // true: in this run the jump goes against its condition
  // Jump tables (UNSHROUD_SWITCH): the targets of a computed jump the code could take. The first time a run meets the jump,
  // going to each other target is a decision of its own (oracle; default no), as for a forced branch.
  std::unordered_map<u64, std::vector<u64>> switchTargets;
  u64 forceSwitch(u64 pc, u64 natural);
  u64 callBefore(u64 ret);                              // the call instruction which returns to `ret` (among the blocks decoded; else by the bytes before it; 0: none)
  bool havocCall(const Insn& I);                        // at a call of havocSites: true when it was left out
  // Variables an address constraint fixed on this path (x == c): what depends on them only needs no constraint again.
  std::vector<u8> pinned; std::unordered_map<u32, std::vector<u32>> pinVars; u64 pinSkips = 0;

  void pokeConcrete(u64 addr, const void* data, size_t size);   // concrete bytes, the cells (expressions) are kept
  u64 memHash() const;                                  // of every page: bytes, expressions, unknown words (two engines in the same state agree)
  int memDiff(const Engine& o, FILE* out, int limit = 8) const;   // where the memory of two engines differs (returns how many places, up to limit)
  std::shared_ptr<State> snapshot();
  void restore(const State& st);

  // ---- registers
  u64 g[16] = {}; u32 gs[16] = {};                     // GPRs: concrete, expression
  u64 rip = 0;
  alignas(32) u8 v[16][32] = {}; Cell vc[16][32] = {}; u32 vsym = 0;   // YMM: bytes, cells; vsym bit i: reg i has symbolic cells
  u64 fsbase = 0, gsbase = 0;
  u32 mxcsr = 0x1f80;
  Flags fl;
  u32 symbolizeReg(int r, const std::string& name);     // whole GPR
  void symbolizeVec(int r, const std::string& name);    // the 32 bytes of a vector register, as four 64-bit inputs
  void symbolizeFlags(const std::string& name);         // CF PF AF ZF SF OF as 1-bit inputs
  Val getReg(int r) const { return Val{g[r], gs[r]}; }
  void setReg(int r, Val x) { g[r] = x.c; gs[r] = x.s; }

  // ---- execution
  // Lazy mode: while run() executes, operations on symbolic values are recorded and built only when read (branches,
  // addresses, what the caller asks for). After run(), registers / flags / memory may hold recorded expressions:
  // X.force(id) builds one, settle() all of them (snapshot() does it). restore() forgets the records.
  // A load whose address depends on the inputs but can only take a few values (a table indexed by something small: masked,
  // a remainder, a byte) gives one expression which selects among the entries, instead of fixing the address on this path:
  // tableMax entries at most (0: never), tableBudget such loads in one run.
  u32 tableMax = 0, tableBudget = 2048, tableLoads = 0;
  bool tableLoad(Val addr, unsigned size, Val& out);
  bool lazy = false;
  size_t lazyLimit = 1u << 21;                          // records at which the live state is built and the tape emptied
  void settle();
  u64 lazyOffRuns = 0;                                  // runs which gave recording up (everything was read)
  std::vector<Page*> lazyPages;
  Stop run(u64 maxIns);
  Stop step();                                          // one instruction
  u64 icount = 0;                                       // instructions run
  u64 symIns = 0;                                       // instructions which asked for expressions
  bool profile = false; u64 cycSym = 0, cycCon = 0;      // UNSHROUD_PROFILE: cycles in instructions with / without expressions
  // ... and, by mnemonic, the instructions which asked for expressions: how many, the table lookups, the nodes made, the cycles
  struct SymHist { u64 n = 0, lookups = 0, nodes = 0, cyc = 0; }; std::vector<SymHist> symHist;
  static const char* mnemonicName(int mn);
  bool hotOn = false; std::unordered_map<u64, u64> hot;  // UNSHROUD_HOT: instructions run, by block
  std::unordered_set<u64> stops;                        // stop before running these addresses
  std::unordered_map<u64, std::function<Stop(Engine&)>> hooks;   // run instead of the instruction at the address
  // A table of hooked addresses shared by many engines (the functions of the system DLLs of a process: win.hpp): the
  // table belongs to its owner, apiCall runs the entry found. A hook of this engine at the same address comes first.
  const std::unordered_map<u64, u32>* apiTable = nullptr; u64 apiLo = 0, apiHi = 0;
  std::function<Stop(Engine&, u32)> apiCall;
  // ---- traps: what an instruction raised instead of completing (run() returns ST_EXCEPTION / ST_FAULT / ST_HALT)
  u8 trapKind = 0; u64 trapArg = 0;                    // TK_INT: the vector; TK_READ / TK_WRITE / TK_EXEC: the address
  // Called with the state as it was before the instruction (rip on it). Returns 0: not handled, run() stops as it
  // always did; 1: the state was changed (an exception handler is to run), execution goes on at rip; 2 (TK_READ /
  // TK_WRITE in the guarded pages only): the instruction is run again with the guard off.
  std::function<int(Engine&, Stop)> trap;
  // The trap flag: an instruction which sets it (popfq) is followed by one more instruction, then by a single-step trap
  // (1: set by the instruction which just ran, 2: the next one traps). Native code is not entered meanwhile.
  u8 tf = 0;
  // mov ss: the CPU holds a pending single step back past the next instruction (movSS: the instruction which just ran loaded
  // SS). ssSel: what SS holds (2bh, or 53h: the other selector a 64-bit Windows process may load there).
  u8 movSS = 0; u16 ssSel = 0x2b;
  // The program's hardware breakpoints (set through a CONTEXT: a handler which goes on, NtContinue, SetThreadContext):
  // dr[0..3] and dr7 as the kernel keeps them (user addresses; local enables, type and length). drExec / drData: the
  // enabled execute / data breakpoints (bit n: DRn), data breakpoint n watching [drLo, drHi); dataHits: B0-B3 of the data
  // breakpoints the instruction running hit; dbHeld: the #DB a mov ss held back; dbStatus: DR6's bits for the #DB being
  // raised; rfOnce: RF, the next instruction does not hit an execute breakpoint. dbWatch: accesses are checked (while a
  // guest instruction runs only: the process model's own accesses are the kernel's). Native code is off while any is set.
  u64 dr[4] = {0, 0, 0, 0}, dr7 = 0, drLo[4] = {0, 0, 0, 0}, drHi[4] = {0, 0, 0, 0}, dbHeld = 0, dbStatus = 0;
  u8 drExec = 0, drData = 0, drWrOnly = 0, dataHits = 0, rfOnce = 0; bool dbWatch = false;
  // dbgOn: something of the above (or tf, movSS) may be live: the run loop looks at them only then (set where they are
  // set, worked out again after each instruction)
  u8 dbgOn = 0;
  void drUpdate();
  void dataCheck(u64 a, unsigned size, bool write) {
    for (int i = 0; i < 4; i++)
      if (((drData >> i) & 1) && (write || !((drWrOnly >> i) & 1)) && a < drHi[i] && a + size > drLo[i]) dataHits |= (u8)(1u << i);
  }
  u8 execHits(u64 a) const { u8 h = 0; for (int i = 0; i < 4; i++) if (((drExec >> i) & 1) && dr[i] == a) h |= (u8)(1u << i); return h; }
  // Addresses from 2^47 up are not a user program's: an access there faults (non-canonical: a general protection fault,
  // the kernel's half: an access violation with the address). Set where a process is modelled.
  bool hiFault = false;
  // syscall / sysenter in the program itself (not through a system DLL): called with rip after the instruction. ST_NONE:
  // done, execution goes on at rip; else the run stops with what it returns.
  std::function<Stop(Engine&)> sysCall;
  // an input of its own for (site, how many times the site was met in this run): the result of something unknown
  Val ucValue(u64 site, const char* what);
  // What the environment answered (a model's result) as an input of its own, one per call site and occurrence in the
  // run: seed is the model's answer (the value of every run which does not ask for another one).
  std::unordered_map<u64, u32> envRets; std::unordered_map<u64, u32> envSeen;
  u32 envOcc(u64 site) { return envSeen[site]++; }
  Val envValue(u64 site, u32 occ, u64 seed, unsigned w = 64);
  // Writes made through writeMem while recW is set (the models' outputs)
  bool recW = false; std::vector<std::pair<u64, u64>> recWrites;
  bool cpuidSym = false;                                // what cpuid answers is an input (seeded with this CPU's answer): another CPU answers otherwise
  u64 guardPages = 0, guardSet = 0;                     // accesses to pages below this one fault (0x10: the null region); 0: none
  void setGuard(u64 pages) { guardPages = guardSet = pages; flushTlb(); }
  // what the trap handler keeps for one run (restore() resets it): faults nobody took, by place; how many traps; the
  // instruction to run again without the guard. After softLimit such faults the guard is off until the next restore().
  std::unordered_set<u64> trapMemo; u32 softFaults = 0, softLimit = 64, trapCount = 0; u64 softRetry = 0;
  std::string stopInfo;
  Insn lastInsn;

  // ---- path
  std::vector<PathConstraint> path;
  bool keepAddressConstraints = true;
  // a run which keeps deciding the same branch (a loop bounded by an input, a copy up to a symbolic end) is stopped:
  // after spinLimit constraints from one instruction (0: never). Reset by spinReset().
  u32 spinLimit = 0; bool spinning = false;
  u64 spinTag[256] = {}; u32 spinCount[256] = {};
  void spinReset() { spinning = false; memset(spinCount, 0, sizeof spinCount); memset(spinTag, 0, sizeof spinTag); }
  // An endless loop (a list walk which never meets its end, a wait on memory which nothing writes) is stopped: after
  // loopLimit instructions with nothing new (no block, no constraint, no expression), the registers are compared each time
  // execution comes back to one place; the same registers twice in a row, with the same stores in between, cannot end.
  u64 loopLimit = 0;                                    // 0: never checked
  u64 writeHash = 0;                                    // of the stores since the mark
  struct LoopMark { u64 rip = 0, hash = 0, at = 0, period = 0, writes = 0, span = 0; bool armed = false, twice = false; } loopMark;
  u64 progressSig = 0, progressAt = 0;
  u64 stateHash() const;
  // A value which the rules made a constant out of values which depend on the inputs keeps a constant expression: the
  // mark by which a branch on it is known to be decided by the rules (an opaque predicate, proved). In mutated and
  // virtualized code such marks spread to everything (a register swapped with an input by three xors, then the stack
  // pointer, then every value of the virtual machine), each operation on them costs lookups, and nothing of it runs
  // as native code. A run which writes more than markLimit of them is such code: from there on, for this engine, a
  // constant is a plain value (branches decided by the flags of an operation on real expressions are still noted).
  bool dropMarks = false; u32 markWrites = 0, markLimit = 20000;       // UNSHROUD_NOMARK=1: from the start; UNSHROUD_MARK_LIMIT=N (0: never)
  void markStorm();
  // true: the constant expression of a value which is being written is to be dropped
  bool plainConst(u32 s) { if (!X.isC(s)) return false; if (dropMarks) return true; if (markLimit && ++markWrites > markLimit) { markStorm(); return true; } return false; }
  bool condFolded = false;                             // the last cond(): symbolic operands, constant result
  std::vector<std::pair<u64, u64>> folded;             // (branch, other side) of branches the expression rules decided
  std::vector<std::pair<u64, u64>> foldedTaken;        // (branch, side taken) of the same branches
  void noteFolded(u64 pc, u64 taken, u64 other) {
    if (folded.size() < 100000 && (folded.empty() || folded.back() != std::make_pair(pc, other))) folded.push_back({pc, other});
    if (foldedTaken.size() < 100000 && (foldedTaken.empty() || foldedTaken.back() != std::make_pair(pc, taken))) foldedTaken.push_back({pc, taken});
  }
  void addConstraint(u32 cond, u64 pc, u64 taken, u64 other, u8 kind, u32 expr = 0);
  // A decision which no input of the program fixes (does a handler take this fault, or is the access let through?) is
  // an input of its own, 1 bit: the decision is a constraint of the path (its "targets" 1 / 2 are not addresses), the
  // explorer flips it like a branch. Its value in this run: runVals (the explorer's values of all inputs), else dflt.
  bool oracle(u64 key, bool dflt);
  const std::vector<u64>* runVals = nullptr;
  std::unordered_map<u64, u32> oracleVars;             // key -> the input
  void concretized(u32 expr, u64 value, unsigned w, u64 pc, u8 kind);   // expr == value on this path (kinds 1-3)

  // ---- values
  u32 S(Val x, unsigned w) { return x.s ? x.s : X.cst(x.c, w); }   // expression of a value
  u32 flagExpr(u32 bit);                                // expression of a flag (built), or 0 if concrete
  Val flag(u32 bit);                                    // value of a flag
  Val cond(unsigned cc);                                // value of condition code cc (0..15, Intel order)
  u64 rflags();                                         // concrete RFLAGS

  // decoding
  const Insn* decodeAt(u64 addr);
  Block* block(u64 addr);
  void flushBlocks();                                   // after stops or hooks changed
  std::string disasm(u64 addr);

  // every conditional jump executed, with the side taken (whether it depends on the inputs or not): coverage, over the
  // runs of an engine. covOn turns the record on; cov holds (address << 1 | taken).
  bool covRec = false; std::vector<u64> covNewRun;      // covRec: the sides this run executed first (for the explorer's force rounds)
  bool covOn = false; std::unordered_set<u64> cov, covPlain; u64 covLast[1024] = {}, covLastP[1024] = {};      // covPlain: on paths which left no call out
  void covNote(u64 pc, bool taken) {
    const u64 k = (pc << 1) | (taken ? 1 : 0); const u32 i = (u32)((pc ^ (pc >> 10) ^ taken) & 1023);
    if (covLast[i] != k) { covLast[i] = k; if (cov.insert(k).second && covRec) covNewRun.push_back(k); }
    if (!havocked && covLastP[i] != k) { covLastP[i] = k; covPlain.insert(k); }
  }
  // stats
  u64 blocksDecoded = 0;
  u64 codeFlushes = 0;                                  // stores into pages with decoded code (each one drops every block and all native code)
  u64 nativeCount = 0;                                  // instructions run on this CPU
  // ---- native execution (jit.hpp): blocks run often, whose inputs hold no expression, run as generated host code
  bool jitOn = true;                                    // UNSHROUD_JIT=0 turns it off
  u32 jitHot = 20;                                      // executions of a block before it is compiled (UNSHROUD_JIT_HOT)
  Jit* jit = nullptr;                                   // made when the first block gets hot
  u64 jitIns = 0, jitRuns = 0;                          // instructions run as generated code, and how many times it was entered
  void taintSet(Page* p, u64 addr, unsigned n, bool sym) {   // the cells of n bytes at addr (one page) changed
    if (p->taint) {
      const unsigned off = (unsigned)(addr & 4095);
      memset(p->taint + off, sym ? 0xff : 0, n); memset(p->taint + 4096 + off, sym ? 0xff : 0, n);
      if (!sym && p->code && !codeBits.empty()) codeMarks(p, addr >> 12, off, n);      // (decoded bytes stay marked for stores)
    } else if (sym && jit) jitDropPage(addr >> 12);
  }
  void jitDropPage(u64 pn);                             // the page changed (another one, other bytes with expressions): native code looks it up again
  // The loop detector works in windows (so that long loops run as native code in between): the first one (2048
  // instructions: a tight loop shows there) when loopLimit instructions brought nothing new, the next ones after 128
  // times the length of the one before, twice as long each time.
  u64 loopWin = 0, loopWinEnd = 0;

private:
  friend struct Sem;
  friend class Jit;
  PageMap pages;
  struct TlbE { u64 tag; Page* p; };
  TlbE rtlb[512], wtlb[512];
  Page* pageR(u64 pn);
  Page* pageW(u64 pn);
  Page* ucPage(u64 pn);
  void flushTlb();
  [[noreturn]] void fault(u64 addr, bool write);        // a memory access which cannot be done: trapKind / trapArg, then throws ST_FAULT
  std::unordered_map<u64, Block*> blocks;
  // Blocks dropped while one of them may still be running (a store into decoded code, a nested run of a handler):
  // freed when the outermost run loop is between two blocks. The block which was running is left after the
  // instruction which caused the drop.
  std::vector<Block*> graveyard; u32 runDepth = 0;
  struct BCache { u64 tag; Block* b; } bcache[4096];
  u32 epoch = 1;
  void* decoder;                                        // ZydisDecoder
  void codeWritten(Page* p);
  // What changed in the page table since the engine was set to a state (snapshot / restore): going back to that same
  // state undoes these changes instead of copying the whole table. (page number, the page it replaced or null; the
  // list holds the engine's reference to a replaced page)
  u64 baseId = 0; std::vector<std::pair<u64, Page*>> journal;
  // The bytes this engine has decoded instructions from: 4096 bits per page (Page::code only says that some engine has
  // decoded something on the page: pages are shared). A store to one of those bytes makes the decoded blocks and the
  // native code stale (codeWritten); a store to the other bytes of such a page is a store like any other - virtual
  // machines keep their registers next to their code. codeTouched: code was written since the engine was last set to
  // a state.
  std::unordered_map<u64, u64*> codeBits; bool codeTouched = false;
  void markCode(u64 addr, unsigned len);                // an instruction was decoded there
  bool codeHit(u64 pn, unsigned off, size_t n) const {  // does [off, off + n) of the page hold a decoded byte?
    auto it = codeBits.find(pn);
    if (it == codeBits.end()) return false;
    const u64* b = it->second;
    if (n >= 64) { for (unsigned i = off & ~63u; i < off + n && i < 4096; i += 64) if (b[i >> 6]) { for (unsigned k = std::max(i, off); k < std::min<size_t>(i + 64, off + n); k++) if ((b[k >> 6] >> (k & 63)) & 1) return true; } return false; }
    for (unsigned i = off; i < off + n && i < 4096; i++) if ((b[i >> 6] >> (i & 63)) & 1) return true;
    return false;
  }
  void codeMarks(Page* p, u64 pn, unsigned off, size_t n) {   // the store marks of the page's decoded bytes in [off, off + n)
    auto it = codeBits.find(pn);
    if (it == codeBits.end() || !p->taint) return;
    const u64* b = it->second;
    for (unsigned i = off; i < off + n && i < 4096; i++) { if (!(i & 63) && !b[i >> 6] && i + 64 <= off + n) { i += 63; continue; } if ((b[i >> 6] >> (i & 63)) & 1) p->taint[4096 + i] = 0xff; }
  }
  void journalDrop();
  Stop exec(const Insn& I);
  Stop runLoop(u64 maxIns);
};

// the expression of n bytes (n <= 8), byte 0 lowest
u32 cellsExpr(Ctx& X, const u8* bytes, const Cell* cells, unsigned n);

// register indexes
enum { RAX = 0, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8, R9, R10, R11, R12, R13, R14, R15 };

}  // namespace unshroud
