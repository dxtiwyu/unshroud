// unshroud - native execution. A block which runs often is compiled: its instructions are encoded again for this CPU with
// the guest's registers in the host's (the stack pointer in another register), every memory operand translated through
// a table of the engine's pages (pages only; a byte which holds an expression or is unknown memory is refused by a
// check of the page's taint bytes), branches linked to other compiled blocks. Whatever generated code cannot do -
// an instruction outside its list, an operand which holds an expression, a page not in the table, a fault - goes back
// to the interpreter, instruction by instruction. Generated code never calls a system function and never touches
// memory which is not a page of the engine or the Jit's own tables.
#pragma once
#include "engine.hpp"

namespace unshroud {

struct JitStats {
  u64 fragments = 0, refused = 0, insCompiled = 0, codeBytes = 0, flushes = 0, deferred = 0;
  u64 runs = 0, ins = 0, helper = 0, fills = 0, bails = 0, exits[8] = {};
  double tCompile = 0;
};

Jit* jitCreate(Engine& E);                  // null: this CPU or this address space cannot (no BMI2 / AVX2, no room below 2 GB)
void jitDestroy(Jit* j);
// Runs from E.rip (the start of block b) for at most `budget` instructions; returns how many ran (0: nothing native
// here, the interpreter goes on).
u64 jitRun(Jit* j, Engine& E, u64 budget, Block* b);
void jitFlushCode(Jit* j);                  // the guest's code, the stops or the hooks changed
void jitFlushTlb(Jit* j);                   // the pages changed (a state restored, pages shared)
void jitDrop(Jit* j, u64 pn);               // one page changed
void jitSyncCov(Jit* j, Engine& E);         // conditional jumps run as native code -> Engine::cov
const JitStats& jitStats(Jit* j);
// Checks, once per process, that this CPU sets the flags the manuals leave undefined the way the interpreter does
// (it follows AMD Zen); instructions for which it does not are never compiled. Returns how many differ.
int jitCalibrate(bool verbose = false);

}  // namespace unshroud
