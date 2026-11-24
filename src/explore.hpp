// unshroud - whole-function exploration: every feasible path, by concolic runs and generational search.
#pragma once
#include "engine.hpp"
#include "solver.hpp"
#include <map>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>

namespace unshroud {

// where an input lives (written there before each run)
struct Input { u32 var; u8 kind; u8 reg; u8 size; u64 addr; };   // kind 0: register, 1: memory

struct ExploreConfig {
  u64 retAddr = 0xdead0000ull;      // the explored function returns there
  u64 maxIns = 20000000;            // per run
  u32 runPages = 4096;              // pages a run may make or copy (16 MB); 0: no limit
  u32 confirmMs = 2500;             // the solver's time to prove that a branch side is impossible when tested replacements say so (else: listed as likely)
  u64 loopLimit = 50000;            // an endless loop is looked for after that many instructions with nothing new (engine.hpp); 0: never
  u32 tableMax = 256;               // loads from a table of at most that many entries are one expression (engine.hpp); 0: the address is fixed and enumerated
  bool lazy = false;                // operations are recorded while a path runs and built when read (engine.hpp); --lazy / UNSHROUD_LAZY=1
  u32 spinLimit = 20000;            // a run is stopped after that many decisions of one instruction (a loop bounded by an input); 0: never
  double timeLimit = 30.0;          // seconds for the function
  u32 maxRuns = 100000;
  u32 attempts = 4;                 // queries for one uncovered branch side, over all paths
  // A side which is impossible after the path which came to it but possible by itself is "blocked", not refuted: up to
  // `relax` of its visits are tried again with the longest part of the path before them which still allows the side
  // (a new input which reaches the branch another way). 0: no such check, such sides are listed as refuted.
  u32 relax = 2;
  double relaxShare = 0.25;         // of the time, at most, for the runs of those inputs and what they lead to
  u64 relaxMaxIns = 2000000;        // ... and the length of each of those runs (they are probes: a long loop is not what they are for)
  u32 relaxSpin = 2000;
  // A path whose queries are slow does not hold the others back: after this share of the time on one path, with other
  // work waiting, the rest of its decisions are queued behind that work (0: a path is finished before the next one).
  double slice = 0.05;
  u32 maxTargets = 32;              // values enumerated for one computed jump / symbolic address
  u32 maxPerSite = 512;             // value queries for one instruction, over all its expressions
  u32 enumPerVisit = 4;             // new values asked for one expression each time a path meets it
  double enumShare = 0.3;           // of the time, at most, for those values
  // A computed jump whose target depends on the inputs and can only be the one taken, visit after visit (an opaque
  // dispatcher in a loop), costs a proof each time: once those proofs took this share of the time without one other
  // target found, the instruction is not asked about any more (0: no such limit).
  double siteWaste = 0.2;
  bool addresses = true;            // enumerate symbolic addresses too
  bool pathMode = false;            // every feasible path (each branch flipped after every distinct prefix), not every edge
  // A path which ends inside a call of the function (the callee throws, ends the process, faults, never ends) names
  // the call: from then on, leaving that call out is a decision the explorer flips (Engine::havocSites) - the code of
  // the function after the call gets explored on the assumption that the call can return. [fnStart, fnEnd): the
  // function's own code (where the calls are looked for); 0: off.
  // First the function is explored as it is; the calls its paths ended in are kept. Then (when nothing is left to
  // try, or after havocAt of the time or of the runs) those calls are named, left out from there on, and the runs
  // which ended in them are made again.
  bool havoc = false; u64 fnStart = 0, fnEnd = 0; double havocAt = 0.6;
  // Forced branches (--force N): once the function is explored (or after forceAt of the time), the jumps whose other
  // side the solver could not reach (impossible, blocked, undecided, likely) are forced that way on a run which came to
  // them (1); 2: the jumps of the function's own code which went one way only, whatever the inputs, too. Paths through a
  // forced jump are assumed (JSON "forced"), what they cover is not in cov_plain.
  int force = 0; double forceAt = 0.75; int forceRounds = 3;   // rounds: what forced runs found is forced in the next one
  std::unordered_set<u64> dead;     // (jump << 1 | side) proved impossible by the jump's own code (unshroud_opaque): never forced
  std::vector<std::pair<u64, u64>> addressRanges;   // only those which fall in these ranges (tables, bytecode); empty: all
  SolveOptions solve;
};

struct PathInfo {
  std::vector<u64> inputs;          // the values which drive it
  Stop stop; u64 pc = 0; std::string info;
  Val rax{0, 0};
  std::vector<u32> branch;          // branch constraints (kind 0, computed targets), in order
  std::vector<u32> all;             // every constraint of the path (addresses and values made concrete too)
  u64 sig = 0;                      // signature of the decisions
  u64 ins = 0;
  u32 assumed = 0;                  // calls left out on the way (what the path found rests on their returning)
  u32 forced = 0;                   // jumps forced against their condition on the way
};

struct ExploreStats {
  u64 runs = 0, ins = 0, queries = 0, sat = 0, unsat = 0, unknown = 0, skipped = 0, relaxed = 0;
  u64 havocSites = 0;               // call sites named by paths which ended inside the call
  u64 forceSites = 0;               // jumps named for forcing
  u64 prefixIns = 0, symIns = 0;    // instructions run again up to the decision a run was made for; instructions which asked for expressions
  double tRun = 0, tSolve = 0, tAll = 0, tEnum = 0, tRelax = 0;
  std::map<std::string, u64> stages;
};

class Explorer {
public:
  Explorer(Engine& E, std::shared_ptr<State> start, std::vector<Input> inputs, const ExploreConfig& cfg);
  void run();
  std::vector<PathInfo> paths;                        // distinct paths
  std::set<std::pair<u64, u64>> edges;                // (branch, target) reached
  // (branch, target) never reached and impossible whatever came before: on each visit the rules folded the condition or
  // the solver found the side impossible by itself -> times
  std::map<std::pair<u64, u64>, int> refuted;
  std::set<std::pair<u64, u64>> blocked;              // (branch, target) never reached, impossible after the paths which came to it, possible (or not decided) by itself
  std::set<std::pair<u64, u64>> undecided;            // (branch, target) the solver gave up on
  std::set<std::pair<u64, u64>> foldedSides;          // (branch, target) the expression rules ruled out
  std::set<std::pair<u64, u64>> likely;               // (branch, target) with no model according to tested replacements, and no proof
  ExploreStats st;
  Solver S;
private:
  Engine& E;
  std::shared_ptr<State> start;
  std::vector<Input> inputs;
  ExploreConfig cfg;
  std::map<std::pair<u64, u64>, u32> asked;           // (branch, target or 0) -> queries made
  std::map<u64, std::set<u64>> values;                // expression made concrete (and, in path mode, the decisions before it) -> values seen
  std::set<u64> tried;                                // path mode: (decisions before, branch, other side) already asked
  std::map<u64, u32> perSite;                         // queries made for the values of one instruction
  std::map<u64, double> wasted;                       // ... and the time of those which found no other value, since the last one which did
  std::set<u64> sigs;
  std::set<u64> complete;                             // expressions whose every value is known
  struct Visit { std::shared_ptr<std::vector<u32>> conds; size_t at; u32 notCond; std::vector<u64> vals, model; bool done = false; };
  std::map<std::pair<u64, u64>, std::vector<Visit>> visits;   // blocked sides: where they were met
  std::map<std::pair<u64, u64>, u32> open;            // (branch, target) -> visits where the side was not impossible by itself
  std::unordered_map<u32, u8> aloneMemo;              // negated condition -> SatResult of the condition alone
  std::set<std::pair<u64, u64>> reachedFolded;        // (branch, target) taken where the rules decided the branch
  PathInfo execute(const std::vector<u64>& vals, bool probe = false);
  bool inRanges(u64 a) const;
  u64 blameCall();                  // the call of the function inside which the last run ended (0: none)
  std::unordered_map<u64, u64> callOf;                // return address -> its call instruction
  bool narrow(u32 expr);
};

}  // namespace unshroud
