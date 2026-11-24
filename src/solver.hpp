// unshroud - resolver: is a conjunction of 1-bit expressions satisfiable, and with which values?
// Stages, cheapest first: constraint slicing, cache, the current inputs, local search, a modular (low bits) proof of
// unsatisfiability, Bitwuzla.
#pragma once
#include "expr.hpp"
#include <unordered_map>
#include <vector>

namespace unshroud {

enum SatResult : int { SR_UNKNOWN = 0, SR_SAT = 1, SR_UNSAT = 2 };
inline const char* satName(SatResult r) { return r == SR_SAT ? "sat" : r == SR_UNSAT ? "unsat" : "unknown"; }

struct SolveOptions {
  u32 timeoutMs = 5000;            // Bitwuzla
  bool slicing = true, cache = true, seedCheck = true, localSearch = true, modular = true, smt = true;
  u32 lsBudget = 3000;             // local search: candidate assignments evaluated
  int modBits = 8;                 // modular proof: equalities checked modulo 2^1 .. 2^modBits
  int modMaxEnum = 20;             // modular proof: at most 2^modMaxEnum assignments enumerated
  bool simplify = true;            // MBA simplification of the constraints before the modular proof and the SMT solver
  bool bounds = true;              // bounds on one expression are merged before anything looks at the constraints
  bool lemmas = true;              // facts implied by overflow checks (z <= K / y: y * z <= K) are added to the query
  u32 simplifyMax = 6000;          // ... of queries of at most that many nodes
  bool race = true;                // the smaller (tested) query is solved on a second thread while the exact one runs
  u32 confirmMs = 0;               // > 0: Bitwuzla's time for a query which tested replacements say has no model (the proof is still needed); 0: all that is left
};

struct SolverStats {
  u64 queries = 0, cached = 0, trivial = 0, seedSat = 0, lsSat = 0, modUnsat = 0, smtSat = 0, smtUnsat = 0, unknown = 0, simplified = 0, likelyUnsat = 0, badModels = 0, races = 0;
  double tLs = 0, tMod = 0, tSmt = 0, tAll = 0, tSimp = 0;
  u64 tooBig = 0;                  // queries not given to the SMT solver: more than smtMaxNodes nodes (see Solver::smt)
  u64 keptCalls = 0, keptOver = 0, keptResets = 0, coreUnsat = 0, cores = 0, opposite = 0;   // the kept SMT solver; queries answered by a core / by a constraint and its negation
};

class Solver {
public:
  explicit Solver(Ctx& X);
  ~Solver();
  // path: constraints the seed satisfies (the current path); query: what is asked on top of them.
  // seed: values of all the variables (X.vars order). On SAT, model gets values for all the variables.
  SatResult check(const std::vector<u32>& path, const std::vector<u32>& query, const std::vector<u64>& seed,
                  std::vector<u64>* model, const SolveOptions& o, const char** stage = nullptr);
  SatResult checkCore(const std::vector<u32>& path, const std::vector<u32>& query, const std::vector<u64>& seed,
                      std::vector<u64>* model, const SolveOptions& o, const char** stage);
  // A variable with a place (VarInfo::place) which a model made a small non-zero number gets its place instead when
  // the path and the query still hold: a pointer to memory of its own rather than to page 0.
  void placeRepair(const std::vector<u32>& path, const std::vector<u32>& query, std::vector<u64>& m);
  u64 placeRepairs = 0;
  // the stages, on a plain list of constraints
  SatResult smt(const std::vector<u32>& conds, std::vector<u64>* model, u32 timeoutMs);
  bool localSearch(const std::vector<u32>& conds, std::vector<u64>& vals, u32 budget, u64 rngSeed);
  SatResult modular(const std::vector<u32>& conds, int maxBits, int maxEnum);
  // a == b whatever the values of the atoms (nodes replaced by free variables) and of the inputs: a proof by Bitwuzla, or false
  bool proveLocal(u32 a, u32 b, const u32* atoms, int na, u32 timeoutMs);
  int decideEq(u32 a, u32 b, const u32* atoms, int na, u32 timeoutMs);   // 1 proved equal, 2 a counterexample exists, 0 undecided
  u64 proofs = 0, proved = 0; double tProof = 0;
  // One SMT solver is kept for all the queries (their constraints are the assumptions of a check): what it has built
  // for one query serves the next ones, and when it says "unsat" it names the constraints which were needed - a core.
  // A later query which contains a core has no model either (asked again after a longer path, or on another path).
  // keepSmt = false (UNSHROUD_SMT_KEEP=0): a new solver for each query, no cores.
  bool keepSmt = true;
  SatResult smtNew(const std::vector<u32>& conds, std::vector<u64>* model, u32 timeoutMs);
  SatResult smtKept(const std::vector<u32>& conds, std::vector<u64>* model, u32 timeoutMs);
  std::vector<u32> lastCore;       // after smt(): the core of an "unsat" by the kept solver (empty otherwise)
  SolverStats stats;
  const std::vector<u32>& varsOf(u32 node);
  class Mba* mba = nullptr;        // every replacement (tested ones included)
  class Mba* mbaExact = nullptr;   // proved replacements only
private:
  void* keptBw = nullptr; void* keptOp = nullptr; double keptDeadline = 0; u32 keptChecks = 0, keptSlow = 0; bool keptOff = false;
  void keptReset();
  std::vector<std::vector<u32>> coreList; std::unordered_map<u32, std::vector<u32>> coreByMax;   // cores (sorted), by their largest constraint
  bool coreIn(const std::vector<u32>& key) const;
  void coreAdd(const std::vector<u32>& core);
  Ctx& X;
  void* tm = nullptr;                              // BitwuzlaTermManager
  void* tmX[2] = {nullptr, nullptr}; std::vector<void*> sortsX[2]; std::unordered_map<u32, void*> termsX[2];   // two more: other forms of a query, each on its own thread
  // the main form and up to two side forms (sound: an answer of theirs is an answer); from: 0 the main form, 1 + i a side form
  SatResult smtRace(const std::vector<u32>& exact, const std::vector<u32>* sides[2], const bool sideSound[2], const std::vector<u32>& orig,
                    const std::vector<u64>& base, std::vector<u64>* model, u32 timeoutMs, u32 confirmMs, bool& likely, int& from);
  std::unordered_map<u32, void*> terms;            // node -> BitwuzlaTerm
  std::vector<void*> sorts;                        // width -> BitwuzlaSort
  std::unordered_map<u32, std::vector<u32>> vcache;
  struct CacheE { std::vector<u32> key; SatResult r; std::vector<std::pair<u32, u64>> model; };
  std::unordered_map<u64, CacheE> qcache;
  void* term(u32 node);
  void* termIn(u32 node, std::unordered_map<u32, void*>& terms);
  void* sort(unsigned w);
};

// splits top-level conjunctions; drops constant-true constraints; returns false if one is constant false
bool flattenConds(Ctx& X, const std::vector<u32>& in, std::vector<u32>& out);

}  // namespace unshroud
