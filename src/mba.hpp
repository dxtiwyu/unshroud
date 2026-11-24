// unshroud - simplification of mixed boolean-arithmetic expressions.
// The arithmetic/bitwise part of an expression (+ - * & | ^ ~ neg) is viewed as a function of its atoms (every other
// subterm). Linear MBA: the values at the 2^t corner points (atoms 0/1) define the function; it is rebuilt in the
// simplest form found (conjunction basis, or a minimal boolean formula when it takes two values). Otherwise: bottom-up
// enumeration of small expressions over the atoms, matched on test inputs. Then the subterms, recursively.
#pragma once
#include "expr.hpp"
#include <unordered_map>
#include <unordered_set>

namespace unshroud {

class Solver;

struct MbaOptions {
  int maxAtoms = 8;          // corner method
  int synthAtoms = 4;        // synthesis
  int synthSize = 7;         // operations in a synthesized expression at most
  u32 synthMax = 300000;     // candidates kept at most
  int tests = 64;            // random assignments every result is checked on
  u32 proveMs = 0;           // > 0: results which are not exact by construction are proved with the SMT solver
  double budget = 1.0;       // seconds one simplify() / foldConditions() may take (then the rest is kept as it is)
  int synthVarsMax = 4;      // whole-expression synthesis over at most that many input variables (0: off)
  int synthVarsSize = 7;     // operations in such an expression at most
  u32 synthVarsMax2 = 1500000;  // candidates kept at most
  double mitmBudget = 1.0;   // seconds for the split search of one expression
  bool verifyAll = false;    // the check also where no rare case can hide (a proof attempt for every result: UNSHROUD_VERIFY_ALL)
  u32 narrowMs = 40;         // the solver's time for one replacement where a rare case can hide (it looks for a counterexample)
  u32 verifyMs = 100;        // a result which rests on tested replacements is given to the solver: a counterexample rejects it, a proof makes it exact (0: no check)
  bool exactOnly = false;    // only replacements which are proved (constructor rules, linear MBA identities by their corner values)
  bool slices = true;        // extractions are pushed down through the operations which let them through
  bool compare = true;       // conditions computed without a comparison are recognized (and proved by the solver)
  u32 proveLocalMs = 60;     // the solver's time for one such proof
  bool proveArith = false;   // with exactOnly: replacements which are not linear MBA identities are tried on the solver too
  bool legacy = false;       // the first simplifier (per-call enumeration), for comparisons (UNSHROUD_MBA_LEGACY)
  int pairMax = 40;          // descendants looked at as operands of what a node is equal to
  bool split = true;         // split search in the table for what is still big
  int splitCone = 0;         // ... for nodes of at most that many nodes (and the root)
};

struct MbaStats { u64 calls = 0, linear = 0, boolean = 0, constant = 0, synth = 0, proved = 0, tested = 0, kept = 0; double t = 0;
  u64 known = 0, table = 0, pair = 0, splits = 0, nodes = 0, rejected = 0, notFree = 0, cmpTried = 0, cmpProved = 0, verified = 0, refuted = 0, unverified = 0, polyTried = 0, polyProved = 0, refutedFinal = 0; double tTop = 0, tPair = 0, tSplit = 0, tCheck = 0, tPoly = 0; };

class Mba {
public:
  explicit Mba(Ctx& X, Solver* S = nullptr);
  ~Mba();
  u32 simplify(u32 e);                         // an equivalent expression, the smallest one found
  u32 simplifyOld(u32 e);                      // the first simplifier
  bool provePoly(u32 r, u32 cand, const std::unordered_set<u32>* forced = nullptr);   // the same polynomial over conjunctions of operands (poly.cpp): equal for every value
  bool lastExact = true;                       // the last simplify(): every replacement behind its result is proved
  u32 foldConditions(u32 e, Solver& S);         // ITE conditions / comparisons which are constant: replaced
  MbaOptions o; MbaStats st;
private:
  Ctx& X; Solver* S;
  std::unordered_map<u32, u32> memo;
  u32 top(u32 e, bool synth);                   // the methods on e itself (0: nothing better)
  u32 rebuild(u32 e);                           // e with simplified children
  u32 synthVars(u32 e);                         // a small expression over the inputs with the same values, or 0
  // by signatures (mba2.cpp)
  class Sigs* sg = nullptr;                     // values on uniform tests: what things are looked up by
  class Sigs* sg2 = nullptr;                    // values on sparse / small / dense tests: a second opinion before a replacement
  bool conservative = false;                    // only the region methods (after a result failed the final check)
  bool freed(u32 r, const u32* atoms, int na, int kind, u64 c);   // r as a function of free atoms: is it this operation on them?
  bool narrowProne(u32 root);
  bool finalCheck(u32 a, u32 b);                // the same values on many assignments (true comparisons)?
  std::unordered_map<u64, u32> bySig;           // signature -> the smallest node known with it
  std::unordered_map<u32, u64> improved;        // node -> what improve() made of it (<< 1), bit 0: by a replacement which is only tested
  std::unordered_map<u64, u8> noSplit;          // signatures the split search failed on
  std::unordered_set<u32> inexact;              // nodes whose simplified form rests on a replacement which is only tested
  bool topExact = false;                        // the last top(): its result is proved
  u32 slice(u32 e, unsigned lo, unsigned w);
  std::unordered_map<u64, u32> sliced; u32 sliceBudget = 0;
  std::unordered_map<u32, u32> sliceOf;         // an extraction of low bits -> what it is once pushed down (pass())
  u32 healBudget = 0;                           // direct proofs of a node against its final form, in one simplify() at most
  u32 narrowBudget = 0;                         // replacements checked by the solver where a rare case can hide, in one simplify() at most
  const char* how = "";                         // the method of the last replacement (for traces)
  bool acceptProved = false;                    // the last accept(): proved by the solver
  u32 constBudget = 0;                          // proofs that a node is a constant, in one simplify() at most
  u32 proofBudget = 0;                          // proofs asked from the solver in one simplify() at most
  bool pairProved = false;                      // the last pairSearch(): a comparison, proved
  bool proveLinear(u32 r, u32 cand, const std::unordered_set<u32>* forced);
  u32 pass(u32 root, double deadline);
  u32 improve(u32 r, bool isRoot, double deadline, bool& exact);
  u32 improveOnce(u32 r, bool isRoot, double deadline, bool& exact);
  u32 pairSearch(u32 r, bool& exact);
  u32 cmpSearch(u32 r);
  u32 accept(u32 r, u32 cand, u32& rNodes);     // cand if it has r's values and is smaller, else 0
  void record(u32 r);
};

}  // namespace unshroud
