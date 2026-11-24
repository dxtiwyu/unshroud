// unshroud - resolver
#include "solver.hpp"
#include "mba.hpp"
#include <bitwuzla/c/bitwuzla.h>
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <intrin.h>
#include <atomic>
#include <mutex>
#include <random>
#include <thread>
#include <condition_variable>

namespace unshroud {

static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

bool flattenConds(Ctx& X, const std::vector<u32>& in, std::vector<u32>& out) {
  std::vector<u32> st(in.rbegin(), in.rend());
  while (!st.empty()) {
    u32 c = st.back(); st.pop_back();
    const Node& x = X.N(c);
    if (x.op == O_CONST) { if (!(x.k & 1)) return false; continue; }
    if (x.op == O_AND && x.w == 1) { st.push_back(x.b); st.push_back(x.a); continue; }
    out.push_back(c);
  }
  return true;
}

Solver::Solver(Ctx& X) : X(X) {
  if (const char* e = getenv("UNSHROUD_SMT_KEEP")) keepSmt = *e && *e != 48;
  tm = bitwuzla_term_manager_new();
  sorts.assign(129, nullptr);
}

Solver::~Solver() { keptReset(); delete mba; delete mbaExact; bitwuzla_term_manager_delete((BitwuzlaTermManager*)tm); for (void* t : tmX) if (t) bitwuzla_term_manager_delete((BitwuzlaTermManager*)t); }

const std::vector<u32>& Solver::varsOf(u32 node) {
  auto it = vcache.find(node);
  if (it != vcache.end()) return it->second;
  std::vector<u32> v; X.collectVars(node, v);
  return vcache.emplace(node, std::move(v)).first->second;
}

// ------------------------------------------------------------------------------------------------ Bitwuzla
void* Solver::sort(unsigned w) {
  if (!sorts[w]) sorts[w] = bitwuzla_mk_bv_sort((BitwuzlaTermManager*)tm, w);
  return sorts[w];
}

void* Solver::term(u32 root) { return termIn(root, terms); }

void* Solver::termIn(u32 root, std::unordered_map<u32, void*>& terms) {
  auto* T = (BitwuzlaTermManager*)tm;
  std::vector<u32> st{root};
  auto S = [&](unsigned w) { return (BitwuzlaSort)sort(w); };
  auto t = [&](u32 id) { return (BitwuzlaTerm)terms[id]; };
  while (!st.empty()) {
    u32 id = st.back();
    if (terms.count(id)) { st.pop_back(); continue; }
    const Node x = X.N(id);
    bool ready = true;
    for (u32 c : {x.a, x.b, x.c}) if (c && !terms.count(c)) { st.push_back(c); ready = false; }
    if (!ready) continue;
    st.pop_back();
    const unsigned w = x.w;
    BitwuzlaTerm r = nullptr, one1 = bitwuzla_mk_bv_value_uint64(T, S(1), 1);
    auto b2 = [&](BitwuzlaKind k) { return bitwuzla_mk_term2(T, k, t(x.a), t(x.b)); };
    auto boolbv = [&](BitwuzlaTerm p) { return bitwuzla_mk_term3(T, BITWUZLA_KIND_ITE, p, one1, bitwuzla_mk_bv_value_uint64(T, S(1), 0)); };
    switch (x.op) {
    case O_CONST: r = bitwuzla_mk_bv_value_uint64(T, S(w), x.k); break;
    case O_VAR: {   // one constant per variable, whatever the map
      auto it = this->terms.find(id);
      if (it != this->terms.end()) r = (BitwuzlaTerm)it->second;
      else { r = bitwuzla_mk_const(T, S(w), X.vars[x.k].name.c_str()); this->terms[id] = r; }
      break;
    }
    case O_ADD: r = b2(BITWUZLA_KIND_BV_ADD); break;
    case O_MUL: r = b2(BITWUZLA_KIND_BV_MUL); break;
    case O_UDIV: case O_UREM: {
      // by a constant: the multiply-high form (what a compiler emits) is far cheaper to bit-blast than a divider.
      // Granlund-Montgomery: l = ceil(log2 d), m = ceil(2^(w+l) / d) < 2^(w+1): floor(x*m / 2^(w+l)) = floor(x / d)
      // off by default: Bitwuzla's rewriter knows urem(x, d) < d with the native form (the f03018 queries), not with this one
      static const bool divAsMul = getenv("UNSHROUD_DIV_AS_MUL") != nullptr;
      const u64 d = X.isC(x.b) ? X.cv(x.b) : 0;
      if (divAsMul && d > 1 && (d & (d - 1)) && w <= 64) {
        unsigned l = 64 - (unsigned)__lzcnt64(d - 1);            // ceil(log2 d)
        // m = ceil(2^(w+l) / d) as w+1 bits: computed with 128-bit arithmetic (no 128-bit division needed: long division)
        unsigned __int128 P = (unsigned __int128)1 << (w + l), q = 0, rem = 0;
        for (int i = (int)(w + l); i >= 0; i--) { rem = (rem << 1) | (unsigned)((P >> i) & 1); if (rem >= d) { rem -= d; q |= (unsigned __int128)1 << i; } }
        if (rem) q += 1;
        const unsigned W2 = 2 * w + 1;
        BitwuzlaTerm xs = bitwuzla_mk_term1_indexed1(T, BITWUZLA_KIND_BV_ZERO_EXTEND, t(x.a), W2 - w);
        // the constant m, as a W2-bit value: high and low 64-bit halves
        BitwuzlaTerm mlo = bitwuzla_mk_bv_value_uint64(T, S(W2 <= 64 ? W2 : 64), (u64)q);
        BitwuzlaTerm mt = W2 <= 64 ? mlo : bitwuzla_mk_term2(T, BITWUZLA_KIND_BV_CONCAT, bitwuzla_mk_bv_value_uint64(T, S(W2 - 64), (u64)(q >> 64)), mlo);
        BitwuzlaTerm prod = bitwuzla_mk_term2(T, BITWUZLA_KIND_BV_MUL, xs, mt);
        // x*m < 2^(2w+1): the quotient is the top w+1-l bits of the product
        BitwuzlaTerm quo = bitwuzla_mk_term1_indexed2(T, BITWUZLA_KIND_BV_EXTRACT, prod, W2 - 1, w + l);
        if (w + 1 - l < w) quo = bitwuzla_mk_term1_indexed1(T, BITWUZLA_KIND_BV_ZERO_EXTEND, quo, l - 1);
        if (x.op == O_UDIV) r = quo;
        else r = bitwuzla_mk_term2(T, BITWUZLA_KIND_BV_SUB, t(x.a), bitwuzla_mk_term2(T, BITWUZLA_KIND_BV_MUL, quo, t(x.b)));
      } else r = b2(x.op == O_UDIV ? BITWUZLA_KIND_BV_UDIV : BITWUZLA_KIND_BV_UREM);
      break;
    }
    case O_SDIV: r = b2(BITWUZLA_KIND_BV_SDIV); break;
    case O_SREM: r = b2(BITWUZLA_KIND_BV_SREM); break;
    case O_MULHU: case O_MULHS: {
      BitwuzlaKind ek = x.op == O_MULHU ? BITWUZLA_KIND_BV_ZERO_EXTEND : BITWUZLA_KIND_BV_SIGN_EXTEND;
      BitwuzlaTerm a2 = bitwuzla_mk_term1_indexed1(T, ek, t(x.a), w), b22 = bitwuzla_mk_term1_indexed1(T, ek, t(x.b), w);
      r = bitwuzla_mk_term1_indexed2(T, BITWUZLA_KIND_BV_EXTRACT, bitwuzla_mk_term2(T, BITWUZLA_KIND_BV_MUL, a2, b22), 2 * w - 1, w);
      break;
    }
    case O_NEG: r = bitwuzla_mk_term1(T, BITWUZLA_KIND_BV_NEG, t(x.a)); break;
    case O_AND: r = b2(BITWUZLA_KIND_BV_AND); break;
    case O_OR: r = b2(BITWUZLA_KIND_BV_OR); break;
    case O_XOR: r = b2(BITWUZLA_KIND_BV_XOR); break;
    case O_NOT: r = bitwuzla_mk_term1(T, BITWUZLA_KIND_BV_NOT, t(x.a)); break;
    case O_SHL: r = b2(BITWUZLA_KIND_BV_SHL); break;
    case O_LSHR: r = b2(BITWUZLA_KIND_BV_SHR); break;
    case O_ASHR: r = b2(BITWUZLA_KIND_BV_ASHR); break;
    case O_ROL: case O_ROR:
      if (X.isC(x.b)) r = bitwuzla_mk_term1_indexed1(T, x.op == O_ROL ? BITWUZLA_KIND_BV_ROLI : BITWUZLA_KIND_BV_RORI, t(x.a), X.cv(x.b) % w);
      else r = b2(x.op == O_ROL ? BITWUZLA_KIND_BV_ROL : BITWUZLA_KIND_BV_ROR);
      break;
    case O_EXTRACT: r = bitwuzla_mk_term1_indexed2(T, BITWUZLA_KIND_BV_EXTRACT, t(x.a), x.lo + w - 1, x.lo); break;
    case O_ZEXT: r = bitwuzla_mk_term1_indexed1(T, BITWUZLA_KIND_BV_ZERO_EXTEND, t(x.a), w - x.lo); break;
    case O_SEXT: r = bitwuzla_mk_term1_indexed1(T, BITWUZLA_KIND_BV_SIGN_EXTEND, t(x.a), w - x.lo); break;
    case O_CONCAT: r = b2(BITWUZLA_KIND_BV_CONCAT); break;
    case O_ITE: r = bitwuzla_mk_term3(T, BITWUZLA_KIND_ITE, bitwuzla_mk_term2(T, BITWUZLA_KIND_EQUAL, t(x.a), one1), t(x.b), t(x.c)); break;
    case O_EQ: r = boolbv(b2(BITWUZLA_KIND_EQUAL)); break;
    case O_ULT: r = boolbv(b2(BITWUZLA_KIND_BV_ULT)); break;
    case O_ULE: r = boolbv(b2(BITWUZLA_KIND_BV_ULE)); break;
    case O_SLT: r = boolbv(b2(BITWUZLA_KIND_BV_SLT)); break;
    case O_SLE: r = boolbv(b2(BITWUZLA_KIND_BV_SLE)); break;
    case O_POPCNT: {
      r = bitwuzla_mk_bv_value_uint64(T, S(w), 0);
      for (unsigned i = 0; i < x.lo; i++)
        r = bitwuzla_mk_term2(T, BITWUZLA_KIND_BV_ADD, r, bitwuzla_mk_term1_indexed1(T, BITWUZLA_KIND_BV_ZERO_EXTEND, bitwuzla_mk_term1_indexed2(T, BITWUZLA_KIND_BV_EXTRACT, t(x.a), i, i), w - 1));
      break;
    }
    case O_CLZ: case O_CTZ: {
      r = bitwuzla_mk_bv_value_uint64(T, S(w), x.lo);
      for (unsigned j = 0; j < x.lo; j++) {
        unsigned bit = x.op == O_CTZ ? x.lo - 1 - j : j;              // the last test wins: highest priority last
        unsigned val = x.op == O_CTZ ? bit : x.lo - 1 - bit;
        BitwuzlaTerm set = bitwuzla_mk_term2(T, BITWUZLA_KIND_EQUAL, bitwuzla_mk_term1_indexed2(T, BITWUZLA_KIND_BV_EXTRACT, t(x.a), bit, bit), one1);
        r = bitwuzla_mk_term3(T, BITWUZLA_KIND_ITE, set, bitwuzla_mk_bv_value_uint64(T, S(w), val), r);
      }
      break;
    }
    default: fprintf(stderr, "unshroud: no Bitwuzla form for %s\n", opName(x.op)); abort();
    }
    terms[id] = r;
  }
  return terms[root];
}

static int32_t keptStop(void* p) { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count() > *(double*)p ? 1 : 0; }

void Solver::keptReset() {
  if (!keptBw) return;
  bitwuzla_delete((Bitwuzla*)keptBw); bitwuzla_options_delete((BitwuzlaOptions*)keptOp);
  keptBw = nullptr; keptOp = nullptr; keptChecks = 0;
}

// the values of the variables of conds, out of a solver which just said "sat"
static void readModel(Ctx& X, Solver& S, Bitwuzla* bw, const std::vector<u32>& conds, std::vector<u64>& model, void* (*termOf)(Solver&, u32)) {
  std::vector<u32> vs;
  for (u32 c : conds) for (u32 v : S.varsOf(c)) vs.push_back(v);
  std::sort(vs.begin(), vs.end()); vs.erase(std::unique(vs.begin(), vs.end()), vs.end());
  for (u32 v : vs) {
    BitwuzlaTerm val = bitwuzla_get_value(bw, (BitwuzlaTerm)termOf(S, X.varNode(v)));
    model[v] = strtoull(bitwuzla_term_value_get_str_fmt(val, 16), nullptr, 16);
  }
}

SatResult Solver::smtNew(const std::vector<u32>& conds, std::vector<u64>* model, u32 timeoutMs) {
  auto* T = (BitwuzlaTermManager*)tm;
  BitwuzlaOptions* op = bitwuzla_options_new();
  bitwuzla_set_option(op, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  if (timeoutMs) bitwuzla_set_option(op, BITWUZLA_OPT_TIME_LIMIT_PER, timeoutMs);
  Bitwuzla* bw = bitwuzla_new(T, op);
  BitwuzlaTerm one1 = bitwuzla_mk_bv_value_uint64(T, (BitwuzlaSort)sort(1), 1);
  for (u32 c : conds) bitwuzla_assert(bw, bitwuzla_mk_term2(T, BITWUZLA_KIND_EQUAL, (BitwuzlaTerm)term(c), one1));
  const BitwuzlaResult r = bitwuzla_check_sat(bw);
  const SatResult res = r == BITWUZLA_SAT ? SR_SAT : r == BITWUZLA_UNSAT ? SR_UNSAT : SR_UNKNOWN;
  if (res == SR_SAT && model) readModel(X, *this, bw, conds, *model, [](Solver& s, u32 n) { return s.term(n); });
  bitwuzla_delete(bw);
  bitwuzla_options_delete(op);
  return res;
}

SatResult Solver::smtKept(const std::vector<u32>& conds, std::vector<u64>* model, u32 timeoutMs) {
  auto* T = (BitwuzlaTermManager*)tm;
  if (keptBw && keptChecks >= 256) { keptReset(); stats.keptResets++; }       // (what it holds of old queries only grows)
  if (!keptBw) {
    BitwuzlaOptions* op = bitwuzla_options_new();
    bitwuzla_set_option(op, BITWUZLA_OPT_PRODUCE_MODELS, 1);
    bitwuzla_set_option(op, BITWUZLA_OPT_PRODUCE_UNSAT_ASSUMPTIONS, 1);
    keptOp = op; keptBw = bitwuzla_new(T, op);
    bitwuzla_set_termination_callback((Bitwuzla*)keptBw, keptStop, &keptDeadline);
  }
  Bitwuzla* bw = (Bitwuzla*)keptBw;
  keptDeadline = std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count() + (timeoutMs ? timeoutMs : 3600000u) / 1000.0;
  BitwuzlaTerm one1 = bitwuzla_mk_bv_value_uint64(T, (BitwuzlaSort)sort(1), 1);
  std::vector<BitwuzlaTerm> as; as.reserve(conds.size());
  for (u32 c : conds) as.push_back(bitwuzla_mk_term2(T, BITWUZLA_KIND_EQUAL, (BitwuzlaTerm)term(c), one1));
  keptChecks++; stats.keptCalls++;
  const BitwuzlaResult r = bitwuzla_check_sat_assuming(bw, (uint32_t)as.size(), as.data());
  const SatResult res = r == BITWUZLA_SAT ? SR_SAT : r == BITWUZLA_UNSAT ? SR_UNSAT : SR_UNKNOWN;
  if (res == SR_SAT && model) readModel(X, *this, bw, conds, *model, [](Solver& s, u32 n) { return s.term(n); });
  if (res == SR_UNSAT) {
    size_t n = 0; const BitwuzlaTerm* ua = bitwuzla_get_unsat_assumptions(bw, &n);
    for (size_t i = 0; i < n; i++) for (size_t k = 0; k < as.size(); k++) if (ua[i] == as[k]) { lastCore.push_back(conds[k]); break; }
    std::sort(lastCore.begin(), lastCore.end()); lastCore.erase(std::unique(lastCore.begin(), lastCore.end()), lastCore.end());
  }
  return res;
}

// The kept solver first, for a share of the time: when what it carries of earlier queries makes it slow on this one,
// a new solver takes over (and after that happened a few times, the kept one is given up).
SatResult Solver::smt(const std::vector<u32>& conds, std::vector<u64>* model, u32 timeoutMs) {
  lastCore.clear();
  // Bitwuzla rewrites what it is given before it looks at its time limit, and that pass can take minutes on a
  // condition of hundreds of thousands of nodes (measured: 283,024 nodes, a function of a protected sample under --uc: the
  // process ran 10 minutes past a 10 s budget). Such a query is not asked: unknown.
  { static const u64 smtMaxNodes = getenv("UNSHROUD_SMT_MAXNODES") ? strtoull(getenv("UNSHROUD_SMT_MAXNODES"), nullptr, 0) : 100000;
    u64 tot = 0; for (u32 c : conds) { tot += X.N(c).size < 64 ? X.N(c).size : X.countNodes(c); if (tot > smtMaxNodes) { stats.tooBig++; return SR_UNKNOWN; } } }
  if (!keepSmt || keptOff) return smtNew(conds, model, timeoutMs);
  const u32 share = 40;
  if (timeoutMs && timeoutMs <= share) return smtKept(conds, model, timeoutMs);
  SatResult r = smtKept(conds, model, share);
  if (r != SR_UNKNOWN) return r;
  stats.keptOver++; keptReset();
  const double t = now();
  r = smtNew(conds, model, timeoutMs ? timeoutMs - share : 0);
  if (now() - t < share / 2000.0 && ++keptSlow >= 3) keptOff = true;           // the new one was quick where the kept one was not
  return r;
}

bool Solver::coreIn(const std::vector<u32>& key) const {
  if (coreList.empty()) return false;
  for (u32 c : key) {
    auto it = coreByMax.find(c);
    if (it == coreByMax.end()) continue;
    for (u32 i : it->second) { const std::vector<u32>& core = coreList[i]; if (core.size() <= key.size() && std::includes(key.begin(), key.end(), core.begin(), core.end())) return true; }
  }
  return false;
}

void Solver::coreAdd(const std::vector<u32>& core) {
  if (core.empty() || coreList.size() >= 200000) return;
  auto& at = coreByMax[core.back()];
  for (u32 i : at) if (coreList[i] == core) return;
  at.push_back((u32)coreList.size()); coreList.push_back(core); stats.cores++;
}

// a == b for every value of the atoms (free variables in place of these nodes) and of the inputs: true when proved
bool Solver::proveLocal(u32 a, u32 b, const u32* atoms, int na, u32 timeoutMs) { return decideEq(a, b, atoms, na, timeoutMs) == 1; }

// 1: a == b always (proved), 2: they differ for some values (a counterexample exists), 0: not decided in time
int Solver::decideEq(u32 a, u32 b, const u32* atoms, int na, u32 timeoutMs) {
  const double t0 = now();
  auto* T = (BitwuzlaTermManager*)tm;
  std::unordered_map<u32, void*> local;
  for (int i = 0; i < na; i++) {
    if (!atoms[i]) continue;
    char name[32]; snprintf(name, sizeof name, "atom%d_%u", i, (unsigned)proofs);
    local[atoms[i]] = bitwuzla_mk_const(T, (BitwuzlaSort)sort(X.W(atoms[i])), name);
  }
  BitwuzlaOptions* op = bitwuzla_options_new();
  bitwuzla_set_option(op, BITWUZLA_OPT_TIME_LIMIT_PER, timeoutMs ? timeoutMs : 1);
  Bitwuzla* bw = bitwuzla_new(T, op);
  bitwuzla_assert(bw, bitwuzla_mk_term2(T, BITWUZLA_KIND_DISTINCT, (BitwuzlaTerm)termIn(a, local), (BitwuzlaTerm)termIn(b, local)));
  BitwuzlaResult r = bitwuzla_check_sat(bw);
  bitwuzla_delete(bw);
  bitwuzla_options_delete(op);
  proofs++; if (r == BITWUZLA_UNSAT) proved++;
  tProof += now() - t0;
  return r == BITWUZLA_UNSAT ? 1 : r == BITWUZLA_SAT ? 2 : 0;
}

// ------------------------------------------------------------------------------------------------ several forms of one query at once
// The query as it was, its exactly simplified form (both sound), and its smaller form by tested replacements, each on a
// thread of its own with its own term manager. A smaller form is not always easier for the solver (a product which the
// other constraints share is gone): whichever sound form answers first is the answer. A model of the tested form is
// checked against the constraints as they were; "no model" there proves nothing (reported through `likely`).
namespace {
struct Race {
  Ctx* X;
  std::atomic<bool> stopAll{false};
  std::atomic<int> status[2];                     // of the side forms: 0 running, 1 model ready, 2 no model, 3 gave up
  bool sound[2] = {false, false};
  std::vector<std::pair<u32, u64>> sideModel[2];
  std::mutex values;                              // reading values out of a solver (the C API formats them into its own buffers)
  std::mutex wake; std::condition_variable cv;    // a side form which waits for its turn is woken when the answer is there
  const std::vector<u32>* orig; const std::vector<u64>* base;
  std::vector<u64> good; int goodFrom = -1; bool checked[2] = {false, false};
  double deadline = 0, likelyAt = 0; u32 confirmMs = 0;
  // on the main thread only (the evaluator is not shared between threads)
  void checkSide(int i) {
    if (checked[i]) return;
    checked[i] = true;
    std::vector<u64> m(*base);
    for (auto& kv : sideModel[i]) m[kv.first] = kv.second;
    bool ok = true;
    for (u32 c : *orig) if (!(X->eval(c, m.data()) & 1)) { ok = false; break; }
    if (ok && goodFrom < 0) { good = m; goodFrom = i; }
  }
};
static double nowS() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }
static int32_t mainStop(void* p) {
  Race* r = (Race*)p;
  for (int i = 0; i < 2; i++) {
    const int s = r->status[i].load();
    if (s == 1) { r->checkSide(i); if (r->goodFrom >= 0) return 1; }
    if (s == 2 && r->sound[i]) return 1;
    if (s == 2 && !r->sound[i] && r->confirmMs && nowS() - r->likelyAt > r->confirmMs / 1000.0) return 1;
  }
  return r->stopAll.load() || nowS() > r->deadline ? 1 : 0;
}
static int32_t sideStop(void* p) { Race* r = (Race*)p; return r->stopAll.load() || nowS() > r->deadline ? 1 : 0; }
}

SatResult Solver::smtRace(const std::vector<u32>& exact, const std::vector<u32>* sides[2], const bool sideSound[2], const std::vector<u32>& orig,
                          const std::vector<u64>& base, std::vector<u64>* model, u32 timeoutMs, u32 confirmMs, bool& likely, int& from) {
  likely = false; from = 0;
  Race R; R.X = &X; R.orig = &orig; R.base = &base; R.deadline = nowS() + timeoutMs / 1000.0 + 0.05; R.confirmMs = confirmMs;
  R.status[0] = 3; R.status[1] = 3;
  Bitwuzla* B[2] = {nullptr, nullptr}; BitwuzlaOptions* opB[2] = {nullptr, nullptr};
  std::vector<std::pair<u32, BitwuzlaTerm>> sideVars[2];
  // the side forms, each in a term manager of its own (everything is built on this thread)
  for (int i = 0; i < 2; i++) {
    if (!sides[i]) continue;
    R.status[i] = 0; R.sound[i] = sideSound[i];
    if (!tmX[i]) { tmX[i] = bitwuzla_term_manager_new(); sortsX[i].assign(129, nullptr); }
    std::swap(tm, tmX[i]); sorts.swap(sortsX[i]); terms.swap(termsX[i]);
    opB[i] = bitwuzla_options_new();
    bitwuzla_set_option(opB[i], BITWUZLA_OPT_PRODUCE_MODELS, 1);
    bitwuzla_set_option(opB[i], BITWUZLA_OPT_TIME_LIMIT_PER, timeoutMs);
    B[i] = bitwuzla_new((BitwuzlaTermManager*)tm, opB[i]);
    BitwuzlaTerm one1 = bitwuzla_mk_bv_value_uint64((BitwuzlaTermManager*)tm, (BitwuzlaSort)sort(1), 1);
    for (u32 c : *sides[i]) bitwuzla_assert(B[i], bitwuzla_mk_term2((BitwuzlaTermManager*)tm, BITWUZLA_KIND_EQUAL, (BitwuzlaTerm)term(c), one1));
    std::vector<u32> vs;
    for (u32 c : *sides[i]) for (u32 v : varsOf(c)) vs.push_back(v);
    std::sort(vs.begin(), vs.end()); vs.erase(std::unique(vs.begin(), vs.end()), vs.end());
    for (u32 v : vs) sideVars[i].push_back({v, (BitwuzlaTerm)term(X.varNode(v))});
    std::swap(tm, tmX[i]); sorts.swap(sortsX[i]); terms.swap(termsX[i]);
    bitwuzla_set_termination_callback(B[i], sideStop, &R);
  }
  // the main form
  auto* T = (BitwuzlaTermManager*)tm;
  BitwuzlaOptions* opA = bitwuzla_options_new();
  bitwuzla_set_option(opA, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  bitwuzla_set_option(opA, BITWUZLA_OPT_TIME_LIMIT_PER, timeoutMs);
  Bitwuzla* A = bitwuzla_new(T, opA);
  BitwuzlaTerm one1 = bitwuzla_mk_bv_value_uint64(T, (BitwuzlaSort)sort(1), 1);
  for (u32 c : exact) bitwuzla_assert(A, bitwuzla_mk_term2(T, BITWUZLA_KIND_EQUAL, (BitwuzlaTerm)term(c), one1));
  bitwuzla_set_termination_callback(A, mainStop, &R);
  std::thread th[2];
  for (int i = 0; i < 2; i++) {
    if (!B[i]) continue;
    th[i] = std::thread([&, i] {
      // the query as it was starts a little later: most of the time the main form has answered by then
      if (R.sound[i]) {
        const double startAt = nowS() + std::min(1.0, std::max(0.1, timeoutMs / 20000.0));
        { std::unique_lock<std::mutex> lk(R.wake); R.cv.wait_for(lk, std::chrono::duration<double>(startAt - nowS()), [&] { return R.stopAll.load(); }); }
        if (R.stopAll.load()) { R.status[i] = 3; return; }
      }
      BitwuzlaResult rb = bitwuzla_check_sat(B[i]);
      if (rb == BITWUZLA_SAT) {
        std::lock_guard<std::mutex> g(R.values);
        for (auto& kv : sideVars[i]) { const char* s = bitwuzla_term_value_get_str_fmt(bitwuzla_get_value(B[i], kv.second), 16); R.sideModel[i].push_back({kv.first, strtoull(s, nullptr, 16)}); }
        R.status[i] = 1;
      } else if (rb == BITWUZLA_UNSAT) { if (!R.sound[i]) R.likelyAt = nowS(); R.status[i] = 2; }
      else R.status[i] = 3;
    });
  }
  BitwuzlaResult ra = bitwuzla_check_sat(A);
  SatResult res = ra == BITWUZLA_SAT ? SR_SAT : ra == BITWUZLA_UNSAT ? SR_UNSAT : SR_UNKNOWN;
  if (res == SR_SAT && model) {
    std::lock_guard<std::mutex> g(R.values);
    std::vector<u32> vs;
    for (u32 c : exact) for (u32 v : varsOf(c)) vs.push_back(v);
    std::sort(vs.begin(), vs.end()); vs.erase(std::unique(vs.begin(), vs.end()), vs.end());
    for (u32 v : vs) { const char* s = bitwuzla_term_value_get_str_fmt(bitwuzla_get_value(A, (BitwuzlaTerm)term(X.varNode(v))), 16); (*model)[v] = strtoull(s, nullptr, 16); }
  }
  { std::lock_guard<std::mutex> g(R.wake); R.stopAll = true; }    // the answer is there, or this form gave up: the others have had the same time
  R.cv.notify_all();
  for (int i = 0; i < 2; i++) if (th[i].joinable()) th[i].join();
  if (res == SR_UNKNOWN) {
    for (int i = 0; i < 2; i++) if (R.status[i].load() == 1) R.checkSide(i);
    if (R.goodFrom >= 0) { if (model) *model = R.good; res = SR_SAT; from = 1 + R.goodFrom; }
    else {
      for (int i = 0; i < 2; i++) {
        const int s = R.status[i].load();
        if (s == 2 && R.sound[i]) { res = SR_UNSAT; from = 1 + i; }
        else if (s == 2) likely = true;
        else if (s == 1) stats.badModels++;
      }
    }
  }
  bitwuzla_delete(A); bitwuzla_options_delete(opA);
  for (int i = 0; i < 2; i++) if (B[i]) { bitwuzla_delete(B[i]); bitwuzla_options_delete(opB[i]); }
  return res;
}

// ------------------------------------------------------------------------------------------------ compiled evaluation
namespace {
struct Prog {
  struct I { u8 op, w, lo; u32 a, b, c; u64 k; };
  std::vector<I> ins; std::vector<u64> val;
  std::vector<u32> roots;                    // positions of the constraints
  std::vector<u32> varPos;                   // variable index -> position of its node (or ~0)
  std::unordered_map<u32, u32> pos;          // node id -> position
  void build(Ctx& X, const std::vector<u32>& conds, size_t nvars) {
    varPos.assign(nvars, ~0u);
    // position 0 is "no operand" (a zero): a real node there would be taken for a missing one wherever an operand is tested
    static const bool oldBug = getenv("UNSHROUD_PROG0_BUG") != nullptr;   // (to measure what the bug did: the old numbering)
    if (ins.empty() && !oldBug) ins.push_back({O_CONST, 64, 0, 0, 0, 0, 0});
    std::vector<std::pair<u32, int>> st;
    for (u32 root : conds) {
      st.push_back({root, 0});
      while (!st.empty()) {
        auto& top = st.back(); u32 id = top.first;
        if (pos.count(id)) { st.pop_back(); continue; }
        const Node& x = X.N(id);
        u32 kids[3] = {x.a, x.b, x.c};
        if (top.second < 3) { u32 c = kids[top.second++]; if (c && !pos.count(c)) st.push_back({c, 0}); continue; }
        u32 p = (u32)ins.size();
        ins.push_back({x.op, x.w, x.lo, x.a ? pos[x.a] : 0, x.b ? pos[x.b] : 0, x.c ? pos[x.c] : 0, x.k});
        pos[id] = p;
        if (x.op == O_VAR) varPos[x.k] = p;
        st.pop_back();
      }
      roots.push_back(pos[root]);
    }
    val.assign(ins.size(), 0);
  }
  void run(const std::vector<u64>& vars) {
    const size_t n = ins.size();
    for (size_t i = 0; i < n; i++) {
      const I& x = ins[i];
      if (x.op == O_CONST) val[i] = x.k;
      else if (x.op == O_VAR) val[i] = vars[x.k] & maskOf(x.w);
      else val[i] = evalOp(x.op, x.w, x.lo, x.k, val[x.a], val[x.b], val[x.c]);
    }
  }
  // how far constraint j is from holding (0: it holds)
  double dist(u32 j) const {
    const I& x = ins[roots[j]];
    if (val[roots[j]] & 1) return 0;
    auto mag = [](u64 d) { unsigned long b; return _BitScanReverse64(&b, d) ? (double)(b + 1) / 64.0 : 0.0; };
    switch (x.op) {
    case O_EQ: return 1.0 + __popcnt64(val[x.a] ^ val[x.b]) / 64.0;
    case O_ULT: case O_ULE: return 1.0 + mag(val[x.a] - val[x.b] + 1);
    case O_SLT: case O_SLE: return 1.0 + mag((val[x.a] - val[x.b] + 1) & maskOf(x.lo));
    default: return 1.0;
    }
  }
};
}

bool Solver::localSearch(const std::vector<u32>& conds, std::vector<u64>& vals, u32 budget, u64 rngSeed) {
  Prog P; P.build(X, conds, X.vars.size());
  std::mt19937_64 rng(rngSeed);
  // variables of each constraint, constants of the formula
  std::vector<std::vector<u32>> cv(conds.size());
  for (size_t j = 0; j < conds.size(); j++) cv[j] = varsOf(conds[j]);
  std::vector<u64> consts;
  for (auto& x : P.ins) if (x.op == O_CONST && x.w > 1) { consts.push_back(x.k); consts.push_back(x.k + 1); consts.push_back(x.k - 1); consts.push_back(0 - x.k); }
  std::sort(consts.begin(), consts.end()); consts.erase(std::unique(consts.begin(), consts.end()), consts.end());
  auto score = [&](double& s) { P.run(vals); s = 0; int bad = 0; for (u32 j = 0; j < conds.size(); j++) { double d = P.dist(j); if (d > 0) { s += d; bad++; } } return bad; };
  double cur; int bad = score(cur);
  if (!bad) return true;
  std::vector<u64> best = vals; double bestScore = cur;
  u32 evals = 0;
  // each candidate evaluates the whole formula: on a long path (thousands of constraints) the search gets fewer of them
  budget = (u32)std::min<u64>(budget, std::max<u64>(96, 6000000ull / std::max<size_t>(1, P.ins.size())));
  while (evals < budget) {
    // a constraint which does not hold
    std::vector<u32> broken;
    for (u32 j = 0; j < conds.size(); j++) if (!(P.val[P.roots[j]] & 1)) broken.push_back(j);
    if (broken.empty()) return true;
    u32 j = broken[rng() % broken.size()];
    if (cv[j].empty()) return false;                           // a constant constraint which does not hold
    // candidate moves on its variables
    u32 bv = 0; u64 bval = 0; double bs = cur; bool found = false;
    for (u32 v : cv[j]) {
      const unsigned w = X.vars[v].w; const u64 m = maskOf(w), old = vals[v];
      u64 cand[48]; int nc = 0;
      if (w == 64 && X.vars[v].place && old < 0x10000) cand[nc++] = X.vars[v].place;   // (a pointer to memory of its own first)
      cand[nc++] = old + 1; cand[nc++] = old - 1; cand[nc++] = 0 - old; cand[nc++] = ~old; cand[nc++] = old << 1; cand[nc++] = old >> 1;
      cand[nc++] = 0; cand[nc++] = 1; cand[nc++] = m; cand[nc++] = signBit(w); cand[nc++] = rng();
      for (int i = 0; i < 12; i++) cand[nc++] = old ^ (1ull << (rng() % w));
      for (int i = 0; i < 4; i++) { unsigned b = (unsigned)(rng() % ((w + 7) / 8)); cand[nc++] = (old & ~(0xffull << (8 * b))) | ((rng() & 0xff) << (8 * b)); }
      for (int i = 0; i < 8 && !consts.empty(); i++) cand[nc++] = consts[rng() % consts.size()];
      for (int i = 0; i < 4; i++) cand[nc++] = 1ull << (rng() % w);
      for (int i = 0; i < nc; i++) {
        u64 c = cand[i] & m;
        if (c == old) continue;
        vals[v] = c; double s; score(s); evals++;
        if (s < bs) { bs = s; bv = v; bval = c; found = true; if (s == 0) break; }
      }
      vals[v] = old;
      if (found && bs == 0) break;
    }
    if (found) { vals[bv] = bval; bad = score(cur); evals++; if (!bad) return true; if (cur < bestScore) { bestScore = cur; best = vals; } continue; }
    // no improvement: random move on one variable of the constraint, or back to the best seen
    if (rng() % 8 == 0) vals = best;
    else { u32 v = cv[j][rng() % cv[j].size()]; vals[v] = (rng() % 2 ? rng() : vals[v] ^ (1ull << (rng() % X.vars[v].w))) & maskOf(X.vars[v].w); }
    bad = score(cur); evals++;
    if (!bad) return true;
  }
  return false;
}

// ------------------------------------------------------------------------------------------------ modular proof
// Equalities at the top level are checked modulo 2^k (if a 64-bit assignment satisfies them, its low k bits do); every
// other node is evaluated exactly at the precision its users need. A constraint whose variables would need more than
// `cap` bits is left out (weaker, still sound). No assignment of the low bits satisfies what is kept: unsatisfiable.
SatResult Solver::modular(const std::vector<u32>& conds, int maxBits, int maxEnum) {
  Prog P; P.build(X, conds, X.vars.size());
  const size_t n = P.ins.size(); const u32 nr = (u32)conds.size();
  if ((u64)nr * n > 12000000ull) return SR_UNKNOWN;   // the demands of each constraint are followed through the whole formula: not on a long path
  const int cap = 16;
  std::vector<u8> need(n), one(n);
  // A subterm whose low bits do not follow from the low bits of its operands (a rotation, a division, a comparison, a
  // shift to the right past the precision) is cut: its low bits are enumerated as if it were a variable. Every value it
  // can take is among those tried, so "no assignment" is still a proof.
  std::vector<u8> cutOne(n), cutAny(n);
  std::vector<u8> reduced(nr);
  std::vector<u32> vlist;
  for (int k : {1, 2, 3, 4, 6, 8, 12, 16}) {
    if (k > maxBits) break;
    std::fill(need.begin(), need.end(), 0); std::fill(cutAny.begin(), cutAny.end(), 0);
    std::vector<u8> keep(nr, 0); int kept = 0;
    // per constraint: its demands alone, to decide whether it is kept (exactly first; then with cuts)
    for (u32 j = 0; j < nr; j++) {
      const auto& r = P.ins[P.roots[j]];
      reduced[j] = r.op == O_EQ;
      bool ok = false;
      for (int cuts = 0; cuts < 2 && !ok; cuts++) {
        std::fill(one.begin(), one.end(), 0); std::fill(cutOne.begin(), cutOne.end(), 0);
        if (reduced[j]) { u8 d = (u8)std::min<int>(k, P.ins[r.a].w); one[r.a] = std::max(one[r.a], d); one[r.b] = std::max(one[r.b], d); }
        else one[P.roots[j]] = 1;
        ok = true;
        for (size_t i = n; i-- > 0 && ok;) {
          if (!one[i]) continue;
          const auto& x = P.ins[i]; const unsigned p = one[i];
          auto dem = [&](u32 c, unsigned d) { d = std::min<unsigned>(d, P.ins[c].w); if (d > one[c]) one[c] = (u8)d; };
          auto full = [&](u32 c) { dem(c, 64); };
          auto cut = [&]() { if (p > (unsigned)cap || i == P.roots[j]) ok = false; else cutOne[i] = 1; };
          switch (x.op) {
          case O_CONST: break;
          case O_VAR: if (p > (unsigned)cap) ok = false; break;
          case O_ADD: case O_MUL: case O_AND: case O_OR: case O_XOR: dem(x.a, p); dem(x.b, p); break;
          case O_NEG: case O_NOT: dem(x.a, p); break;
          case O_SHL: if (P.ins[x.b].op == O_CONST) { if (P.ins[x.b].k < p) dem(x.a, p - (unsigned)P.ins[x.b].k); } else if (cuts) cut(); else { dem(x.a, p); full(x.b); } break;
          case O_LSHR: case O_ASHR:
            if (P.ins[x.b].op == O_CONST && !(cuts && p + P.ins[x.b].k > (u64)cap)) dem(x.a, p + (unsigned)std::min<u64>(P.ins[x.b].k, 64));
            else if (cuts) cut(); else { full(x.a); full(x.b); }
            break;
          case O_EXTRACT: if (cuts && x.lo + p > (unsigned)cap) cut(); else dem(x.a, x.lo + p); break;
          case O_ZEXT: case O_SEXT: dem(x.a, p); break;
          case O_CONCAT: dem(x.b, p); if (p > P.ins[x.b].w) dem(x.a, p - P.ins[x.b].w); break;
          case O_ITE: dem(x.a, 1); dem(x.b, p); dem(x.c, p); break;
          default: if (cuts) cut(); else { full(x.a); if (x.b) full(x.b); if (x.c) full(x.c); } break;
          }
        }
      }
      if (!ok) continue;
      keep[j] = 1; kept++;
      for (size_t i = 0; i < n; i++) { if (one[i] > need[i]) need[i] = one[i]; if (cutOne[i]) cutAny[i] = 1; }
    }
    if (!kept) return SR_UNKNOWN;
    // the variables and the size of the search
    vlist.clear(); int bits = 0;
    for (size_t i = 0; i < n; i++) if (need[i] && (P.ins[i].op == O_VAR || cutAny[i])) { vlist.push_back((u32)i); bits += need[i]; }
    if (bits > maxEnum) return SR_UNKNOWN;
    std::vector<u32> active; for (size_t i = 0; i < n; i++) if (need[i]) active.push_back((u32)i);
    bool sat = false;
    const u64 total = 1ull << bits;
    if (total * active.size() > 6000000ull) return SR_UNKNOWN;      // about 15 ms of work at most
    for (u64 a = 0; a < total && !sat; a++) {
      u64 rest = a;
      for (u32 vi : vlist) { P.val[vi] = rest & maskOf(need[vi]); rest >>= need[vi]; }
      for (u32 i : active) {
        const auto& x = P.ins[i];
        if (x.op == O_VAR || cutAny[i]) continue;
        if (x.op == O_CONST) { P.val[i] = x.k & maskOf(need[i]); continue; }
        P.val[i] = evalOp(x.op, x.w, x.lo, x.k, P.val[x.a], P.val[x.b], P.val[x.c]) & maskOf(need[i]);
      }
      bool all = true;
      for (u32 j = 0; j < nr && all; j++) {
        if (!keep[j]) continue;
        const auto& r = P.ins[P.roots[j]];
        if (reduced[j]) all = ((P.val[r.a] ^ P.val[r.b]) & maskOf(std::min<int>(k, P.ins[r.a].w))) == 0;
        else all = P.val[P.roots[j]] & 1;
      }
      sat = all;
    }
    if (!sat) {
      if (getenv("UNSHROUD_MOD_DEBUG")) {
        fprintf(stderr, "modular: unsat at k=%d, kept %d of %u, bits %d%c", k, kept, nr, bits, 10);
        for (u32 j = 0; j < nr; j++) fprintf(stderr, "  constraint %u kept %d reduced %d root op %s%c", j, (int)keep[j], (int)reduced[j], opName(P.ins[P.roots[j]].op), 10);
        for (size_t i = 0; i < n; i++) if (need[i]) fprintf(stderr, "  node %zu op %s w %u need %u cut %d a %u b %u k %llx%c", i, opName(P.ins[i].op), P.ins[i].w, need[i], (int)cutAny[i], P.ins[i].a, P.ins[i].b, (unsigned long long)P.ins[i].k, 10);
      }
      return SR_UNSAT;
    }
  }
  return SR_UNKNOWN;
}

// ------------------------------------------------------------------------------------------------ the pipeline
SatResult Solver::check(const std::vector<u32>& path, const std::vector<u32>& query, const std::vector<u64>& seed,
                        std::vector<u64>* model, const SolveOptions& o, const char** stage) {
  const SatResult r = checkCore(path, query, seed, model, o, stage);
  if (r == SR_SAT && model) placeRepair(path, query, *model);
  return r;
}

void Solver::placeRepair(const std::vector<u32>& path, const std::vector<u32>& query, std::vector<u64>& m) {
  std::vector<u32> cand;
  for (u32 c : query) for (u32 v : varsOf(c)) if (v < m.size() && v < X.vars.size() && X.vars[v].place && m[v] && m[v] < 0x10000) cand.push_back(v);
  if (cand.empty()) return;
  std::sort(cand.begin(), cand.end()); cand.erase(std::unique(cand.begin(), cand.end()), cand.end());
  for (u32 v : cand) {
    const u64 old = m[v]; m[v] = X.vars[v].place;
    bool ok = true;
    for (u32 c : query) if (!(X.eval(c, m.data()) & 1)) { ok = false; break; }
    if (ok) for (u32 c : path) if (!(X.eval(c, m.data()) & 1)) { ok = false; break; }
    if (ok) placeRepairs++; else m[v] = old;
  }
}

SatResult Solver::checkCore(const std::vector<u32>& path, const std::vector<u32>& query, const std::vector<u64>& seed,
                            std::vector<u64>* model, const SolveOptions& o, const char** stage) {
  const double t0 = now();
  stats.queries++;
  const char* dummy; if (!stage) stage = &dummy;
  static const bool dbg = getenv("UNSHROUD_SOLVE_DEBUG") != nullptr;
  const std::vector<u32>* unmergedP = nullptr; bool* mergedP = nullptr;
  auto done = [&](SatResult r, const char* st) {
    if (r == SR_UNSAT && mergedP && *mergedP && unmergedP && !unmergedP->empty()) {
      std::vector<u64> m2(X.vars.size());
      const SatResult r2 = smt(*unmergedP, &m2, 20000);
      fprintf(stderr, "bounds check: unsat by %s after merging; as it was: %s%s%c", st, satName(r2), r2 == SR_SAT ? "  <<<< MISMATCH" : "", 10);
    }
    *stage = st; stats.tAll += now() - t0;
    if (dbg) fprintf(stderr, "solve: %s by %s, %.4fs, path %zu, query %s\n", satName(r), st, now() - t0, path.size(), query.empty() ? "-" : X.str(query[0], 7).c_str());
    return r;
  };
  std::vector<u32> q, p;
  if (!flattenConds(X, query, q)) { stats.trivial++; return done(SR_UNSAT, "trivial"); }
  if (q.empty()) { stats.trivial++; if (model) *model = seed; return done(SR_SAT, "trivial"); }
  if (!flattenConds(X, path, p)) { stats.trivial++; return done(SR_UNSAT, "trivial"); }
  // slicing: the path constraints which share variables with the query, transitively
  std::vector<u32> conds;
  if (o.slicing) {
    std::vector<u8> inSet(X.vars.size(), 0);
    for (u32 c : q) for (u32 v : varsOf(c)) inSet[v] = 1;
    std::vector<u8> taken(p.size(), 0);
    bool grew = true;
    while (grew) {
      grew = false;
      for (size_t i = 0; i < p.size(); i++) {
        if (taken[i]) continue;
        const auto& vs = varsOf(p[i]);
        bool hit = false; for (u32 v : vs) if (inSet[v]) { hit = true; break; }
        if (!hit) continue;
        taken[i] = 1; conds.push_back(p[i]);
        for (u32 v : vs) if (!inSet[v]) { inSet[v] = 1; grew = true; }
      }
    }
  } else conds = p;
  // a constraint which is there twice once is enough
  std::sort(conds.begin(), conds.end()); conds.erase(std::unique(conds.begin(), conds.end()), conds.end());
  for (u32 c : q) conds.push_back(c);
  // Bounds on one expression (a loop bounded by an input leaves one per iteration: 0 < n, 1 < n, 2 < n ...) are merged
  // into the strongest one each way; values ruled out which are outside them are dropped. The same set of solutions.
  static const bool boundsCheck = getenv("UNSHROUD_BOUNDS_CHECK") != nullptr;     // self-check: what is found without a model is asked again as it was
  const std::vector<u32> unmerged(boundsCheck ? conds : std::vector<u32>());
  bool merged = false;
  unmergedP = &unmerged; mergedP = &merged;
  if (o.bounds && conds.size() > 2) {
    struct B { u64 lo, hi; int n; };
    std::unordered_map<u32, B> bnd;
    auto side = [&](u32 c, u32& e, bool& lower, u64& v) -> bool {     // c is "v <= e" (lower) or "e <= v"
      const Node& x = X.N(c);
      if (x.op != O_ULT && x.op != O_ULE) return false;
      const u64 m = maskOf(x.lo);
      if (X.isC(x.a) && !X.isC(x.b)) { e = x.b; lower = true; v = X.cv(x.a); if (x.op == O_ULT) { if (v == m) return false; v++; } return true; }
      if (X.isC(x.b) && !X.isC(x.a)) { e = x.a; lower = false; v = X.cv(x.b); if (x.op == O_ULT) { if (v == 0) return false; v--; } return true; }
      return false;
    };
    for (u32 c : conds) {
      u32 e; bool lower; u64 v;
      if (!side(c, e, lower, v)) continue;
      auto it = bnd.find(e);
      if (it == bnd.end()) it = bnd.emplace(e, B{0, maskOf(X.W(e)), 0}).first;
      if (lower) it->second.lo = std::max(it->second.lo, v); else it->second.hi = std::min(it->second.hi, v);
      it->second.n++;
    }
    bool any = false;
    for (auto& kv : bnd) if (kv.second.n > 1) any = true;
    if (any) {
      std::vector<u32> out; bool empty = false;
      for (u32 c : conds) {
        u32 e; bool lower; u64 v;
        if (side(c, e, lower, v)) { if (bnd[e].n > 1) continue; out.push_back(c); continue; }       // merged below
        const Node& x = X.N(c);
        // e != k, e == k against the bounds of e
        const Node& y = x.op == O_NOT ? X.N(x.a) : x;
        if (y.op == O_EQ && X.isC(y.b) && !X.isC(y.a)) {
          auto it = bnd.find(y.a);
          if (it != bnd.end() && (X.cv(y.b) < it->second.lo || X.cv(y.b) > it->second.hi)) { if (x.op == O_NOT) continue; empty = true; break; }
        }
        out.push_back(c);
      }
      for (auto& kv : bnd) {
        const B& b = kv.second;
        if (b.n <= 1) continue;
        if (b.lo > b.hi) { empty = true; break; }
        const unsigned w = X.W(kv.first);
        if (b.lo > 0) out.push_back(X.ule(X.cst(b.lo, w), kv.first));
        if (b.hi < maskOf(w)) out.push_back(X.ule(kv.first, X.cst(b.hi, w)));
      }
      if (empty) { stats.trivial++; return done(SR_UNSAT, "bounds"); }
      std::vector<u32> flat;
      if (!flattenConds(X, out, flat)) { stats.trivial++; return done(SR_UNSAT, "bounds"); }
      std::sort(flat.begin(), flat.end()); flat.erase(std::unique(flat.begin(), flat.end()), flat.end());
      conds.swap(flat); merged = true;
      if (conds.empty()) {                                   // nothing is asked of the variables of the query
        stats.trivial++;
        if (model) { *model = seed; model->resize(X.vars.size()); for (size_t i = seed.size(); i < X.vars.size(); i++) (*model)[i] = X.vars[i].seed; }
        return done(SR_SAT, "bounds");
      }
    }
  }
  // the cache
  std::vector<u32> key(conds); std::sort(key.begin(), key.end()); key.erase(std::unique(key.begin(), key.end()), key.end());
  // a constraint and its negation, both asked for: nothing satisfies that (the same condition decided again further
  // down a path, asked the other way)
  for (u32 c : key) {
    const u32 nc = X.not_(c);
    if (nc != c && std::binary_search(key.begin(), key.end(), nc)) { stats.trivial++; stats.opposite++; return done(SR_UNSAT, "opposite"); }
  }
  // a set of constraints the SMT solver found to have no model (a core), all of it asked again
  if (o.cache && coreIn(key)) {
    static const bool coreCheck = getenv("UNSHROUD_CORE_CHECK") != nullptr;     // self-check: the whole query to a new solver
    if (coreCheck) { const SatResult r2 = smtNew(key, nullptr, 20000); fprintf(stderr, "core check: %s%s%c", satName(r2), r2 == SR_SAT ? "  <<<< MISMATCH" : "", 10); }
    stats.coreUnsat++; return done(SR_UNSAT, "core");
  }
  u64 h = 0xcbf29ce484222325ull; for (u32 c : key) h = (h ^ c) * 0x100000001b3ull;
  if (o.cache) {
    auto it = qcache.find(h);
    if (it != qcache.end() && it->second.key == key) {
      stats.cached++;
      if (it->second.r == SR_SAT && model) { *model = seed; for (auto& kv : it->second.model) (*model)[kv.first] = kv.second; }
      return done(it->second.r, "cache");
    }
  }
  auto remember = [&](SatResult r, const std::vector<u64>* m) {
    if (!o.cache || r == SR_UNKNOWN) return;
    CacheE e; e.key = key; e.r = r;
    if (m) { std::vector<u32> vs; for (u32 c : conds) for (u32 v : varsOf(c)) vs.push_back(v);
      std::sort(vs.begin(), vs.end()); vs.erase(std::unique(vs.begin(), vs.end()), vs.end());
      for (u32 v : vs) e.model.push_back({v, (*m)[v]}); }
    qcache[h] = std::move(e);
  };
  std::vector<u64> vals(seed); vals.resize(X.vars.size());
  for (size_t i = seed.size(); i < X.vars.size(); i++) vals[i] = X.vars[i].seed;
  if (o.seedCheck) {
    bool all = true;
    for (u32 c : q) if (!(X.eval(c, vals.data()) & 1)) { all = false; break; }
    if (all) { stats.seedSat++; if (model) *model = vals; remember(SR_SAT, &vals); return done(SR_SAT, "seed"); }
  }
  if (o.localSearch) {
    double t = now();
    std::vector<u64> ls(vals);
    bool ok = localSearch(conds, ls, o.lsBudget, h);
    stats.tLs += now() - t;
    if (ok) { stats.lsSat++; if (model) *model = ls; remember(SR_SAT, &ls); return done(SR_SAT, "local"); }
  }
  const std::vector<u32> conds0(conds);                // the query as it was: what a model must satisfy
  // What an overflow check says about the product it guards: z <= K / y gives y * z <= K (no wrap), K / y < z gives a
  // product above K (in its high half or its low one). When the query asks the opposite, there is no model - which the
  // bit-level solver does not find in time.
  if (o.lemmas) {
    const size_t n0 = conds.size();
    for (size_t i = 0; i < n0; i++) {
      const Node x = X.N(conds[i]);
      u32 lemma = 0;
      if (x.op == O_ULE && X.N(x.b).op == O_UDIV && !X.isC(X.N(x.b).b)) { const Node d = X.N(x.b); lemma = X.ule(X.mul(d.b, x.a), d.a); }
      else if (x.op == O_ULT && X.N(x.a).op == O_UDIV && !X.isC(X.N(x.a).b)) { const Node d = X.N(x.a); const u32 w = X.W(x.b);
        lemma = X.or_(X.ne(X.mulhu(d.b, x.b), X.cst(0, w)), X.ult(d.a, X.mul(d.b, x.b))); }
      if (!lemma) continue;
      if (X.isC(lemma)) { if (!(X.cv(lemma) & 1)) { stats.trivial++; remember(SR_UNSAT, nullptr); return done(SR_UNSAT, "lemma"); } continue; }
      const u32 neg = X.not_(lemma);
      if (std::find(conds.begin(), conds.end(), neg) != conds.end()) { stats.trivial++; remember(SR_UNSAT, nullptr); return done(SR_UNSAT, "lemma"); }
      // (the fact is not added to the query: one more multiplier costs the solver more than it tells it)
    }
  }
  u32 smtUsedMs = 0;
  std::vector<u32> raceWith;                           // the smaller query, when it is to be solved along with the exact one
  bool exactChanged = false;                           // the proved replacements changed the query: the solver gets both forms
  bool likely = false;                                 // unsatisfiable according to replacements which are only tested
  // A big query (thousands of nodes: a long path through a loop, a hash) is not rewritten: the time it takes and a second
  // solver running beside the first cost more there than a smaller form of one constraint brings.
  u64 querySize = 0; for (u32 c : conds) { querySize += X.countNodes(c); if (querySize > o.simplifyMax) break; }   // (distinct nodes of each constraint)
  if (o.simplify && querySize <= o.simplifyMax) {
    double t = now();
    if (!mba) {
      mba = new Mba(X, this); mba->o.synthSize = 5; mba->o.synthMax = 60000; mba->o.budget = 0.5; mba->o.verifyMs = 0;   // models are checked here, and no model is not concluded from it
      mbaExact = new Mba(X, this); mbaExact->o.exactOnly = true; mbaExact->o.budget = 0.5; mbaExact->o.verifyMs = 0;
    }
    // a share of the query's time for all of this, whatever the number of constraints
    const double stageEnd = t + std::min(0.4, std::max(0.03, o.timeoutMs * 0.00004));
    // 1. proved replacements only (constructor rules, linear MBA identities): what follows holds for the query itself
    bool& changed = exactChanged;
    for (u32& c : conds) {
      u32 n0 = X.countNodes(c);
      if (n0 > 4000 || n0 < 8) continue;
      if (now() >= stageEnd) break;
      mbaExact->o.budget = std::min(0.5, stageEnd - now());
      u32 r = mbaExact->simplify(c);
      if (r != c && (X.isC(r) || X.countNodes(r) * 10 <= n0 * 7)) { c = r; changed = true; }   // clearly smaller only: Bitwuzla can find another form harder
    }
    if (changed) {
      stats.simplified++;
      std::vector<u32> flat;
      if (!flattenConds(X, conds, flat)) { stats.tSimp += now() - t; remember(SR_UNSAT, nullptr); return done(SR_UNSAT, "simplify"); }
      conds = flat;
    }
    // 2. tested replacements too: a smaller query to find a model with (checked on the query as it was), or to learn
    //    that there is probably none - which is not a proof: a condition true for one input in 2^64 tests as a constant
    std::vector<u32> tc(conds); bool tchanged = false;
    const double stageEnd2 = now() + std::min(0.4, std::max(0.03, o.timeoutMs * 0.00004));
    if (!mba->o.legacy) for (u32& c : tc) {
      u32 n0 = X.countNodes(c);
      if (n0 > 4000 || n0 < 8) continue;
      if (now() >= stageEnd2) break;
      mba->o.budget = std::min(0.5, stageEnd2 - now());
      u32 r = mba->simplify(c);
      if (r != c && (X.isC(r) || X.countNodes(r) * 10 <= n0 * 7)) { c = r; tchanged = true; }
    }
    stats.tSimp += now() - t;
    if (dbg) for (size_t i = 0; i < conds.size(); i++) fprintf(stderr, "  cond %zu: exact %u nodes: %s\n         tested %u nodes: %s\n", i, X.countNodes(conds[i]), X.str(conds[i], 9).c_str(), i < tc.size() ? X.countNodes(tc[i]) : 0, i < tc.size() ? X.str(tc[i], 9).c_str() : "");
    if (tchanged) {
      std::vector<u32> tflat; SatResult tr = SR_UNKNOWN; std::vector<u64> tm(vals);
      if (!flattenConds(X, tc, tflat)) tr = SR_UNSAT;
      else {
        if (o.localSearch) { std::vector<u64> ls(vals); if (localSearch(tflat, ls, o.lsBudget, h ^ 0x51)) { tm = ls; tr = SR_SAT; } }
        if (tr == SR_UNKNOWN && o.modular) { double t2 = now(); if (modular(tflat, o.modBits, o.modMaxEnum) == SR_UNSAT) tr = SR_UNSAT; stats.tMod += now() - t2; }
        // a small share of the time for the smaller query: a model found there is checked, "no model" there proves nothing
        if (tr == SR_UNKNOWN && o.smt) raceWith = tflat;               // the solver takes it along with the query itself (below)
      }
      if (tr == SR_SAT) {
        bool ok = true;
        for (u32 c : conds0) if (!(X.eval(c, tm.data()) & 1)) { ok = false; break; }
        if (ok) { stats.smtSat++; if (model) *model = tm; remember(SR_SAT, &tm); return done(SR_SAT, "simplified"); }
        stats.badModels++;                              // a replacement was wrong for these values
      }
      likely = tr == SR_UNSAT;
    }
  }
  if (o.modular) {
    double t = now();
    SatResult r = modular(conds, o.modBits, o.modMaxEnum);
    stats.tMod += now() - t;
    if (r == SR_UNSAT) { stats.modUnsat++; remember(r, nullptr); return done(r, "modular"); }
  }
  if (o.smt) {
    double t = now();
    std::vector<u64> m(vals);
    // the limit is the query's: what the earlier stages took is not available any more
    const u32 spent = (u32)((now() - t0) * 1000);
    const u32 left = o.timeoutMs > spent + 50 ? o.timeoutMs - spent : 50;
    (void)smtUsedMs;
    SatResult r; int from = 0;
    const std::vector<u32>* sides[2] = {nullptr, nullptr}; bool sideSound[2] = {false, false}; int ns = 0;
    if (o.race && exactChanged) { sides[ns] = &conds0; sideSound[ns] = true; ns++; }           // the query as it was
    if (o.race && !raceWith.empty()) { sides[ns] = &raceWith; sideSound[ns] = false; ns++; }   // its smaller form (tested)
    const u32 limit = likely && o.confirmMs ? std::max<u32>(50, std::min<u32>(left, o.confirmMs)) : left;
    if (ns) { bool lk = false; r = smtRace(conds, sides, sideSound, conds0, vals, &m, limit, o.confirmMs, lk, from); likely = likely || lk; stats.races++; }
    else {
      r = smt(conds, &m, limit);
      if (r == SR_UNSAT && !exactChanged && !lastCore.empty()) coreAdd(lastCore);     // (conds are the query's own constraints then)
    }
    const bool fromTested = from > 0 && !sideSound[from - 1];
    stats.tSmt += now() - t;
    if (r == SR_SAT) { stats.smtSat++; if (model) *model = m; remember(r, &m); return done(r, fromTested ? "simplified" : "smt"); }
    if (r == SR_UNSAT) { stats.smtUnsat++; remember(r, nullptr); return done(r, "smt"); }
  }
  if (likely) { stats.likelyUnsat++; return done(SR_UNKNOWN, "likely-unsat"); }
  stats.unknown++;
  return done(SR_UNKNOWN, "none");
}

}  // namespace unshroud
