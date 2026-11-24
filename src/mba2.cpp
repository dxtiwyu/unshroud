// unshroud - simplification by signatures. Bottom-up over the DAG; each node, rebuilt from its simplified operands, is replaced by
// the smallest thing known to have its values on the test assignments (sig.hpp):
//   a constant, a node met before, the table's expression over the inputs, an operation on two of its own descendants
//   (what an MBA identity over big operands collapses to), the exact linear / boolean form of its MBA region (mba.cpp),
//   a split A op B found in the table.
// Comparisons are free bits in the signatures: nothing here decides what a comparison computes.
#include "mba.hpp"
#include "sig.hpp"
#include "solver.hpp"
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <intrin.h>

namespace unshroud {

static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }
static inline bool isCompare(u8 op) { return op == O_EQ || op == O_ULT || op == O_ULE || op == O_SLT || op == O_SLE; }
static inline bool mbaOp(u8 op) { return op == O_ADD || op == O_MUL || op == O_NEG || op == O_AND || op == O_OR || op == O_XOR || op == O_NOT; }

Mba::~Mba() { delete sg; delete sg2; }

void Mba::record(u32 r) {
  const u64 h = sg->hash(r);
  auto it = bySig.find(h);
  if (it == bySig.end()) { bySig.emplace(h, r); return; }
  if (it->second == r) return;
  if (!sg->same(it->second, r)) return;                       // another function with the same hash: the first one stays
  if (X.N(r).size < X.N(it->second).size) it->second = r;
}

u32 Mba::accept(u32 r, u32 cand, u32& rNodes) {
  if (!cand || cand == r || X.W(cand) != X.W(r)) return 0;
  if (!sg->same(cand, r)) return 0;
  if (!sg2->full() && !sg2->same(cand, r)) { st.rejected++; return 0; }
  if (!(X.isC(cand) || X.N(cand).op == O_VAR)) {
    if (!rNodes) rNodes = X.countNodes(r);
    if (X.countNodes(cand) >= rNodes) return 0;
  }
  // The same values on every test is not the same function: two expressions can differ for one input in 2^50 (a carry
  // which runs through a constant's bits). What is not proved by its polynomial goes to the solver, which finds such an
  // input quickly when there is one (within a number of checks per call).
  acceptProved = provePoly(r, cand, nullptr);
  if (!acceptProved && S && o.verifyMs && narrowBudget) {
    narrowBudget--;
    const int d = S->decideEq(r, cand, nullptr, 0, o.narrowMs);
    if (d == 2) { st.refuted++; return 0; }
    if (d == 1) acceptProved = true;
  }
  return cand;
}

u32 Mba::simplify(u32 root) {
  if (o.legacy) { lastExact = false; return simplifyOld(root); }
  const double t0 = now();
  st.calls++;
  if (!sg) { sg = new Sigs(X, 0); sg2 = new Sigs(X, 1); }
  const double deadline = t0 + o.budget;
  sliceBudget = 20000; proofBudget = 16; constBudget = 24; narrowBudget = 64; healBudget = 200;
  u32 cur = root;
  for (int attempt = 0; attempt < 2; attempt++) {
    cur = root; bool ex = true;
    for (int round = 0; round < 4; round++) {
      u32 r = pass(cur, deadline);
      if (inexact.count(cur)) ex = false;
      if (r == cur) break;
      cur = r;
    }
    // the root once more, with the expensive search allowed
    if (X.sym(cur) && !sg->full() && now() < deadline && !conservative) {
      bool e2 = true; u32 r = improve(cur, true, deadline, e2);
      if (r != cur) { memo[cur] = r; if (!e2) { inexact.insert(cur); ex = false; } cur = r; }
    }
    lastExact = ex;
    if (cur == root || ex) break;
    // the whole of it a linear MBA of its atoms, like the result: the corner values prove it
    if (!conservative && (proveLinear(root, cur, nullptr) || provePoly(root, cur, nullptr))) { lastExact = true; st.verified++; break; }
    bool ok = finalCheck(root, cur);
    if (ok && S && o.verifyMs && !conservative && (sg->narrow(root) || o.verifyAll)) {
      // tests cannot see what happens for one input in 2^40 (a carry into the bit which is read): the solver may
      // (a counterexample, when there is one, comes quickly; a big result is rarely proved in any time worth spending here)
      SolveOptions so; so.timeoutMs = X.N(root).size <= 200 ? o.verifyMs : std::max<u32>(20, o.verifyMs / 2); so.simplify = false; so.modular = false; so.cache = false; so.lsBudget = 400;
      std::vector<u64> seedv(X.vars.size()), model;
      for (size_t i = 0; i < seedv.size(); i++) seedv[i] = X.vars[i].seed;
      const double tv = now();
      SatResult r = S->check({}, {X.ne(root, cur)}, seedv, &model, so);
      st.tCheck += now() - tv;
      if (r == SR_UNSAT) { st.verified++; lastExact = true; }
      else if (r == SR_SAT) { st.refuted++; st.refutedFinal++; ok = false; }
      else st.unverified++;
    }
    if (ok) break;
    // a replacement was wrong somewhere: everything learned is dropped, and only the region methods are used from now on
    st.rejected++;
    if (getenv("UNSHROUD_MBA_DEBUG")) fprintf(stderr, "mba: the result failed the final check, conservative from now on\n");
    memo.clear(); improved.clear(); bySig.clear(); noSplit.clear(); inexact.clear();
    if (conservative) { cur = root; lastExact = true; break; }
    conservative = true;
  }
  conservative = false;
  memo[root] = cur;
  if (!lastExact) inexact.insert(root);
  st.t += now() - t0;
  return cur;
}

// Can the expression take a value for very few inputs only? Where a bit above the lowest is read out of a sum or a product
// (a carry decides it), where something is the same on every test without being a constant by its structure.
bool Mba::narrowProne(u32 root) {
  X.newGen();
  std::vector<u32> st{root}; X.stamp[root] = X.gen;
  size_t seen = 0;
  while (!st.empty()) {
    const u32 id = st.back(); st.pop_back();
    if (++seen > 50000) return true;
    const Node& x = X.N(id);
    if (x.op == O_EXTRACT && x.lo > 0) { const u8 a = X.N(x.a).op; if (a == O_ADD || a == O_MUL || a == O_NEG || a == O_UDIV || a == O_UREM || a == O_SDIV || a == O_SREM || a == O_MULHU || a == O_MULHS) return true; }
    if (x.op == O_LSHR || x.op == O_ASHR || x.op == O_UDIV || x.op == O_UREM || x.op == O_SDIV || x.op == O_SREM || x.op == O_MULHU || x.op == O_MULHS || x.op == O_CLZ || x.op == O_CTZ) return true;
    if (sg->isSuspect(id)) return true;
    for (u32 c : {x.a, x.b, x.c}) if (c && X.stamp[c] != X.gen) { X.stamp[c] = X.gen; st.push_back(c); }
  }
  return false;
}

static u64 checkVar(void* ud, u32 var, int k) {
  Ctx& X = *(Ctx*)ud;
  if (k < 96) return sigTestValue(var + 1000, k + 7, 0);                        // uniform, not the signature's
  if (k < 192) return sigTestValue(var + 1000, k, 1);                           // sparse, small, dense
  const u64 seed = X.vars[var].seed;                                            // around the inputs of the path
  u64 r = sigTestValue(var + 2000, k, 0);
  return (r & 3) == 0 ? seed : seed ^ (1ull << ((r >> 8) & 63)) ^ ((r & 4) ? 1ull << ((r >> 16) & 63) : 0);
}

bool Mba::finalCheck(u32 a, u32 b) {
  const double t = now();
  const int n = 256;
  std::vector<u64> out(2 * n);
  u32 roots[2] = {a, b};
  evalBatch(X, roots, 2, n, checkVar, &X, out.data());
  st.tCheck += now() - t;
  return memcmp(out.data(), out.data() + n, sizeof(u64) * n) == 0;
}

// Bits lo .. lo+w-1 of e, with the extraction pushed down through whatever lets it through (the constructors do that for
// small operands only: here the copies are wanted, a flag taken out of a packed register is what is left of them).
u32 Mba::slice(u32 e, unsigned lo, unsigned w) {
  const unsigned we = X.W(e);
  if (lo == 0 && w == we) return e;
  const Node x = X.N(e);
  if (x.op == O_CONST || x.op == O_VAR || sliceBudget == 0) return X.extract(e, lo, w);
  const u64 key = ((u64)e << 16) | (lo << 8) | w;
  auto it = sliced.find(key);
  if (it != sliced.end()) return it->second;
  sliceBudget--;
  u32 r = 0;
  switch (x.op) {
  case O_AND: r = X.and_(slice(x.a, lo, w), slice(x.b, lo, w)); break;
  case O_OR: r = X.or_(slice(x.a, lo, w), slice(x.b, lo, w)); break;
  case O_XOR: r = X.xor_(slice(x.a, lo, w), slice(x.b, lo, w)); break;
  case O_NOT: r = X.not_(slice(x.a, lo, w)); break;
  case O_ITE: r = X.ite(x.a, slice(x.b, lo, w), slice(x.c, lo, w)); break;
  case O_ADD: if (lo == 0) r = X.add(slice(x.a, 0, w), slice(x.b, 0, w)); break;
  case O_NEG: if (lo == 0) r = X.neg(slice(x.a, 0, w)); break;
  case O_MUL:
    if (X.isC(x.b) && (X.cv(x.b) & (X.cv(x.b) - 1)) == 0 && X.cv(x.b)) {
      unsigned long sh; _BitScanForward64(&sh, X.cv(x.b));
      if (lo >= sh) r = slice(x.a, lo - sh, w);
      else if (lo + w <= sh) r = X.cst(0, w);
      else r = X.concat(slice(x.a, 0, lo + w - sh), X.cst(0, sh - lo));
    } else if (lo == 0) r = X.mul(slice(x.a, 0, w), slice(x.b, 0, w));
    break;
  case O_EXTRACT: r = slice(x.a, x.lo + lo, w); break;
  case O_ZEXT: {
    const unsigned wx = x.lo;
    if (lo + w <= wx) r = slice(x.a, lo, w);
    else if (lo >= wx) r = X.cst(0, w);
    else r = X.zext(slice(x.a, lo, wx - lo), w);
    break;
  }
  case O_SEXT: {
    const unsigned wx = x.lo;
    if (lo + w <= wx) r = slice(x.a, lo, w);
    break;
  }
  case O_CONCAT: {
    const unsigned wl = x.lo;
    if (lo + w <= wl) r = slice(x.b, lo, w);
    else if (lo >= wl) r = slice(x.a, lo - wl, w);
    else r = X.concat(slice(x.a, 0, lo + w - wl), slice(x.b, lo, wl - lo));
    break;
  }
  default: break;
  }
  if (!r) r = X.extract(e, lo, w);
  sliced[key] = r;
  return r;
}

u32 Mba::pass(u32 root, double deadline) {
  std::vector<std::pair<u32, int>> stk{{root, 0}};
  while (!stk.empty()) {
    auto& tp = stk.back(); const u32 id = tp.first;
    if (memo.count(id)) { stk.pop_back(); continue; }
    const Node y = X.N(id);
    const u32 kids[3] = {y.a, y.b, y.c};
    // The low bits of something: the extraction goes down through what was written first (exact), and what comes
    // out is simplified at its own width - a sum which is a linear MBA modulo 2^w only, junk above the bits read.
    // (Simplifying the wide operand first can end in a form which is only tested, and that is what the bits would
    // then be taken from.)
    if (y.op == O_EXTRACT && o.slices && y.lo == 0 && tp.second == 0) {
      const u32 s = slice(y.a, 0, y.w);
      if (s != id && X.N(s).op != O_EXTRACT) { tp.second = 4; sliceOf[id] = s; if (!memo.count(s)) stk.push_back({s, 0}); continue; }
    }
    if (tp.second == 4) {
      const u32 s = sliceOf[id]; stk.pop_back();
      memo[id] = memo.count(s) ? memo[s] : s;
      if (inexact.count(s)) inexact.insert(id);
      continue;
    }
    if (tp.second < 3) { u32 c = kids[tp.second++]; if (c && !memo.count(c)) stk.push_back({c, 0}); continue; }
    stk.pop_back();
    u32 r = id; bool ex = true;
    if (y.op != O_CONST && y.op != O_VAR) {
      for (u32 c : kids) if (c && inexact.count(c)) ex = false;
      u32 a = y.a ? memo[y.a] : 0, b = y.b ? memo[y.b] : 0, c = y.c ? memo[y.c] : 0;
      if (y.op == O_EXTRACT && o.slices) r = slice(a, y.lo, y.w);
      else if (a != y.a || b != y.b || c != y.c) r = X.make(y.op, y.w, y.lo, a, b, c, y.k);
      if (X.sym(r) && !sg->full() && now() < deadline) { bool e2 = true; r = improve(r, false, deadline, e2); if (!e2) ex = false; }
    }
    // what the operands became was not all proved: the node itself against its final form may be (the same polynomial)
    if (!ex && r != id && healBudget && !conservative && X.N(id).size <= 400) { healBudget--; if (provePoly(id, r, nullptr)) ex = true; }
    if (r != id && getenv("UNSHROUD_MBA_TRACE")) fprintf(stderr, "mba: %s%s   =>  %s (%s)%s", X.str(id, 5).c_str(), "\n", X.str(r, 5).c_str(), ex ? "exact" : "tested", "\n"), fprintf(stderr, "      by %s\n", how);
    memo[id] = r;
    if (!ex) inexact.insert(id);
  }
  return memo[root];
}

u32 Mba::improve(u32 r, bool isRoot, double deadline, bool& exact) {
  const u32 r0 = r;
  exact = true;
  if (!isRoot) { auto it = improved.find(r); if (it != improved.end()) { exact = !(it->second & 1); return it->second >> 1 ? (u32)(it->second >> 1) : r; } }
  for (int round = 0; round < 6; round++) {
    bool e = true;
    u32 b = improveOnce(r, isRoot, deadline, e);
    if (!b || b == r) break;
    r = b;
    if (!e) exact = false;
    if (!X.sym(r)) break;
  }
  improved[r0] = ((u64)r << 1) | (exact ? 0 : 1);
  if (!improved.count(r)) improved[r] = (u64)r << 1;
  if (X.sym(r)) record(r);
  return r;
}

u32 Mba::improveOnce(u32 r, bool isRoot, double deadline, bool& exact) {
  const Node x = X.N(r);
  exact = true;
  if (x.op == O_VAR || x.op == O_CONST || isCompare(x.op)) return 0;
  const unsigned w = x.w;
  st.nodes++;
  if (conservative) {                                          // proved replacements only
    if (X.unknownBits(r) == 0) return X.cst(X.known(r).ones, w);
    if (!mbaOp(x.op) || now() >= deadline) return 0;
    u32 c = top(r, false);
    return c && c != r && X.W(c) == w && topExact ? c : 0;
  }
  const bool tested = !o.exactOnly;                            // replacements which are not proved are allowed
  if (X.unknownBits(r) == 0) { st.constant++; st.proved++; return X.cst(X.known(r).ones, w); }   // every bit is fixed by the structure
  if (w == 1 && x.size > 3 && now() < deadline) {
    // before anything decides that it is a constant: the comparison it computes, proved
    const double t = now();
    pairProved = false;
    u32 c = cmpSearch(r);
    st.tPair += now() - t;
    if (c && pairProved) { exact = true; st.proved++; return c; }
  }
  // the same value on every test, below operations which cannot hide a rare case: a constant
  u64 cv;
  if (!sg->narrow(r) && sg->isConst(r, cv)) {
    u64 cv2;
    if (sg2->isConst(r, cv2) && cv2 == cv) {
      const u32 c = X.cst(cv, w);
      exact = provePoly(r, c, nullptr);
      bool refuted = false;
      if (!exact && S && o.verifyMs && narrowBudget) { narrowBudget--; const int d = S->decideEq(r, c, nullptr, 0, o.narrowMs); if (d == 1) exact = true; else if (d == 2) { refuted = true; st.refuted++; } }
      if (!refuted && (exact || tested)) { how = "constant"; st.constant++; if (exact) st.proved++; else st.tested++; return c; }
      exact = true;
    }
  }
  // the same value on every test: a constant if that is proved (a condition which holds for one input in 2^64 looks the same)
  if (sg->suspect(r, cv) && now() < deadline) {
    u64 cv2;
    if (sg2->suspect(r, cv2) && cv2 == cv) {
      if (mbaOp(x.op)) { u32 c = top(r, false); if (c && X.isC(c) && topExact && X.cv(c) == cv) { st.constant++; return c; } }
      if (S && constBudget) {
        constBudget--; st.cmpTried++;
        if (S->proveLocal(r, X.cst(cv, w), nullptr, 0, o.proveLocalMs)) { st.cmpProved++; st.constant++; st.proved++; return X.cst(cv, w); }
      }
    }
  }
  u32 rNodes = 0;
  // a smaller node with the same values is known
  if (tested) {
    auto it = bySig.find(sg->hash(r));
    if (it != bySig.end() && it->second != r && X.N(it->second).size < x.size) { if (u32 c = accept(r, it->second, rNodes)) { how = "known"; st.known++; exact = acceptProved; if (exact) st.proved++; else st.tested++; return c; } }
  }
  if (x.size <= 3) return 0;                                   // one operation on leaves
  const u64* s = sg->of(r);
  // the table: the smallest expression over the inputs with these values
  const bool tableWidth = w == 64 || w == 32 || w == 16 || w == 8;
  u32 leaves[ORA_LEAVES] = {0, 0, 0, 0};
  if (tableWidth) {
    for (u32 i = 0; i < ORA_LEAVES && i < X.vars.size(); i++) if (X.vars[i].w >= w) leaves[i] = X.resize(X.varNode(i), w);
    if (u32 c = accept(r, Oracle::get(w).lookup(X, s, leaves), rNodes)) {
      exact = acceptProved || proveLinear(r, c, nullptr);
      if (exact || tested) { how = "table"; st.table++; if (exact) st.proved++; else st.tested++; return c; }
    }
  }
  // an operation on two descendants
  {
    const double t = now();
    bool e = false;
    pairProved = false;
    u32 c = pairSearch(r, e);
    if (!pairProved) c = accept(r, c, rNodes);                   // a proved comparison has free bits as its signature: nothing to compare
    else if (c && X.countNodes(c) >= X.countNodes(r)) c = 0;
    st.tPair += now() - t;
    if (c) { how = pairProved ? "compare" : "pair"; if (!pairProved && acceptProved) e = true; st.pair++; if (e) st.proved++; else st.tested++; exact = e; return c; }
  }
  // the MBA region: exact linear / boolean forms
  if (mbaOp(x.op) && now() < deadline) {
    const double t = now();
    u32 c = top(r, false);
    st.tTop += now() - t;
    if (c && c != r && X.W(c) == w) {
      if (!sg->same(c, r)) { if (getenv("UNSHROUD_MBA_DEBUG")) fprintf(stderr, "mba: region result differs on the tests: %s -> %s\n", X.str(r, 6).c_str(), X.str(c, 6).c_str()); }
      else { how = "region"; exact = topExact || provePoly(r, c, nullptr); if (exact || tested) return c; exact = true; }
    }
  }
  // a split in the table, for what is still big
  if (o.split && tableWidth && now() < deadline) {
    if (!rNodes) rNodes = X.countNodes(r);
    if (rNodes > 7 && (isRoot || rNodes <= (u32)o.splitCone)) {
      const u64 h = sg->hash(r);
      if (!noSplit.count(h)) {
        const double t = now();
        u32 c = accept(r, Oracle::get(w).split(X, s, leaves), rNodes);
        st.tSplit += now() - t;
        if (c) {
          exact = acceptProved || proveLinear(r, c, nullptr);
          if (exact || tested) { how = "split"; st.splits++; if (exact) st.proved++; else st.tested++; return c; }
        }
        noSplit[h] = 1;
      }
    }
  }
  return 0;
}

// A condition computed without a comparison (the top bit of r | -r, of a borrow chain...): the comparison of two descendants
// it is. Tests cannot tell "never" from "almost never": taken only with a proof (the solver, on free operands). 0 if none.
u32 Mba::cmpSearch(u32 r) {
  const unsigned w = X.W(r);
  if (w != 1 || !S || !o.compare) return 0;
  const u64* s = sg->of(r);
  auto all = [&](auto f) { for (int k = 0; k < SIG_K; k++) if (!f(k)) return false; return true; };
  bool exact = false;
  // a condition computed without a comparison (the top bit of r | -r, of a borrow chain...): a comparison of descendants.
  // Tests cannot tell "never" from "almost never": these are taken only with a proof (the solver, on free operands).
  {
    std::vector<u32> E;
    X.newGen();
    std::vector<u32> q{r}; X.stamp[r] = X.gen;
    for (size_t head = 0; head < q.size() && E.size() < 20 && head < 400; head++) {
      const Node& x = X.N(q[head]);
      for (u32 c : {x.a, x.b, x.c}) {
        if (!c || X.stamp[c] == X.gen) continue;
        X.stamp[c] = X.gen; q.push_back(c);
        if (X.W(c) >= 8 && !X.isC(c)) E.push_back(c);
      }
    }
    const int ne = (int)E.size();
    std::vector<const u64*> ev(ne);
    for (int i = 0; i < ne; i++) ev[i] = sg->of(E[i]);
    auto tryCmp = [&](u32 cand, const u32* at, int na, int kind) -> u32 {
      if (cand == r || X.isC(cand)) return 0;
      if (!freed(r, at, na, kind, 0)) { st.notFree++; return 0; }
      if (proofBudget == 0) return 0;
      st.cmpTried++; proofBudget--;
      const bool pv = S->proveLocal(r, cand, at, na, o.proveLocalMs);
      if (getenv("UNSHROUD_MBA_DEBUG")) fprintf(stderr, "mba: comparison %s: %s%s  <=  %s%s", pv ? "proved" : "not proved", X.str(cand, 6).c_str(), "\n", X.str(r, 9).c_str(), "\n");
      if (!pv) return 0;
      st.cmpProved++;
      return cand;
    };
    for (int i = 0; i < ne; i++) {
      const u64* d = ev[i]; const unsigned wd = X.W(E[i]);
      const u32 at[2] = {E[i], 0};
      const u32 zero = X.cst(0, wd);
      if (all([&](int k) { return (u64)(d[k] == 0) == s[k]; })) if (u32 c = tryCmp(X.eq(E[i], zero), at, 1, 40)) { pairProved = true; exact = true; return c; }
      if (all([&](int k) { return (u64)(d[k] != 0) == s[k]; })) if (u32 c = tryCmp(X.ne(E[i], zero), at, 1, 41)) { pairProved = true; exact = true; return c; }
    }
    // against a constant of the cone (or its opposite, its neighbours)
    std::vector<u64> K;
    for (u32 id : q) if (X.isC(id) && X.W(id) >= 8) { const u64 k = X.cv(id); for (u64 v : {k, 0 - k, k + 1, k - 1, 1 - k, ~k}) if (K.size() < 48 && std::find(K.begin(), K.end(), v) == K.end()) K.push_back(v); }
    for (int i = 0; i < ne; i++) {
      const u64* d = ev[i]; const unsigned wd = X.W(E[i]); const u64 md = maskOf(wd);
      const u32 at[2] = {E[i], 0};
      for (u64 k0 : K) {
        const u64 c = k0 & md;
        for (int kind = 0; kind < 5; kind++) {
          auto f = [&](int k) -> u64 { switch (kind) { case 0: return d[k] < c; case 1: return c < d[k]; case 2: return sx(d[k], wd) < sx(c, wd); case 3: return sx(c, wd) < sx(d[k], wd); default: return d[k] == c; } };
          const bool pos = f(5) == s[5] && f(6) == s[6] && all([&](int k) { return f(k) == s[k]; });
          const bool neg = !pos && f(5) != s[5] && f(6) != s[6] && all([&](int k) { return f(k) != s[k]; });
          if (!pos && !neg) continue;
          if (!freed(r, at, 1, (pos ? 60 : 70) + kind, c)) { st.notFree++; continue; }
          const u32 C = X.cst(c, wd);
          u32 cand = kind == 0 ? X.ult(E[i], C) : kind == 1 ? X.ult(C, E[i]) : kind == 2 ? X.slt(E[i], C) : kind == 3 ? X.slt(C, E[i]) : X.eq(E[i], C);
          if (neg) cand = X.not_(cand);
          if (cand == r || X.isC(cand) || proofBudget == 0) continue;
          st.cmpTried++; proofBudget--;
          if (S->proveLocal(r, cand, at, 1, o.proveLocalMs)) { st.cmpProved++; pairProved = true; return cand; }
        }
      }
    }
    for (int i = 0; i < ne; i++) for (int j = 0; j < ne; j++) {
      if (i == j || X.W(E[i]) != X.W(E[j])) continue;
      const u64* a = ev[i]; const u64* b = ev[j]; const unsigned wd = X.W(E[i]);
      const u32 at[2] = {E[i], E[j]};
      for (int kind = 0; kind < 4; kind++) {
        auto f = [&](int k) -> u64 { switch (kind) { case 0: return a[k] < b[k]; case 1: return a[k] <= b[k]; case 2: return sx(a[k], wd) < sx(b[k], wd); default: return sx(a[k], wd) <= sx(b[k], wd); } };
        if (f(5) != s[5] || f(6) != s[6] || !all([&](int k) { return f(k) == s[k]; })) continue;
        const u32 cand = kind == 0 ? X.ult(E[i], E[j]) : kind == 1 ? X.ule(E[i], E[j]) : kind == 2 ? X.slt(E[i], E[j]) : X.sle(E[i], E[j]);
        if (u32 c = tryCmp(cand, at, 2, 50 + kind)) { pairProved = true; exact = true; return c; }
      }
    }
  }
  (void)exact;
  return 0;
}

// r as one operation on descendants (plus a constant): the cheapest match on every test, built; 0 if none
u32 Mba::pairSearch(u32 r, bool& exact) {
  const unsigned w = X.W(r); const u64 m = maskOf(w);
  const u64* s = sg->of(r);
  std::vector<u32> D;
  {
    X.newGen();
    std::vector<u32> q{r}; X.stamp[r] = X.gen;
    for (size_t head = 0; head < q.size() && D.size() < (size_t)o.pairMax && head < 600; head++) {
      const Node& x = X.N(q[head]);
      for (u32 c : {x.a, x.b, x.c}) {
        if (!c || X.stamp[c] == X.gen) continue;
        X.stamp[c] = X.gen; q.push_back(c);
        if (X.W(c) == w && !X.isC(c)) D.push_back(c);
      }
    }
  }
  const int n = (int)D.size();
  if (!n) return 0;
  std::vector<const u64*> v(n); std::vector<u64> sz(n);
  for (int i = 0; i < n; i++) { v[i] = sg->of(D[i]); sz[i] = X.N(D[i]).size; }
  // kinds: 0 ~d, 1 -d, 2 d+c, 3 d^c, 4 d*c, 5 d&c, 6 d|c; 10.. binary: op (0 add, 1 a-b, 2 b-a, 3 mul, 4 and, 5 or, 6 xor) * 4 + variant (0 plain, 1 +c, 2 c-, 3 ^c)
  struct Match { u64 cost; int kind, i, j; u64 c; };
  std::vector<Match> found;
  u64 worst = ~0ull;                                          // of the matches kept
  auto offer = [&](u64 cost, int kind, int i, int j, u64 c) {
    cost = cost * 256 + (u64)(255 - std::min(255, i + j));
    if (found.size() >= 8 && cost >= worst) return;
    found.push_back({cost, kind, i, j, c});
    if (found.size() > 8) { std::sort(found.begin(), found.end(), [](const Match& p, const Match& q) { return p.cost < q.cost; }); found.resize(8); worst = found.back().cost; }
  };
  auto all = [&](auto f) { for (int k = 0; k < SIG_K; k++) if (!f(k)) return false; return true; };
  for (int i = 0; i < n; i++) {
    const u64* d = v[i];
    if (((~d[5]) & m) == s[5] && all([&](int k) { return ((~d[k]) & m) == s[k]; })) offer(sz[i] + 1, 0, i, 0, 0);
    if (((0 - d[5]) & m) == s[5] && all([&](int k) { return ((0 - d[k]) & m) == s[k]; })) offer(sz[i] + 1, 1, i, 0, 0);
    { const u64 c = (s[5] - d[5]) & m; if (((d[6] + c) & m) == s[6] && all([&](int k) { return ((d[k] + c) & m) == s[k]; })) offer(sz[i] + 2, 2, i, 0, c); }
    { const u64 c = s[5] ^ d[5]; if ((d[6] ^ c) == s[6] && all([&](int k) { return (d[k] ^ c) == s[k]; })) offer(sz[i] + 2, 3, i, 0, c); }
    for (int k0 = 2; k0 < 8; k0++) if (d[k0] & 1) {
      u64 inv = d[k0]; for (int t = 0; t < 6; t++) inv *= 2 - d[k0] * inv;
      const u64 c = (s[k0] * inv) & m;
      if (c > 1 && all([&](int k) { return ((d[k] * c) & m) == s[k]; })) offer(sz[i] + 2, 4, i, 0, c);
      break;
    }
    if (all([&](int k) { return (s[k] & ~d[k]) == 0; })) {
      u64 drop = 0; for (int k = 0; k < SIG_K; k++) drop |= d[k] & ~s[k];
      const u64 c = ~drop & m;
      if (c != m && all([&](int k) { return (d[k] & c) == s[k]; })) offer(sz[i] + 2, 5, i, 0, c);
    }
    if (all([&](int k) { return (d[k] & ~s[k]) == 0; })) {
      u64 c = 0; for (int k = 0; k < SIG_K; k++) c |= s[k] & ~d[k];
      if (c && all([&](int k) { return (d[k] | c) == s[k]; })) offer(sz[i] + 2, 6, i, 0, c);
    }
  }
  for (int i = 0; i < n; i++) {
    const u64* a = v[i];
    for (int j = i + 1; j < n; j++) {
      const u64* b = v[j];
      const u64 base = sz[i] + sz[j] + 1;
      if (found.size() >= 8 && base * 256 >= worst) continue;
      for (int op = 0; op < 7; op++) {
        auto f = [&](int k) -> u64 {
          switch (op) { case 0: return (a[k] + b[k]) & m; case 1: return (a[k] - b[k]) & m; case 2: return (b[k] - a[k]) & m; case 3: return (a[k] * b[k]) & m;
                        case 4: return a[k] & b[k]; case 5: return a[k] | b[k]; default: return a[k] ^ b[k]; }
        };
        const u64 f2 = f(5), f3 = f(6);
        if (f2 == s[5] && f3 == s[6] && all([&](int k) { return f(k) == s[k]; })) { offer(base, 10 + op * 4, i, j, 0); continue; }
        if (op == 1 || op == 2) { if (op == 2) continue; }                       // a-b+c and c-(a-b) cover b-a
        { const u64 c = (s[5] - f2) & m; if (((f3 + c) & m) == s[6] && all([&](int k) { return ((f(k) + c) & m) == s[k]; })) offer(base + 1, 10 + op * 4 + 1, i, j, c); }
        { const u64 c = (s[5] + f2) & m; if (((c - f3) & m) == s[6] && all([&](int k) { return ((c - f(k)) & m) == s[k]; })) offer(base + 1, 10 + op * 4 + 2, i, j, c); }
        if (op >= 3) { const u64 c = s[5] ^ f2; if ((f3 ^ c) == s[6] && all([&](int k) { return (f(k) ^ c) == s[k]; })) offer(base + 1, 10 + op * 4 + 3, i, j, c); }
      }
    }
  }
  std::sort(found.begin(), found.end(), [](const Match& p, const Match& q) { return p.cost < q.cost; });
  for (const Match& best : found) {
    // an identity over the operands as free values, not only over the values they take here
    const u32 at[2] = {D[best.i], best.kind >= 10 ? D[best.j] : 0};
    if (!freed(r, at, best.kind >= 10 ? 2 : 1, best.kind, best.c)) { st.notFree++; continue; }
    const u32 a = D[best.i], C = X.cst(best.c, w);
    u32 e;
    if (best.kind < 10) {
      switch (best.kind) { case 0: e = X.not_(a); break; case 1: e = X.neg(a); break; case 2: e = X.add(a, C); break; case 3: e = X.xor_(a, C); break;
                           case 4: e = X.mul(a, C); break; case 5: e = X.and_(a, C); break; default: e = X.or_(a, C); break; }
    } else {
      const u32 b = D[best.j]; const int op = (best.kind - 10) / 4, var = (best.kind - 10) % 4;
      switch (op) { case 0: e = X.add(a, b); break; case 1: e = X.sub(a, b); break; case 2: e = X.sub(b, a); break; case 3: e = X.mul(a, b); break;
                    case 4: e = X.and_(a, b); break; case 5: e = X.or_(a, b); break; default: e = X.xor_(a, b); break; }
      e = var == 0 ? e : var == 1 ? X.add(e, C) : var == 2 ? X.sub(C, e) : X.xor_(e, C);
    }
    // proved when r is a linear MBA of the operands with the candidate's corner values
    std::unordered_set<u32> forced{at[0]}; if (at[1]) forced.insert(at[1]);
    if (getenv("UNSHROUD_MBA_DEBUG")) {
      fprintf(stderr, "pair: kind %d c %llx  a=%s  b=%s  suspect a %d b %d r %d\n", best.kind, (unsigned long long)best.c, X.str(at[0], 4).c_str(), at[1] ? X.str(at[1], 4).c_str() : "-", (int)sg->isSuspect(at[0]), at[1] ? (int)sg->isSuspect(at[1]) : 0, (int)sg->isSuspect(r));
      for (int k = 0; k < 10; k++) fprintf(stderr, "   test %d: r %llx a %llx b %llx\n", k, (unsigned long long)s[k], (unsigned long long)sg->of(at[0])[k], at[1] ? (unsigned long long)sg->of(at[1])[k] : 0ull);
    }
    exact = proveLinear(r, e, &forced) || provePoly(r, e, nullptr);
    if (!exact && o.exactOnly && o.proveArith && S && sg->same(e, r)) { st.cmpTried++; exact = S->proveLocal(r, e, at, at[1] ? 2 : 1, o.proveLocalMs); if (exact) st.cmpProved++; }
    if (!exact && o.exactOnly) continue;
    return e;
  }
  return 0;
}

// The cone of r down to the atoms, with the atoms and every other leaf below (variables, comparisons) given free values:
// does r compute the operation `kind` (see pairSearch) on the atoms on every test? An identity found on the values the
// operands happen to take (a | b = a + b while they share no bit) fails here.
bool Mba::freed(u32 r, const u32* atoms, int na, int kind, u64 c) {
  const unsigned w = X.W(r); const u64 m = maskOf(w);
  const int n = 64;
  static const u64 special[] = {0, 1, 2, ~0ull, ~0ull - 1, 0x8000000000000000ull, 0x7fffffffffffffffull, 0xffffffffull, 0x100000000ull, 0x5555555555555555ull, 0xaaaaaaaaaaaaaaaaull};
  u64 rs = 0x243F6A8885A308D3ull ^ ((u64)r << 20) ^ atoms[0];
  auto rnd = [&]() { rs += 0x9E3779B97F4A7C15ull; u64 z = rs; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull; z = (z ^ (z >> 27)) * 0x94D049BB133111EBull; return z ^ (z >> 31); };
  X.newGen();
  std::vector<u64> buf((size_t)na * n); u32 slots = (u32)na;
  for (int i = 0; i < na; i++) {
    u64* o = &buf[(size_t)i * n]; const u64 ma = maskOf(X.W(atoms[i]));
    for (int k = 0; k < n; k++) o[k] = (k < 4 ? (((k >> i) & 1) ? ma : 0) : k < 16 ? special[rnd() % 11] : rnd()) & ma;
    // the second atom equal to the first, and next to it (what a comparison turns on)
    if (i == 1 && X.W(atoms[0]) == X.W(atoms[1])) for (int k = 16; k < 28; k++) o[k] = (buf[k] + (k < 20 ? 0 : k < 24 ? 1 : ~0ull)) & ma;
    // around the constant it is compared with
    if (i == 0 && kind >= 60) for (int k = 16; k < 28; k++) o[k] = (c + (u64)((k - 16) % 3) - 1) & ma;
    X.stamp[atoms[i]] = X.gen; X.memo[atoms[i]] = (u64)i;
  }
  if (X.stamp[r] == X.gen) return false;
  unsigned wmax = 0; for (int i = 0; i < na; i++) wmax = std::max(wmax, X.W(atoms[i]));
  std::vector<u32> st{r};
  while (!st.empty()) {
    const u32 id = st.back();
    if (X.stamp[id] == X.gen) { st.pop_back(); continue; }
    const Node& x = X.N(id);
    const bool leaf = x.op == O_VAR || x.op == O_CONST || isCompare(x.op) || sg->isSuspect(id);
    // bits of an atom, computed another way (the constructors push extractions down into what an atom is made of):
    // a node whose values are a slice of an atom's on every test takes that slice of the atom's free value
    if (!leaf && x.w <= wmax && x.op != O_EXTRACT) {
      int from = -1; unsigned lo = 0;
      const u64* sv = sg->of(id); const u64 mx = maskOf(x.w);
      for (int i = 0; i < na && from < 0; i++) {
        const u64* av = sg->of(atoms[i]); const unsigned wat = X.W(atoms[i]);
        for (unsigned l = 0; l + x.w <= wat && from < 0; l++) {
          if (((av[5] >> l) & mx) != sv[5] || ((av[6] >> l) & mx) != sv[6]) continue;
          bool ok = true;
          for (int k = 0; k < SIG_K && ok; k++) ok = ((av[k] >> l) & mx) == sv[k];
          if (ok && !sg2->full()) { const u64* a2 = sg2->of(atoms[i]); const u64* s2 = sg2->of(id); for (int k = 0; k < SIG_K && ok; k++) ok = ((a2[k] >> l) & mx) == s2[k]; }
          if (ok) { from = i; lo = l; }
        }
      }
      // or its complement / its opposite
      int how = 0;
      for (int i = 0; i < na && from < 0; i++) {
        if (X.W(atoms[i]) != x.w) continue;
        const u64* av = sg->of(atoms[i]);
        for (int h = 1; h <= 2 && from < 0; h++) {
          auto f = [&](u64 v) { return (h == 1 ? ~v : 0 - v) & mx; };
          if (f(av[5]) != sv[5] || f(av[6]) != sv[6]) continue;
          bool ok = true;
          for (int k = 0; k < SIG_K && ok; k++) ok = f(av[k]) == sv[k];
          if (ok && !sg2->full()) { const u64* a2 = sg2->of(atoms[i]); const u64* s2 = sg2->of(id); for (int k = 0; k < SIG_K && ok; k++) ok = f(a2[k]) == s2[k]; }
          if (ok) { from = i; how = h; lo = 0; }
        }
      }
      if (from >= 0) {
        st.pop_back();
        const u32 s = slots++;
        buf.resize((size_t)slots * n);
        for (int k = 0; k < n; k++) { const u64 v = buf[(size_t)from * n + k]; buf[(size_t)s * n + k] = (how == 1 ? ~v : how == 2 ? 0 - v : v >> lo) & mx; }
        X.memo[id] = s; X.stamp[id] = X.gen;
        continue;
      }
    }
    // a sum which is the atoms' sum or difference plus a constant (the constructors flatten A + B into the terms of A and
    // of B: the node A + B is not made of the nodes A and B any more)
    if (!leaf && x.op == O_ADD && x.w == w) {
      const u64* sv = sg->of(id); const u64* s2 = sg2->full() ? nullptr : sg2->of(id);
      const u64* av[2] = {nullptr, nullptr}; const u64* a2[2] = {nullptr, nullptr};
      for (int i = 0; i < na; i++) if (X.W(atoms[i]) == w) { av[i] = sg->of(atoms[i]); a2[i] = s2 ? sg2->of(atoms[i]) : nullptr; }
      static const int combos[5][2] = {{1, 1}, {1, -1}, {-1, 1}, {1, 0}, {0, 1}};
      int hit = -1; u64 cc = 0;
      for (int q = 0; q < 5 && hit < 0; q++) {
        const int s0 = combos[q][0], s1 = combos[q][1];
        if ((s0 && !av[0]) || (s1 && !(na > 1 && av[1]))) continue;
        auto f = [&](const u64* const* a, int k) -> u64 { return ((s0 ? (s0 > 0 ? a[0][k] : 0 - a[0][k]) : 0) + (s1 ? (s1 > 0 ? a[1][k] : 0 - a[1][k]) : 0)) & m; };
        const u64 c0 = (sv[5] - f(av, 5)) & m;
        if (((f(av, 6) + c0) & m) != sv[6]) continue;
        bool ok = true;
        for (int k = 0; k < SIG_K && ok; k++) ok = ((f(av, k) + c0) & m) == sv[k];
        if (ok && s2) for (int k = 0; k < SIG_K && ok; k++) ok = ((f(a2, k) + c0) & m) == s2[k];
        if (ok) { hit = q; cc = c0; }
      }
      if (hit >= 0) {
        st.pop_back();
        const u32 s = slots++;
        buf.resize((size_t)slots * n);
        const int s0 = combos[hit][0], s1 = combos[hit][1];
        for (int k = 0; k < n; k++) {
          const u64 v0 = s0 ? buf[k] : 0, v1 = s1 ? buf[(size_t)n + k] : 0;
          buf[(size_t)s * n + k] = ((s0 > 0 ? v0 : 0 - v0) + (s1 > 0 ? v1 : 0 - v1) + cc) & m;
        }
        X.memo[id] = s; X.stamp[id] = X.gen;
        continue;
      }
    }
    if (!leaf) {
      bool ready = true;
      if (x.a && X.stamp[x.a] != X.gen) { st.push_back(x.a); ready = false; }
      if (x.b && X.stamp[x.b] != X.gen) { st.push_back(x.b); ready = false; }
      if (x.c && X.stamp[x.c] != X.gen) { st.push_back(x.c); ready = false; }
      if (!ready) continue;
    }
    st.pop_back();
    if (slots >= 3000) return false;                           // not a local identity
    const u32 s = slots++;
    buf.resize((size_t)slots * n);
    u64* o = &buf[(size_t)s * n];
    const u64 mx = maskOf(x.w);
    if (x.op == O_CONST) { for (int k = 0; k < n; k++) o[k] = x.k; }
    else if (leaf) { for (int k = 0; k < n; k++) o[k] = (k < 16 && (rnd() & 1) ? special[rnd() % 11] : rnd()) & mx; }
    else evalVec(x.op, x.w, x.lo, x.k, x.a ? &buf[(size_t)X.memo[x.a] * n] : nullptr, x.b ? &buf[(size_t)X.memo[x.b] * n] : nullptr, x.c ? &buf[(size_t)X.memo[x.c] * n] : nullptr, o, n);
    X.memo[id] = s; X.stamp[id] = X.gen;
  }
  const u64* got = &buf[(size_t)X.memo[r] * n];
  const u64* a = &buf[0]; const u64* b = na > 1 ? &buf[n] : nullptr;
  for (int k = 0; k < n; k++) {
    u64 e;
    if (kind >= 40) {
      const unsigned wa = X.W(atoms[0]);
      switch (kind) { case 40: e = a[k] == 0; break; case 41: e = a[k] != 0; break; case 50: e = a[k] < b[k]; break; case 51: e = a[k] <= b[k]; break;
                      case 52: e = sx(a[k], wa) < sx(b[k], wa); break; case 53: e = sx(a[k], wa) <= sx(b[k], wa); break;
                      case 60: e = a[k] < c; break; case 61: e = c < a[k]; break; case 62: e = sx(a[k], wa) < sx(c, wa); break; case 63: e = sx(c, wa) < sx(a[k], wa); break;
                      case 64: e = a[k] == c; break;
                      case 70: e = !(a[k] < c); break; case 71: e = !(c < a[k]); break; case 72: e = !(sx(a[k], wa) < sx(c, wa)); break; case 73: e = !(sx(c, wa) < sx(a[k], wa)); break;
                      default: e = a[k] != c; break; }
    } else if (kind < 10) {
      switch (kind) { case 0: e = ~a[k]; break; case 1: e = 0 - a[k]; break; case 2: e = a[k] + c; break; case 3: e = a[k] ^ c; break;
                      case 4: e = a[k] * c; break; case 5: e = a[k] & c; break; default: e = a[k] | c; break; }
    } else {
      const int op = (kind - 10) / 4, var = (kind - 10) % 4;
      switch (op) { case 0: e = a[k] + b[k]; break; case 1: e = a[k] - b[k]; break; case 2: e = b[k] - a[k]; break; case 3: e = a[k] * b[k]; break;
                    case 4: e = a[k] & b[k]; break; case 5: e = a[k] | b[k]; break; default: e = a[k] ^ b[k]; break; }
      e = var == 0 ? e : var == 1 ? e + c : var == 2 ? c - e : e ^ c;
    }
    if ((e & m) != got[k]) return false;
  }
  return true;
}

}  // namespace unshroud
