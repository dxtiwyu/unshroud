#include "mba.hpp"
#include "solver.hpp"
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <random>
#include <unordered_set>
#include <functional>
#include <map>

namespace unshroud {

static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

Mba::Mba(Ctx& X, Solver* S) : X(X), S(S) {
  if (const char* e = getenv("UNSHROUD_MBA_LEGACY")) o.legacy = *e && *e != 48;
  if (const char* e = getenv("UNSHROUD_MBA_SPLITCONE")) o.splitCone = atoi(e);
  if (const char* e = getenv("UNSHROUD_MBA_PAIRMAX")) o.pairMax = atoi(e);
  if (const char* e = getenv("UNSHROUD_VERIFY_ALL")) o.verifyAll = *e && *e != 48;
  if (const char* e = getenv("UNSHROUD_VERIFY_MS")) o.verifyMs = (u32)atoi(e);
}

static inline bool interior(u8 op) { return op == O_ADD || op == O_MUL || op == O_NEG || op == O_AND || op == O_OR || op == O_XOR || op == O_NOT; }

namespace {
// the MBA part of an expression, compiled: atoms are inputs
struct Fn {
  struct I { u8 op; u32 a, b; };            // operands: index into slots
  std::vector<I> ins;                       // interior nodes in order
  std::vector<u64> slot;                    // atoms first, then constants, then interior nodes
  std::vector<u32> atoms;                   // atom node ids
  u32 nAtoms = 0, nConst = 0;
  unsigned w = 64; u64 m = ~0ull;
  bool exactLinear = true;                  // no product of two non-constants, no constant inside a bitwise operation
  bool products = false;                    // a product of two non-constants
  std::vector<u64> bitConsts;               // constants used inside bitwise operations
  int interiorCount = 0;
  bool cut = false;                         // a node was made an atom by the depth limit / the region bound
  const std::unordered_set<u32>* forced = nullptr;   // nodes which are atoms whatever they are
  bool build(Ctx& X, u32 root, int maxAtoms, int depthLimit = 1 << 30) {
    w = X.W(root); m = maskOf(w);
    std::unordered_map<u32, u32> idx;       // node -> slot
    std::vector<u32> order, consts;
    std::unordered_map<u32, std::pair<u32, u32>> lowAnd;   // zext(low bits of a) -> (a, mask constant)
    // the depth at which each interior node is first met (breadth first): deeper than the limit, it is an atom
    std::unordered_map<u32, int> depth;
    if (depthLimit < (1 << 30)) {
      std::vector<u32> cur{root}; depth[root] = 0;
      for (int d = 0; d < depthLimit && !cur.empty(); d++) {
        std::vector<u32> next;
        for (u32 id : cur) { const Node& x = X.N(id); if (!interior(x.op)) continue;
          for (u32 c : {x.a, x.b}) if (c && !depth.count(c)) { depth[c] = d + 1; next.push_back(c); } }
        cur.swap(next);
      }
    }
    // depthLimit -1: the subterms used twice or more inside the region are atoms (the operands of an MBA identity)
    std::unordered_set<u32> shared;
    if (depthLimit == -1) {
      // breadth first, over a bounded part of the region: what is not reached is an atom
      std::unordered_map<u32, int> uses; std::vector<u32> todo{root}; std::unordered_set<u32> seen{root};
      for (size_t head = 0; head < todo.size(); head++) {
        u32 id = todo[head]; const Node& x = X.N(id);
        if (!interior(x.op)) continue;
        if (head >= 256) { if (id != root) { shared.insert(id); cut = true; } continue; }
        for (u32 c : {x.a, x.b}) if (c) { if (++uses[c] == 2 && c != root && X.N(c).op != O_CONST) shared.insert(c); if (seen.insert(c).second) todo.push_back(c); }
      }
      if (shared.empty()) return false;
      depthLimit = 1 << 30;
    }
    // depthLimit -2: the products of two non-constants are atoms (what is around them may be a linear MBA of them and the variables)
    bool prodAtoms = false, anyProd = false;
    if (depthLimit == -2) { prodAtoms = true; depthLimit = 1 << 30; }
    auto isAtom = [&](u32 id) { if (!interior(X.N(id).op)) return X.N(id).op != O_CONST; if (shared.count(id)) return true;
      if (prodAtoms && X.N(id).op == O_MUL && X.N(X.N(id).a).op != O_CONST && X.N(X.N(id).b).op != O_CONST) { anyProd = true; cut = true; return true; } if (forced && forced->count(id)) return true; if (depthLimit >= (1 << 30)) return false; auto it = depth.find(id); bool at = it == depth.end() || it->second >= depthLimit; if (at) cut = true; return at; };
    // atoms and constants first (discovery), interior nodes in post-order
    std::vector<std::pair<u32, int>> st{{root, 0}};
    std::unordered_set<u32> done;
    while (!st.empty()) {
      auto& top = st.back(); u32 id = top.first; const Node& x = X.N(id);
      if (done.count(id)) { st.pop_back(); continue; }
      const bool deep = depthLimit < (1 << 30) && (depth.find(id) == depth.end() || depth[id] >= depthLimit);
      if (x.op == O_ZEXT && X.N(x.a).op == O_EXTRACT && X.N(x.a).lo == 0 && X.W(X.N(x.a).a) == X.W(id) && id != root && !deep) {
        // the low bits of a, as a & mask: an AND for the analysis
        u32 inner = X.N(x.a).a, mk = X.cst(maskOf(X.N(x.a).w), X.W(id));
        if (!done.count(inner) && top.second == 0) { top.second = 1; st.push_back({inner, 0}); continue; }
        if (!done.count(mk)) { done.insert(mk); consts.push_back(mk); }
        done.insert(id); order.push_back(id); lowAnd[id] = {inner, mk}; st.pop_back();
        continue;
      }
      if (x.op == O_CONST || (id != root && isAtom(id))) {
        done.insert(id); st.pop_back();
        if (x.op == O_CONST) consts.push_back(id); else { atoms.push_back(id); if ((int)atoms.size() > maxAtoms) return false; }
        continue;
      }
      u32 kids[2] = {x.a, x.b}; int nk = (x.op == O_NEG || x.op == O_NOT) ? 1 : 2;
      if (top.second < nk) { u32 c = kids[top.second++]; if (!done.count(c)) st.push_back({c, 0}); continue; }
      done.insert(id); order.push_back(id); st.pop_back();
    }
    if ((int)atoms.size() > maxAtoms) return false;
    if (prodAtoms && !anyProd) return false;                  // (no product: the whole region again)
    nAtoms = (u32)atoms.size(); nConst = (u32)consts.size();
    for (u32 i = 0; i < nAtoms; i++) idx[atoms[i]] = i;
    for (u32 i = 0; i < nConst; i++) idx[consts[i]] = nAtoms + i;
    slot.assign(nAtoms + nConst + order.size(), 0);
    for (u32 i = 0; i < nConst; i++) slot[nAtoms + i] = X.N(consts[i]).k;
    // a linear MBA: bitwise operations on atoms (class 0), combined by + - and products by constants (class 1); 2: a constant
    std::vector<u8> cls(slot.size(), 0);
    for (u32 i = 0; i < nConst; i++) { const u64 k = X.N(consts[i]).k; cls[nAtoms + i] = (k == 0 || k == m) ? 0 : 2; }
    for (u32 id : order) {
      auto la = lowAnd.find(id);
      if (la != lowAnd.end()) {
        u64 mv = X.cv(la->second.second);
        if (std::find(bitConsts.begin(), bitConsts.end(), mv) == bitConsts.end()) bitConsts.push_back(mv);
        exactLinear = false;
        idx[id] = (u32)(nAtoms + nConst + ins.size());
        cls[idx[id]] = 1;
        ins.push_back(I{O_AND, idx[la->second.first], idx[la->second.second]});
        continue;
      }
      const Node& x = X.N(id);
      I in{x.op, idx[x.a], x.b ? idx[x.b] : 0};
      if (x.op == O_MUL && !X.isC(x.a) && !X.isC(x.b)) { exactLinear = false; products = true; }
      if (x.op == O_AND || x.op == O_OR || x.op == O_XOR)
        for (u32 c : {x.a, x.b}) if (X.isC(c) && X.cv(c) != 0 && X.cv(c) != m) {
          exactLinear = false;
          if (std::find(bitConsts.begin(), bitConsts.end(), X.cv(c)) == bitConsts.end()) bitConsts.push_back(X.cv(c));
        }
      idx[id] = (u32)(nAtoms + nConst + ins.size());
      {
        const u8 ca = cls[in.a], cb = cls[in.b]; u8 c = 1;
        if (x.op == O_AND || x.op == O_OR || x.op == O_XOR) { if (ca == 0 && cb == 0) c = 0; else exactLinear = false; }
        else if (x.op == O_NOT) c = ca == 0 ? 0 : 1;
        cls[idx[id]] = c;
      }
      ins.push_back(in);
    }
    interiorCount = (int)order.size();
    return !order.empty();
  }
  u64 eval(const u64* atomVals) {
    for (u32 i = 0; i < nAtoms; i++) slot[i] = atomVals[i] & m;
    u32 base = nAtoms + nConst;
    for (size_t i = 0; i < ins.size(); i++) {
      const I& x = ins[i]; u64 a = slot[x.a], b = slot[x.b], r;
      switch (x.op) {
      case O_ADD: r = a + b; break; case O_MUL: r = a * b; break; case O_NEG: r = 0 - a; break;
      case O_AND: r = a & b; break; case O_OR: r = a | b; break; case O_XOR: r = a ^ b; break; default: r = ~a; break;
      }
      slot[base + i] = r & m;
    }
    return ins.empty() ? 0 : slot[base + ins.size() - 1];
  }
};
}  // namespace

// ------------------------------------------------------------------------------------------------ minimal boolean formulas
namespace {
struct BoolForm { u8 cost = 255; u8 op = 0; u16 a = 0, b = 0; };   // op: 0 atom/const, 1 not, 2 and, 3 or, 4 xor
struct BoolTable {
  int t = -1; std::vector<BoolForm> best; u16 full = 0; int maxCost = 0;
  void build(int nt, int deep = 0) {
    t = nt; const int n = 1 << t; full = (u16)((1u << n) - 1);
    best.assign(1u << n, BoolForm{});
    std::vector<std::vector<u16>> byCost(1);
    auto add = [&](u16 tt, u8 cost, u8 op, u16 a, u16 b) {
      tt &= full;
      if (best[tt].cost <= cost) return;
      bool fresh = best[tt].cost == 255;
      best[tt] = {cost, op, a, b};
      if (fresh || true) { if (byCost.size() <= cost) byCost.resize(cost + 1); byCost[cost].push_back(tt); }
    };
    for (int i = 0; i < t; i++) { u16 v = 0; for (int b = 0; b < n; b++) if ((b >> i) & 1) v |= (u16)(1u << b); add(v, 0, 0, (u16)i, 0); }
    add(0, 0, 0, 100, 0); add(full, 0, 0, 101, 0);
    maxCost = t <= 3 ? 9 : deep ? deep : 5;
    for (int c = 1; c <= maxCost; c++) {
      if (byCost.size() <= (size_t)c) byCost.resize(c + 1);
      for (u16 a : std::vector<u16>(byCost[c - 1])) if (best[a].cost == c - 1) add((u16)~a, (u8)c, 1, a, 0);
      for (int i = 0; i <= (c - 1) / 2; i++) {
        int j = c - 1 - i;
        std::vector<u16> L1(byCost[i]), L2(byCost[j]);
        for (u16 a : L1) { if (best[a].cost != i) continue;
          for (u16 b : L2) { if (best[b].cost != j) continue;
            add(a & b, (u8)c, 2, a, b); add(a | b, (u8)c, 3, a, b); add(a ^ b, (u8)c, 4, a, b); } }
      }
    }
  }
};
BoolTable g_bool[5];
}

// the boolean function with truth table tt over the atoms, as an expression (0 if none is known)
static u32 boolExpr(Ctx& X, int t, u16 tt, const std::vector<u32>& atoms, unsigned w) {
  BoolTable& T = g_bool[t];
  if (T.t != t) T.build(t);
  tt &= T.full;
  // four atoms: formulas of up to 5 operations are tabulated at once, up to 8 when a function needs it (once per process)
  if (T.best[tt].cost == 255 && t == 4 && T.maxCost < 8) T.build(4, 8);
  if (T.best[tt].cost == 255) {
    // algebraic normal form: xor of conjunctions
    const int n = 1 << t; std::vector<u8> c(n);
    for (int b = 0; b < n; b++) c[b] = (tt >> b) & 1;
    for (int i = 0; i < t; i++) for (int s = 0; s < n; s++) if (s & (1 << i)) c[s] ^= c[s ^ (1 << i)];
    u32 acc = X.cst(0, w);
    for (int s = 0; s < n; s++) if (c[s]) {
      u32 term = X.cst(maskOf(w), w);
      for (int i = 0; i < t; i++) if (s & (1 << i)) term = X.and_(term, atoms[i]);
      acc = X.xor_(acc, term);
    }
    return acc;
  }
  std::function<u32(u16)> mk = [&](u16 f) -> u32 {
    const BoolForm& b = T.best[f & T.full];
    switch (b.op) {
    case 0: return b.a == 100 ? X.cst(0, w) : b.a == 101 ? X.cst(maskOf(w), w) : atoms[b.a];
    case 1: return X.not_(mk(b.a));
    case 2: return X.and_(mk(b.a), mk(b.b));
    case 3: return X.or_(mk(b.a), mk(b.b));
    default: return X.xor_(mk(b.a), mk(b.b));
    }
  };
  return mk(tt);
}

// ------------------------------------------------------------------------------------------------ checking a candidate
namespace {
struct FastRng { u64 s; u64 operator()() { s += 0x9E3779B97F4A7C15ull; u64 z = s; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull; z = (z ^ (z >> 27)) * 0x94D049BB133111EBull; return z ^ (z >> 31); } };
struct Checker {
  Ctx& X; Fn& f; FastRng rng{0x5eed}; int n; bool ready = false;
  std::vector<std::vector<u64>> tests;       // atom assignments
  std::vector<u64> want;
  std::unordered_set<u32> atomSet;
  Checker(Ctx& X, Fn& f, int n) : X(X), f(f), n(n), atomSet(f.atoms.begin(), f.atoms.end()) {}
  // the tests are made when something is to be checked
  void ensure() {
    if (ready) return;
    ready = true;
    const u64 special[] = {0, 1, 2, ~0ull, ~0ull - 1, 0x8000000000000000ull, 0x7fffffffffffffffull, 0xffffffffull, 0x100000000ull, 0x5555555555555555ull, 0xaaaaaaaaaaaaaaaaull};
    // the corner points first (every atom 0 or -1): two linear MBAs which agree there are the same function
    const int corners = f.nAtoms <= 8 ? 1 << f.nAtoms : 0;
    tests.reserve(n + corners); want.reserve(n + corners);
    for (int k = 0; k < n + corners; k++) {
      std::vector<u64> v(f.nAtoms);
      if (k < corners) { for (u32 i = 0; i < f.nAtoms; i++) v[i] = ((k >> i) & 1) ? ~0ull : 0; }
      else for (u32 i = 0; i < f.nAtoms; i++) v[i] = (k - corners < 24 && rng() % 2) ? special[rng() % 11] : rng();
      want.push_back(f.eval(v.data()));
      tests.push_back(std::move(v));
    }
  }
  // the same value on two quick assignments? (then worth the full constant test)
  bool maybeConstant() {
    FastRng r2{0x1234}; std::vector<u64> v(f.nAtoms);
    for (u32 i = 0; i < f.nAtoms; i++) v[i] = r2();
    const u64 a = f.eval(v.data());
    for (u32 i = 0; i < f.nAtoms; i++) v[i] = r2();
    return f.eval(v.data()) == a;
  }
  // does candidate c compute the same on every test? (its leaves must be among the atoms)
  bool lastLinear = false;                   // the last candidate accepted is a linear MBA of the atoms (or an atom, a constant)
  bool ok(u32 c) {
    ensure();
    lastLinear = true;
    Fn g; g.forced = &atomSet;
    if (X.isC(c)) { for (u64 v : want) if (v != X.cv(c)) return false; return true; }
    {                             // an atom by itself
      auto it = std::find(f.atoms.begin(), f.atoms.end(), c);
      if (it != f.atoms.end()) {
        size_t i = it - f.atoms.begin();
        for (size_t k = 0; k < tests.size(); k++) if ((tests[k][i] & f.m) != want[k]) return false;
        return true;
      }
      if (!interior(X.N(c).op)) return false;
    }
    if (!g.build(X, c, 64)) return false;
    lastLinear = g.exactLinear;
    std::vector<int> map(g.nAtoms);
    for (u32 i = 0; i < g.nAtoms; i++) {
      auto it = std::find(f.atoms.begin(), f.atoms.end(), g.atoms[i]);
      if (it == f.atoms.end()) return false;
      map[i] = (int)(it - f.atoms.begin());
    }
    std::vector<u64> v(g.nAtoms);
    for (size_t k = 0; k < tests.size(); k++) {
      for (u32 i = 0; i < g.nAtoms; i++) v[i] = tests[k][map[i]];
      if (g.eval(v.data()) != want[k]) return false;
    }
    return true;
  }
};
}

// ------------------------------------------------------------------------------------------------ synthesis
namespace {
const int K = 16;
struct Cand { u8 op; u8 size; u32 a, b; u64 v[K]; };
}

// Bottom-up enumeration of expressions over leaves (nodes of width w) and constants, deduplicated by their values on the
// test assignments, until one has the target values. tests[k][i]: the value of leaf i in test k.
static u32 synthesizeOver(Ctx& X, const std::vector<u32>& leaves, const std::vector<u64>& constsIn, const std::vector<std::vector<u64>>& tests,
                          const std::vector<u64>& want, unsigned w, int maxSize, u32 maxCands) {
  const u64 m = maskOf(w);
  std::vector<Cand> C; C.reserve(1 << 16);
  std::unordered_set<u64> seen;
  u64 target[K]; for (int k = 0; k < K; k++) target[k] = want[k] & m;
  auto sig = [&](const u64* v) { u64 h = 0xcbf29ce484222325ull; for (int k = 0; k < K; k++) h = (h ^ v[k]) * 0x100000001b3ull; return h; };
  const u64 th = sig(target);
  std::vector<std::vector<u32>> level(1);
  int found = -1;
  auto push = [&](Cand& c) {
    u64 h = sig(c.v);
    if (seen.count(h)) return;
    seen.insert(h);
    level[c.size].push_back((u32)C.size());
    C.push_back(c);
    if (h == th && memcmp(c.v, target, sizeof target) == 0) found = (int)C.size() - 1;
  };
  for (u32 i = 0; i < leaves.size(); i++) { Cand c{0, 0, i, 0, {}}; for (int k = 0; k < K; k++) c.v[k] = tests[k][i] & m; push(c); }
  for (u64 k0 : constsIn) { Cand c{1, 0, 0, 0, {}}; c.a = (u32)(k0 & 0xffffffff); c.b = (u32)(k0 >> 32); for (int k = 0; k < K; k++) c.v[k] = k0 & m; push(c); }
  for (int s = 1; s <= maxSize && found < 0 && C.size() < maxCands; s++) {
    level.resize(s + 1);
    for (u32 ia : std::vector<u32>(level[s - 1])) {
      Cand c{2, (u8)s, ia, 0, {}}; for (int k = 0; k < K; k++) c.v[k] = ~C[ia].v[k] & m; push(c);
      Cand d{3, (u8)s, ia, 0, {}}; for (int k = 0; k < K; k++) d.v[k] = (0 - C[ia].v[k]) & m; push(d);
      if (found >= 0) break;
    }
    for (int i = 0; i <= s - 1 && found < 0; i++) {
      int j = s - 1 - i;
      std::vector<u32> L1(level[i]), L2(level[j]);
      for (u32 ia : L1) {
        for (u32 ib : L2) {
          u64 va[K], vb[K]; memcpy(va, C[ia].v, sizeof va); memcpy(vb, C[ib].v, sizeof vb);   // C grows below
          for (u8 op = 4; op <= 9; op++) {
            if (op != 9 && i > j) continue;                // commutative: once
            Cand c{op, (u8)s, ia, ib, {}};
            for (int k = 0; k < K; k++) {
              u64 r;
              switch (op) { case 4: r = va[k] + vb[k]; break; case 5: r = va[k] * vb[k]; break; case 6: r = va[k] & vb[k]; break;
                            case 7: r = va[k] | vb[k]; break; case 8: r = va[k] ^ vb[k]; break; default: r = va[k] - vb[k]; break; }
              c.v[k] = r & m;
            }
            push(c);
            if (found >= 0 || C.size() >= maxCands) break;
          }
          if (found >= 0 || C.size() >= maxCands) break;
        }
        if (found >= 0 || C.size() >= maxCands) break;
      }
    }
  }
  if (found < 0) return 0;
  std::function<u32(u32)> mk = [&](u32 i) -> u32 {
    const Cand& c = C[i];
    switch (c.op) {
    case 0: return leaves[c.a];
    case 1: return X.cst(((u64)c.b << 32) | c.a, w);
    case 2: return X.not_(mk(c.a));
    case 3: return X.neg(mk(c.a));
    case 4: return X.add(mk(c.a), mk(c.b));
    case 5: return X.mul(mk(c.a), mk(c.b));
    case 6: return X.and_(mk(c.a), mk(c.b));
    case 7: return X.or_(mk(c.a), mk(c.b));
    case 8: return X.xor_(mk(c.a), mk(c.b));
    default: return X.sub(mk(c.a), mk(c.b));
    }
  };
  return mk((u32)found);
}

// Meet in the middle: a table of every expression up to a size, then the target split at its top operation. For ^ + - and
// * by an odd value the other operand's values follow from the target's and are looked up; for & and | the operands are
// supersets / subsets of the target. The operand which is not in the table is split the same way once more.
namespace {
struct Table {
  std::vector<Cand> C; std::unordered_map<u64, u32> bySig; u64 m;
  static u64 sig(const u64* v) { u64 h = 0xcbf29ce484222325ull; for (int k = 0; k < K; k++) h = (h ^ v[k]) * 0x100000001b3ull; return h; }
  int find(const u64* v) const { auto it = bySig.find(sig(v)); if (it == bySig.end() || memcmp(C[it->second].v, v, sizeof(u64) * K)) return -1; return (int)it->second; }
  bool add(Cand& c) { u64 h = sig(c.v); if (bySig.count(h)) return false; bySig[h] = (u32)C.size(); C.push_back(c); return true; }
};
}

static u32 synthesizeMITM(Ctx& X, const std::vector<u32>& leaves, const std::vector<u64>& consts, const std::vector<std::vector<u64>>& tests,
                          const std::vector<u64>& want, unsigned w, int tableSize, u32 maxTable, double budgetSec) {
  const u64 m = maskOf(w);
  Table T; T.m = m; T.C.reserve(1 << 16);
  std::vector<std::vector<u32>> level(1);
  auto push = [&](Cand& c) { if (T.add(c)) level[c.size].push_back((u32)T.C.size() - 1); };
  for (u32 i = 0; i < leaves.size(); i++) { Cand c{0, 0, i, 0, {}}; for (int k = 0; k < K; k++) c.v[k] = tests[k][i] & m; push(c); }
  for (u64 k0 : consts) { Cand c{1, 0, (u32)(k0 & 0xffffffff), (u32)(k0 >> 32), {}}; for (int k = 0; k < K; k++) c.v[k] = k0 & m; push(c); }
  for (int sz = 1; sz <= tableSize && T.C.size() < maxTable; sz++) {
    level.resize(sz + 1);
    for (u32 ia : std::vector<u32>(level[sz - 1])) {
      Cand c{2, (u8)sz, ia, 0, {}}; for (int k = 0; k < K; k++) c.v[k] = ~T.C[ia].v[k] & m; push(c);
      Cand d{3, (u8)sz, ia, 0, {}}; for (int k = 0; k < K; k++) d.v[k] = (0 - T.C[ia].v[k]) & m; push(d);
    }
    for (int i = 0; i <= sz - 1 && T.C.size() < maxTable; i++) {
      int j = sz - 1 - i;
      std::vector<u32> L1(level[i]), L2(level[j]);
      for (u32 ia : L1) {
        u64 va[K]; memcpy(va, T.C[ia].v, sizeof va);
        for (u32 ib : L2) {
          u64 vb[K]; memcpy(vb, T.C[ib].v, sizeof vb);
          for (u8 op = 4; op <= 9; op++) {
            if (op != 9 && i > j) continue;
            Cand c{op, (u8)sz, ia, ib, {}};
            for (int k = 0; k < K; k++) {
              u64 r;
              switch (op) { case 4: r = va[k] + vb[k]; break; case 5: r = va[k] * vb[k]; break; case 6: r = va[k] & vb[k]; break;
                            case 7: r = va[k] | vb[k]; break; case 8: r = va[k] ^ vb[k]; break; default: r = va[k] - vb[k]; break; }
              c.v[k] = r & m;
            }
            push(c);
          }
          if (T.C.size() >= maxTable) break;
        }
        if (T.C.size() >= maxTable) break;
      }
    }
  }
  std::function<u32(u32)> mk = [&](u32 i) -> u32 {
    const Cand& c = T.C[i];
    switch (c.op) {
    case 0: return leaves[c.a];
    case 1: return X.cst(((u64)c.b << 32) | c.a, w);
    case 2: return X.not_(mk(c.a)); case 3: return X.neg(mk(c.a));
    case 4: return X.add(mk(c.a), mk(c.b)); case 5: return X.mul(mk(c.a), mk(c.b));
    case 6: return X.and_(mk(c.a), mk(c.b)); case 7: return X.or_(mk(c.a), mk(c.b));
    case 8: return X.xor_(mk(c.a), mk(c.b)); default: return X.sub(mk(c.a), mk(c.b));
    }
  };
  // the split, recursively (depth 2): returns an expression with these values, or 0
  const double deadline = now() + budgetSec;
  std::function<u32(const u64*, int)> solve = [&](const u64* f, int depth) -> u32 {
    if (now() > deadline) return 0;
    int hit = T.find(f);
    if (hit >= 0) return mk((u32)hit);
    if (depth == 0) return 0;
    u64 need[K];
    // ~B, -B
    for (int k = 0; k < K; k++) need[k] = ~f[k] & m;
    if (u32 r = solve(need, depth - 1)) return X.not_(r);
    for (int k = 0; k < K; k++) need[k] = (0 - f[k]) & m;
    if (u32 r = solve(need, depth - 1)) return X.neg(r);
    const size_t n = T.C.size();
    const bool top = depth == 2;
    // A op B with A in the table, B looked up (then split once more at depth 2); the inner searches see the smaller expressions only
    const size_t nA = top ? n : std::min<size_t>(n, 20000);
    for (int pass = 0; pass < 2; pass++) {
      const int sub = pass == 0 ? 0 : depth - 1;     // first only direct hits, then splits of the other operand
      if (pass == 1 && sub == 0) break;
      for (size_t ia = 0; ia < (pass == 0 ? nA : std::min<size_t>(nA, 512)); ia++) {
        if ((ia & 1023) == 0 && now() > deadline) return 0;
        const u64* a = T.C[ia].v;
        for (int k = 0; k < K; k++) need[k] = (f[k] ^ a[k]) & m;            // f = A ^ B
        if (u32 r = solve(need, sub)) return X.xor_(mk((u32)ia), r);
        for (int k = 0; k < K; k++) need[k] = (f[k] - a[k]) & m;            // f = A + B
        if (u32 r = solve(need, sub)) return X.add(mk((u32)ia), r);
        for (int k = 0; k < K; k++) need[k] = (a[k] - f[k]) & m;            // f = A - B
        if (u32 r = solve(need, sub)) return X.sub(mk((u32)ia), r);
        bool odd = true; for (int k = 0; k < K && odd; k++) odd = a[k] & 1;   // f = A * B with A odd
        if (odd) {
          for (int k = 0; k < K; k++) { u64 inv = a[k]; for (int t = 0; t < 6; t++) inv *= 2 - a[k] * inv; need[k] = (f[k] * inv) & m; }
          if (u32 r = solve(need, sub)) return X.mul(mk((u32)ia), r);
        }
      }
    }
    // f = A & B: both are supersets of f; f = A | B: both are subsets (at the top only)
    for (int op = 0; op < 2 && top; op++) {
      std::vector<u32> cand;
      for (size_t ia = 0; ia < n && cand.size() < 3000; ia++) {
        const u64* a = T.C[ia].v; bool ok = true;
        for (int k = 0; k < K && ok; k++) ok = op == 0 ? (f[k] & ~a[k]) == 0 : (a[k] & ~f[k]) == 0;
        if (ok && T.C[ia].op != 1) cand.push_back((u32)ia);
      }
      for (size_t i = 0; i < cand.size(); i++)
        for (size_t j = i + 1; j < cand.size(); j++) {
          const u64* a = T.C[cand[i]].v; const u64* b = T.C[cand[j]].v; bool ok = true;
          for (int k = 0; k < K && ok; k++) ok = ((op == 0 ? (a[k] & b[k]) : (a[k] | b[k])) & m) == f[k];
          if (ok) return op == 0 ? X.and_(mk(cand[i]), mk(cand[j])) : X.or_(mk(cand[i]), mk(cand[j]));
        }
    }
    return 0;
  };
  u64 target[K]; for (int k = 0; k < K; k++) target[k] = want[k] & m;
  return solve(target, 2);
}

// over the atoms of an MBA region: a first pass with the plain constants only (a smaller space reaches deeper), then with
// the region's constants too
static u32 synthesize(Ctx& X, Fn& f, Checker& ck, const MbaOptions& o) {
  ck.ensure();
  std::vector<u64> want(ck.want.begin(), ck.want.begin() + K);
  std::vector<std::vector<u64>> tests(ck.tests.begin(), ck.tests.begin() + K);
  std::vector<u64> base = {0, 1, 2, f.m};
  u32 r = synthesizeOver(X, f.atoms, base, tests, want, f.w, o.synthSize, o.synthMax);
  if (r) return r;
  std::vector<u64> more = base;
  for (u32 i = 0; i < f.nConst && i < 6; i++) more.push_back(f.slot[f.nAtoms + i]);
  if (want[0] == want[1]) more.push_back(want[0]);
  if (more.size() == base.size()) return 0;
  return synthesizeOver(X, f.atoms, more, tests, want, f.w, std::max(3, o.synthSize - 2), o.synthMax);
}

// ------------------------------------------------------------------------------------------------ the methods
// Linear MBA whose bitwise operations also take constants: the bits are grouped by the bits the constants have there
// (a pattern); per pattern the function of the atom bits is recovered from 2^t evaluations, as in the plain method.
static u32 linearConst(Ctx& X, Fn& f, std::vector<u64>& pureOut, bool& pure) {
  const u32 t = f.nAtoms, n = 1u << t; const u64 m = f.m; const unsigned w = f.w;
  const std::vector<u64>& K = f.bitConsts;
  pure = false;
  if (K.empty() || K.size() > 3 || t > 4) return 0;
  std::map<u32, u64> masks;                         // pattern -> the bits which have it
  for (unsigned j = 0; j < w; j++) { u32 pat = 0; for (size_t k = 0; k < K.size(); k++) pat |= (u32)((K[k] >> j) & 1) << k; masks[pat] |= 1ull << j; }
  std::vector<u64> zero(t, 0);
  const u64 e0 = f.eval(zero.data());
  std::vector<u64> av(t);
  // D[p][b] = G(b, p) - G(0, p), as a small signed integer
  std::map<u32, std::vector<i64>> D;
  for (auto& [pat, M] : masks) {
    std::vector<i64>& d = D[pat]; d.assign(n, 0);
    unsigned long l; _BitScanForward64(&l, M);
    const unsigned keep = w - l;                    // D * M is known modulo 2^w: D modulo 2^(w - l)
    // M >> l is odd: D = (v >> l) * inverse(M >> l) modulo 2^keep
    u64 Mo = M >> l, inv = Mo; for (int i = 0; i < 6; i++) inv *= 2 - Mo * inv;
    for (u32 b = 1; b < n; b++) {
      for (u32 i = 0; i < t; i++) av[i] = ((b >> i) & 1) ? M : 0;
      u64 v = (f.eval(av.data()) - e0) & m;
      if (v & ((1ull << l) - 1)) return 0;          // not of the form D * M: not a linear MBA with constants
      u64 dm = ((v >> l) * inv) & maskOf(keep);
      d[b] = keep >= 64 ? (i64)dm : sx(dm, keep);
    }
  }
  // pure bitwise? G(b, p) in {0, 1} everywhere, with G(0, p) the bits of e0 there
  pure = true;
  std::map<u32, std::vector<int>> G;
  for (auto& [pat, M] : masks) {
    u64 g0bits = e0 & M;
    if (g0bits != 0 && g0bits != M) { pure = false; break; }
    int g0 = g0bits ? 1 : 0;
    std::vector<int>& g = G[pat]; g.assign(n, 0);
    for (u32 b = 0; b < n; b++) { i64 v = g0 + D[pat][b]; if (v != 0 && v != 1) { pure = false; break; } g[b] = (int)v; }
    if (!pure) break;
  }
  if (pure && t + K.size() <= 4) {
    // a boolean function of the atoms and of the constants' bits (patterns never seen: 0)
    const int nv = (int)(t + K.size());
    u16 tt = 0;
    for (auto& [pat, g] : G) for (u32 b = 0; b < n; b++) if (g[b]) tt |= (u16)(1u << (b | (pat << t)));
    std::vector<u32> vars(f.atoms.begin(), f.atoms.end());
    for (u64 k : K) vars.push_back(X.cst(k, w));
    pureOut.push_back(boolExpr(X, nv, tt, vars, w));
  } else pure = false;
  // the masked conjunction basis: e = e0 + sum over S != {} and patterns of c[S,p] * (AND_S & M_p)
  u32 acc = X.cst(e0, w);
  for (u32 S = 1; S < n; S++) {
    std::map<u64, u64> byCoef;                      // coefficient -> union of the masks which have it
    for (auto& [pat, M] : masks) {
      i64 c = 0;
      for (u32 T = S;; T = (T - 1) & S) { c += ((__popcnt(S ^ T) & 1) ? -1 : 1) * D[pat][T]; if (!T) break; }
      if (c) byCoef[(u64)c & m] |= M;
    }
    if (byCoef.empty()) continue;
    u32 term = 0;
    for (u32 i = 0; i < t; i++) if (S & (1u << i)) term = term ? X.and_(term, f.atoms[i]) : f.atoms[i];
    for (auto& [c, M] : byCoef) {
      u32 masked = (M & m) == m ? term : X.and_(term, X.cst(M, w));
      acc = X.add(acc, X.mul(masked, X.cst(c, w)));
    }
  }
  return acc;
}

// A linear MBA whose corner values (G[b] = value at the corner b minus twice the value at 0) are sums of a few
// coefficients: e0 + a1 * F1 + a2 * F2 + a3 * F3 with boolean functions F of the atoms the values depend on (at most 4
// of them; the others drop out). Every choice of F or its complement (a * F = -a - a * ~F) is a candidate: the caller
// keeps the smallest one which passes its tests.
static void fewTerms(Ctx& X, const Fn& f, const std::vector<u64>& G, std::vector<u32>& out) {
  const u32 t = f.nAtoms, n = 1u << t; const u64 m = f.m; const unsigned w = f.w;
  std::vector<u32> ess;
  for (u32 i = 0; i < t; i++) { bool dep = false; for (u32 b = 0; b < n && !dep; b++) dep = G[b] != G[b ^ (1u << i)]; if (dep) ess.push_back(i); }
  const u32 ne = (u32)ess.size();
  if (ne == 0 || ne > 4) return;
  const u32 n2 = 1u << ne;
  std::vector<u64> v(n2); std::vector<u64> D;
  for (u32 b2 = 0; b2 < n2; b2++) {
    u32 b = 0; for (u32 k = 0; k < ne; k++) if (b2 & (1u << k)) b |= 1u << ess[k];
    v[b2] = (G[b] - G[0]) & m;
    if (v[b2] && std::find(D.begin(), D.end(), v[b2]) == D.end()) { D.push_back(v[b2]); if (D.size() > 7) return; }
  }
  if (D.empty()) return;
  // the coefficients: the fewest of the values such that every value is a sum of some of them
  std::vector<u64> a;
  auto sums = [&](const std::vector<u64>& c, u64 d, u32& which) {
    for (u32 s = 1; s < (1u << c.size()); s++) { u64 x = 0; for (size_t j = 0; j < c.size(); j++) if (s & (1u << j)) x += c[j]; if ((x & m) == d) { which = s; return true; } }
    return false;
  };
  auto covers = [&](const std::vector<u64>& c) { u32 s; for (u64 d : D) if (!sums(c, d, s)) return false; return true; };
  if (D.size() == 1) a = D;
  for (size_t i = 0; a.empty() && i < D.size(); i++) for (size_t j = i + 1; a.empty() && j < D.size(); j++) if (covers({D[i], D[j]})) a = {D[i], D[j]};
  for (size_t i = 0; a.empty() && i < D.size(); i++) for (size_t j = i + 1; a.empty() && j < D.size(); j++) for (size_t k = j + 1; a.empty() && k < D.size(); k++)
    if (covers({D[i], D[j], D[k]})) a = {D[i], D[j], D[k]};
  if (a.empty()) return;
  const u32 k = (u32)a.size();
  u16 T[3] = {0, 0, 0};
  for (u32 b2 = 1; b2 < n2; b2++) if (v[b2]) { u32 s = 0; sums(a, v[b2], s); for (u32 j = 0; j < k; j++) if (s & (1u << j)) T[j] |= (u16)(1u << b2); }
  std::vector<u32> atoms; for (u32 i : ess) atoms.push_back(f.atoms[i]);
  const u16 full = (u16)((1u << n2) - 1);
  const u64 e0 = (0 - G[0]) & m;
  for (u32 pol = 0; pol < (1u << k); pol++) {
    u64 c0 = e0; u32 acc = 0;
    for (u32 j = 0; j < k; j++) {
      const bool neg = (pol >> j) & 1;
      const u32 F = boolExpr(X, (int)ne, neg ? (u16)(~T[j] & full) : T[j], atoms, w);
      const u64 coef = neg ? (0 - a[j]) & m : a[j];
      if (neg) c0 = (c0 - a[j]) & m;
      const u32 term = X.mul(F, X.cst(coef, w));
      acc = acc ? X.add(acc, term) : term;
    }
    out.push_back(X.add(acc, X.cst(c0, w)));
  }
}

u32 Mba::top(u32 e, bool synth) {
  const u32 size0 = X.countNodes(e);
  u32 best = 0, bestSize = size0; const char* how = nullptr; bool exact = false; bool uncut = false;
  // the whole MBA region, then regions cut at a depth (deeper subterms are atoms: MBA applied to MBA results)
  for (int depthLimit : {1 << 30, -2, -1, 2, 3, 4, 5, 6}) {
    if (best && bestSize <= 3) break;
    if (depthLimit >= 2 && depthLimit < (1 << 30) && uncut) break;        // deeper cuts are the whole region again
    Fn f;
    const bool built = f.build(X, e, o.maxAtoms, depthLimit);
    if (depthLimit >= 2 && depthLimit < (1 << 30) && !f.cut) uncut = true;
    if (!built || f.interiorCount < 2) continue;
    Checker ck(X, f, std::max(o.tests, K));
    auto consider = [&](u32 c, const char* m, bool ex) {
      if (!c || c == e) return;
      u32 sz = X.countNodes(c);
      if (sz >= bestSize) return;
      if (!ck.ok(c)) return;
      best = c; bestSize = sz; how = m; exact = ex && ck.lastLinear;
    };
    if (ck.maybeConstant()) {
      ck.ensure();
      bool same = true; for (u64 v : ck.want) if (v != ck.want[0]) { same = false; break; }
      if (same) consider(X.cst(ck.want[0], f.w), "constant", f.exactLinear);
    }
    const u32 t = f.nAtoms, n = 1u << t; const u64 m = f.m; const unsigned w = f.w;
    if (!best || bestSize > 1) {
      std::vector<u64> G(n), av(t);
      for (u32 b = 0; b < n; b++) { for (u32 i = 0; i < t; i++) av[i] = (b >> i) & 1; G[b] = f.eval(av.data()); }
      const u64 e0 = G[0];
      for (u32 b = 0; b < n; b++) G[b] = (G[b] - 2 * e0) & m;
      std::vector<u64> c(G);
      for (u32 i = 0; i < t; i++) for (u32 s2 = 0; s2 < n; s2++) if (s2 & (1u << i)) c[s2] = (c[s2] - c[s2 ^ (1u << i)]) & m;
      u32 lin = X.cst((0 - c[0]) & m, w);
      for (u32 s2 = 1; s2 < n; s2++) {
        if (!c[s2]) continue;
        u32 term = 0;
        for (u32 i = 0; i < t; i++) if (s2 & (1u << i)) term = term ? X.and_(term, f.atoms[i]) : f.atoms[i];
        lin = X.add(lin, X.mul(term, X.cst(c[s2], w)));
      }
      consider(lin, "linear", f.exactLinear);
      u64 g0 = G[0], g1 = g0; bool two = true;
      for (u32 b = 0; b < n && two; b++) if (G[b] != g0) { if (g1 == g0) g1 = G[b]; else if (G[b] != g1) two = false; }
      if (two && g1 != g0 && t <= 4) {
        u16 tt = 0; for (u32 b = 0; b < n; b++) if (G[b] == g1) tt |= (u16)(1u << b);
        u32 F = boolExpr(X, (int)t, tt, f.atoms, w);
        consider(X.add(X.mul(F, X.cst((g1 - g0) & m, w)), X.cst((0 - g0) & m, w)), "boolean", f.exactLinear);
      }
      if (!best || bestSize > 3) { std::vector<u32> few; fewTerms(X, f, G, few); for (u32 c2 : few) consider(c2, "boolean-terms", f.exactLinear); }
      if (!f.bitConsts.empty() && !f.products) {
        std::vector<u64> pureOut; bool pure = false;
        u32 lc = linearConst(X, f, pureOut, pure);
        for (u64 pc : pureOut) consider((u32)pc, "boolean-const", false);
        consider(lc, "linear-const", false);
      }
    }
    if (synth && depthLimit == (1 << 30) && (!best || bestSize > 3) && (int)t <= o.synthAtoms && f.interiorCount >= 3)
      consider(synthesize(X, f, ck, o), "synth", false);
  }
  topExact = false;
  if (!best) return 0;
  if (o.exactOnly && !exact) return 0;
  if (!exact && o.proveMs && S) {
    std::vector<u64> model; SolveOptions so; so.timeoutMs = o.proveMs; so.localSearch = true; so.modular = false;
    SatResult r = S->check({}, {X.ne(e, best)}, std::vector<u64>(X.vars.size(), 0), &model, so);
    if (r == SR_SAT) return 0;
    if (r == SR_UNSAT) exact = true;
  }
  if (!strcmp(how, "linear") || !strcmp(how, "linear-const")) st.linear++; else if (!strncmp(how, "boolean", 7)) st.boolean++; else if (!strcmp(how, "constant")) st.constant++; else st.synth++;
  if (exact) st.proved++; else st.tested++;
  topExact = exact;
  return best;
}

// r and cand as functions of the atoms of r's MBA region (and of the nodes in `forced`): both linear MBAs with the same
// values at the corner points, hence the same function
bool Mba::proveLinear(u32 r, u32 cand, const std::unordered_set<u32>* forced) {
  Fn f; f.forced = forced;
  if (!f.build(X, r, 6) || !f.exactLinear) return false;
  Checker ck(X, f, 0);
  return ck.ok(cand) && ck.lastLinear;
}

// The whole expression as a black box over its input variables: the smallest expression with the same values on random
// inputs (then checked on many more). Independent of how the obfuscation nests: what MBA gets rewritten into does not matter.
u32 Mba::synthVars(u32 e) {
  std::vector<u32> vars; X.collectVars(e, vars);
  const unsigned w = X.W(e); const u64 m = maskOf(w);
  if (vars.empty() || vars.size() > (size_t)o.synthVarsMax) return 0;
  std::vector<u32> leaves;
  for (u32 v : vars) { u32 node = X.varNode(v); unsigned vw = X.vars[v].w; leaves.push_back(vw == w ? node : vw > w ? X.extract(node, 0, w) : X.zext(node, w)); }
  std::mt19937_64 rng(0x5eedull * (e + 1));
  const u64 special[] = {0, 1, 2, ~0ull, 0x8000000000000000ull, 0x7fffffffffffffffull, 0xffffffffull, 0x5555555555555555ull};
  std::vector<u64> vals(X.vars.size());
  for (size_t i = 0; i < vals.size(); i++) vals[i] = X.vars[i].seed;
  auto draw = [&](int k) { for (u32 v : vars) { u64 x = (k < 6 && rng() % 2) ? special[rng() % 8] : rng(); vals[v] = x & maskOf(X.vars[v].w); } };
  auto leafVal = [&](size_t i) { u32 v = vars[i]; unsigned vw = X.vars[v].w; return vals[v] & (vw >= w ? m : maskOf(vw)); };
  std::vector<std::vector<u64>> tests(K, std::vector<u64>(leaves.size())); std::vector<u64> want(K);
  for (int k = 0; k < K; k++) { draw(k); for (size_t i = 0; i < leaves.size(); i++) tests[k][i] = leafVal(i); want[k] = X.eval(e, vals.data()); }
  std::vector<u64> consts = {0, 1, 2, m};
  for (u32 v : vars) vals[v] = 0;
  const u64 e0 = X.eval(e, vals.data());
  if (std::find(consts.begin(), consts.end(), e0) == consts.end()) consts.push_back(e0);
  u32 r = synthesizeOver(X, leaves, consts, tests, want, w, leaves.size() <= 2 ? 6 : 4, 400000);
  if (!r) r = synthesizeMITM(X, leaves, consts, tests, want, w, leaves.size() <= 3 ? 3 : 2, 300000, o.mitmBudget);
  if (!r) return 0;
  // the same values on many more inputs
  for (int k = 0; k < 256; k++) { draw(k % 12); if (X.eval(e, vals.data()) != X.eval(r, vals.data())) return 0; }
  return r;
}

u32 Mba::simplifyOld(u32 root) {
  const double t0 = now();
  st.calls++;
  // the roots of the MBA regions: synthesis is tried there only
  std::unordered_set<u32> maximal{root};
  {
    std::unordered_set<u32> seen; std::vector<u32> todo{root};
    while (!todo.empty()) {
      u32 id = todo.back(); todo.pop_back();
      if (!seen.insert(id).second) continue;
      const Node& x = X.N(id);
      for (u32 c : {x.a, x.b, x.c}) if (c) { if (!interior(x.op)) maximal.insert(c); todo.push_back(c); }
    }
  }
  // bottom-up over the DAG (no recursion: expressions can be very deep)
  std::vector<std::pair<u32, int>> stk{{root, 0}};
  while (!stk.empty()) {
    auto& tp = stk.back(); u32 id = tp.first;
    if (memo.count(id)) { stk.pop_back(); continue; }
    const Node& x = X.N(id);
    u32 kids[3] = {x.a, x.b, x.c};
    if (tp.second < 3) { u32 c = kids[tp.second++]; if (c && !memo.count(c)) stk.push_back({c, 0}); continue; }
    stk.pop_back();
    const Node y = X.N(id);
    u32 r = id;
    if (y.op != O_CONST && y.op != O_VAR) {
      u32 a = y.a ? memo[y.a] : 0, b = y.b ? memo[y.b] : 0, c = y.c ? memo[y.c] : 0;
      if (a != y.a || b != y.b || c != y.c) r = X.make(y.op, y.w, y.lo, a, b, c, y.k);
    }
    if (X.sym(r) && interior(X.N(r).op) && now() - t0 < o.budget) { u32 t = top(r, maximal.count(id) != 0); if (t) r = t; }
    memo[id] = r;
  }
  u32 res = memo[root];
  // still big: the whole of it as a black box over its inputs
  if (o.synthVarsMax > 0 && X.sym(res) && X.countNodes(res) > 6 && now() - t0 < o.budget) {
    u32 r = synthVars(res);
    if (r && X.countNodes(r) < X.countNodes(res)) { res = r; st.synth++; st.tested++; memo[root] = res; }
  }
  st.t += now() - t0;
  return res;
}

u32 Mba::foldConditions(u32 root, Solver& S2) {
  const double t0 = now();
  SolveOptions so; so.smt = false; so.lsBudget = 400;
  std::unordered_map<u32, u32> done;
  std::vector<std::pair<u32, int>> stk{{root, 0}};
  std::vector<u64> seed(X.vars.size());
  for (size_t i = 0; i < seed.size(); i++) seed[i] = X.vars[i].seed;
  while (!stk.empty()) {
    auto& tp = stk.back(); u32 id = tp.first;
    if (done.count(id)) { stk.pop_back(); continue; }
    const Node& x = X.N(id);
    u32 kids[3] = {x.a, x.b, x.c};
    if (tp.second < 3) { u32 c = kids[tp.second++]; if (c && !done.count(c)) stk.push_back({c, 0}); continue; }
    stk.pop_back();
    const Node y = X.N(id);
    u32 r = id;
    if (y.op != O_CONST && y.op != O_VAR) {
      u32 a = y.a ? done[y.a] : 0, b = y.b ? done[y.b] : 0, c = y.c ? done[y.c] : 0;
      if (a != y.a || b != y.b || c != y.c) r = X.make(y.op, y.w, y.lo, a, b, c, y.k);
    }
    const Node z = X.N(r);
    bool cond = z.w == 1 && X.sym(r) && (z.op == O_EQ || z.op == O_ULT || z.op == O_ULE || z.op == O_SLT || z.op == O_SLE);
    if (cond && now() - t0 < o.budget) {
      if (S2.check({}, {r}, seed, nullptr, so) == SR_UNSAT) r = X.cst(0, 1);
      else if (S2.check({}, {X.not_(r)}, seed, nullptr, so) == SR_UNSAT) r = X.cst(1, 1);
    }
    done[id] = r;
  }
  return done[root];
}

}  // namespace unshroud
