// unshroud - proofs of MBA identities by polynomials. A bitwise function of whole values is a sum of conjunctions with integer
// coefficients (x | y = x + y - (x & y), ~x = -x - 1 ...); with every conjunction of two or more operands taken as an
// indeterminate, + - * make polynomials over them. Two expressions with the same polynomial are equal for every value
// (the converse does not hold: a proof, not a decision). Linear MBA identities, their products and their nestings are
// found equal. An operand of a bitwise operation is named by its own polynomial: two ways of writing one value are one
// operand, and a value and its complement are one operand with a polarity.
// A narrow computation extended with zeros is the low bits of the same computation on whole values: zext(e) is
// lift(e) & (2^k - 1), where lift(e) has e's operations done at full width (ids with VIRT set stand for lifted nodes).
#include "mba.hpp"
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <intrin.h>
#include <map>
#include <string>
#include <unordered_map>
#include <unordered_set>

namespace unshroud {
namespace {

typedef std::map<std::vector<u64>, u64> Poly;      // product of conjunctions (each a set of operands, sorted) -> coefficient; {}: the constant

struct Prover {
  enum : u32 { VIRT = 0x40000000u };
  enum Kind { K_ATOM, K_CONST, K_ADD, K_NEG, K_MUL, K_SHL, K_BIT, K_SAME };
  Ctx& X; unsigned w; u64 m; const std::unordered_set<u32>* forced;
  std::vector<u32> atoms; std::vector<Poly> atomPoly; std::unordered_map<u32, int> atomIdx;
  std::unordered_map<u32, Poly> memo;
  size_t work = 0; bool tooBig = false;
  Prover(Ctx& X, unsigned w, const std::unordered_set<u32>* forced) : X(X), w(w), m(maskOf(w)), forced(forced) {}

  static bool virt(u32 id) { return (id & VIRT) != 0; }
  const Node& N(u32 id) const { return X.N(id & ~VIRT); }
  static u32 kid(u32 id, u32 c) { return virt(id) && c ? (c | VIRT) : c; }
  Kind kind(u32 id) const {
    const Node& x = N(id);
    if (!virt(id)) {
      if ((forced && forced->count(id)) || x.w != w) return K_ATOM;
      switch (x.op) {
      case O_CONST: return K_CONST; case O_ADD: return K_ADD; case O_NEG: return K_NEG; case O_MUL: return K_MUL;
      case O_AND: case O_OR: case O_XOR: case O_NOT: return K_BIT;
      case O_ZEXT: return kind(x.a | VIRT) != K_ATOM ? K_BIT : K_ATOM;   // lift(x.a) & (2^k - 1), when something of it can be lifted
      default: return K_ATOM;
      }
    }
    switch (x.op) {
    case O_CONST: return K_CONST; case O_ADD: return K_ADD; case O_NEG: return K_NEG; case O_MUL: return K_MUL;
    case O_AND: case O_OR: case O_XOR: case O_NOT: return K_BIT;
    case O_EXTRACT: return x.lo == 0 && X.W(x.a) == w ? K_SAME : K_ATOM;     // the low bits of a whole value: that value
    case O_CONCAT: return X.isC(x.b) && X.cv(x.b) == 0 ? K_SHL : K_ATOM;       // zeros below: a shift to the left
    default: return K_ATOM;
    }
  }
  // a bitwise node as (operation, operands)
  void bitOp(u32 id, u8& op, u32& a, u32& b) {
    const Node x = N(id);
    if (!virt(id) && x.op == O_ZEXT) {
      // (a narrow value masked by a constant: that constant is the mask, one operand less)
      const Node y = X.N(x.a);
      op = O_AND;
      if (y.op == O_AND && X.isC(y.b)) { a = y.a | VIRT; b = X.cst(X.cv(y.b), w); }
      else { a = x.a | VIRT; b = X.cst(maskOf(x.lo), w); }
    }
    else { op = x.op; a = kid(id, x.a); b = x.op == O_NOT ? 0 : kid(id, x.b); }
  }

  int newAtom(u32 id, const Poly& p) {
    if (atoms.size() >= 64) { tooBig = true; return 0; }
    atoms.push_back(id); atomPoly.push_back(p);
    return (int)atoms.size() - 1;
  }
  int atomOf(u32 id) {                               // an indeterminate
    auto it = atomIdx.find(id);
    if (it != atomIdx.end()) return it->second;
    const int a = newAtom(id, Poly());
    if (!tooBig) atomPoly[a][{1ull << a}] = 1;
    atomIdx[id] = a;
    return a;
  }
  void addTerm(Poly& p, const std::vector<u64>& k, u64 c) { c &= m; if (!c) return; u64& v = p[k]; v = (v + c) & m; if (!v) p.erase(k); }
  void addScaled(Poly& p, const Poly& q, u64 c) { for (auto& kv : q) addTerm(p, kv.first, kv.second * c); }
  bool product(const Poly& a, const Poly& b, Poly& r) {
    if (a.size() * b.size() > 4000) return false;
    for (auto& ka : a) for (auto& kb : b) {
      std::vector<u64> k(ka.first.size() + kb.first.size());
      std::merge(ka.first.begin(), ka.first.end(), kb.first.begin(), kb.first.end(), k.begin());
      addTerm(r, k, ka.second * kb.second);
    }
    return true;
  }
  bool poly(u32 id, Poly& out);
  bool region(u32 root, Poly& out);

  // an operand of a bitwise operation, and its polarity
  struct Ref { int a; bool neg; };
  std::map<std::string, int> byPoly; std::unordered_map<u32, Ref> refs;
  static std::string keyOf(const Poly& p) {
    std::string key;
    for (auto& kv : p) { const u64 n = kv.first.size(); key.append((const char*)&n, 8); key.append((const char*)kv.first.data(), 8 * kv.first.size()); key.append((const char*)&kv.second, 8); }
    return key;
  }
  Ref refOf(u32 id) {
    auto it = refs.find(id);
    if (it != refs.end()) return it->second;
    Ref r{0, false};
    Poly p;
    if (kind(id) == K_ATOM) r = {atomOf(id), false};
    else if (!poly(id, p)) { tooBig = false; r = {atomOf(id), false}; }
    else {
      Poly q;                                          // the complement: -p - 1
      addScaled(q, p, m); addTerm(q, {}, m);
      auto single = [&](const Poly& t) -> int {        // one indeterminate by itself?
        if (t.size() != 1 || t.begin()->second != 1 || t.begin()->first.size() != 1) return -1;
        const u64 f = t.begin()->first[0]; if (f & (f - 1)) return -1;
        unsigned long i; _BitScanForward64(&i, f); return (int)i;
      };
      const std::string kp = keyOf(p), kq = keyOf(q);
      int a;
      if ((a = single(p)) >= 0) r = {a, false};
      else if ((a = single(q)) >= 0) r = {a, true};
      else if (byPoly.count(kp)) r = {byPoly[kp], false};
      else if (byPoly.count(kq)) r = {byPoly[kq], true};
      else if (kp <= kq) { a = newAtom(id, p); byPoly[kp] = a; r = {a, false}; }
      else { a = newAtom(id, q); byPoly[kq] = a; r = {a, true}; }
    }
    refs[id] = r;
    return r;
  }
};

bool Prover::poly(u32 id, Poly& out) {
  auto it = memo.find(id);
  if (it != memo.end()) { out = it->second; return true; }
  if (++work > 6000 || tooBig) return false;
  Poly r, a, b;
  const Node x = N(id);
  switch (kind(id)) {
  case K_ATOM: addTerm(r, {1ull << atomOf(id)}, 1); break;
  case K_CONST: addTerm(r, {}, x.k); break;
  case K_SAME: if (!poly(x.a, r)) return false; break;
  case K_ADD: if (!poly(kid(id, x.a), a) || !poly(kid(id, x.b), b)) return false; r = a; addScaled(r, b, 1); break;
  case K_NEG: if (!poly(kid(id, x.a), a)) return false; addScaled(r, a, m); break;
  case K_MUL: if (!poly(kid(id, x.a), a) || !poly(kid(id, x.b), b) || !product(a, b, r)) return false; break;
  case K_SHL: if (!poly(kid(id, x.a), a)) return false; addScaled(r, a, x.lo >= 64 ? 0 : 1ull << x.lo); break;
  case K_BIT: if (!region(id, r)) return false; break;
  }
  if (tooBig || r.size() > 3000) return false;
  memo[id] = r; out = r;
  return true;
}

// a bitwise region: its truth table over its operands, then the sum of conjunctions
bool Prover::region(u32 root, Poly& out) {
  std::vector<int> leafAtom; std::unordered_map<u32, u64> pat;     // the operands; node -> truth-table column
  std::vector<std::pair<u32, int>> st{{root, 0}}; std::vector<u32> order; std::unordered_set<u32> seen;
  static const u64 col[6] = {0xAAAAAAAAAAAAAAAAull, 0xCCCCCCCCCCCCCCCCull, 0xF0F0F0F0F0F0F0F0ull, 0xFF00FF00FF00FF00ull, 0xFFFF0000FFFF0000ull, 0xFFFFFFFF00000000ull};
  while (!st.empty()) {
    const u32 id = st.back().first;
    if (seen.count(id)) { st.pop_back(); continue; }
    const Kind kd = kind(id);
    const Node x = N(id);
    if (kd != K_BIT && kd != K_SAME) {
      seen.insert(id); st.pop_back();
      if (kd == K_CONST && (x.k == 0 || (!virt(id) && x.k == m))) { pat[id] = x.k ? ~0ull : 0; continue; }
      const Ref rf = refOf(id);
      if (tooBig) return false;
      size_t l = 0;
      for (; l < leafAtom.size(); l++) if (leafAtom[l] == rf.a) break;
      if (l == leafAtom.size()) { if (l >= 6) { addTerm(out, {1ull << atomOf(root)}, 1); return !tooBig; } leafAtom.push_back(rf.a); }
      pat[id] = rf.neg ? ~col[l] : col[l];
      continue;
    }
    u32 kids[2] = {0, 0};
    if (kd == K_SAME) kids[0] = x.a;
    else { u8 bop; bitOp(id, bop, kids[0], kids[1]); }
    if (st.back().second < 2) { const u32 c = kids[st.back().second++]; if (c && !seen.count(c)) st.push_back({c, 0}); continue; }
    seen.insert(id); order.push_back(id); st.pop_back();
  }
  for (u32 id : order) {
    if (kind(id) == K_SAME) { pat[id] = pat[N(id).a]; continue; }
    u8 bop; u32 ka, kb; bitOp(id, bop, ka, kb);
    const u64 a = pat[ka], b = kb ? pat[kb] : 0;
    pat[id] = bop == O_AND ? a & b : bop == O_OR ? a | b : bop == O_XOR ? a ^ b : ~a;
  }
  const int k = (int)leafAtom.size(), n = 1 << k;
  const u64 tt = pat[root];
  std::vector<i64> c(n);
  for (int s = 0; s < n; s++) c[s] = (tt >> s) & 1;
  for (int i = 0; i < k; i++) for (int s = 0; s < n; s++) if (s & (1 << i)) c[s] -= c[s ^ (1 << i)];
  addTerm(out, {}, (u64)(0 - c[0]));                                // the empty conjunction is -1
  for (int s = 1; s < n; s++) {
    if (!c[s]) continue;
    if ((s & (s - 1)) == 0) {                                       // one operand: what it is
      unsigned long i; _BitScanForward(&i, (unsigned long)s);
      addScaled(out, atomPoly[leafAtom[i]], (u64)c[s]);
    } else {
      u64 mask = 0; for (int i = 0; i < k; i++) if (s & (1 << i)) mask |= 1ull << leafAtom[i];
      addTerm(out, {mask}, (u64)c[s]);
    }
  }
  return !tooBig;
}

}  // namespace

bool Mba::provePoly(u32 r, u32 cand, const std::unordered_set<u32>* forced) {
  if (X.W(r) != X.W(cand) || X.n.size() >= Prover::VIRT) return false;
  struct Timer { double& t; std::chrono::steady_clock::time_point t0 = std::chrono::steady_clock::now(); ~Timer() { t += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(); } } timer{st.tPoly};
  Prover P(X, X.W(r), forced);
  Poly a, b;
  if (!P.poly(r, a) || !P.poly(cand, b)) return false;
  st.polyTried++;
  if (a != b && getenv("UNSHROUD_POLY_DEBUG") && X.countNodes(r) < 60) {
    auto show = [&](const char* nm, const Poly& q) {
      fprintf(stderr, "  %s:", nm);
      for (auto& kv : q) { fprintf(stderr, " %+lld", (long long)kv.second); for (u64 f : kv.first) { fprintf(stderr, "*["); for (int i = 0; i < 64; i++) if (f >> i & 1) fprintf(stderr, "a%d ", i); fprintf(stderr, "]"); } }
      fputc(10, stderr);
    };
    fprintf(stderr, "poly: %s%c   vs %s%c", X.str(r, 8).c_str(), 10, X.str(cand, 8).c_str(), 10);
    show("left", a); show("right", b);
    for (size_t i = 0; i < P.atoms.size(); i++) fprintf(stderr, "  a%zu = %s%s%c", i, (P.atoms[i] & Prover::VIRT) ? "lifted " : "", X.str(P.atoms[i] & ~Prover::VIRT, 5).c_str(), 10);
  }
  if (a != b) return false;
  st.polyProved++;
  return true;
}

}  // namespace unshroud
