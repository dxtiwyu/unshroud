// unshroud - expression DAG
#include "expr.hpp"
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <intrin.h>
#include <immintrin.h>
#include <random>
#include <unordered_map>

namespace unshroud {

const char* opName(u8 op) {
  static const char* names[] = {"none", "const", "var", "add", "mul", "udiv", "urem", "sdiv", "srem", "mulhu", "mulhs", "neg",
    "and", "or", "xor", "not", "shl", "lshr", "ashr", "rol", "ror", "extract", "zext", "sext", "concat", "ite",
    "eq", "ult", "ule", "slt", "sle", "popcnt", "clz", "ctz"};
  return op < O_COUNT ? names[op] : "?";
}

static inline unsigned msb64(u64 v) { unsigned long i; _BitScanReverse64(&i, v); return (unsigned)i; }
static inline unsigned lsb64(u64 v) { unsigned long i; _BitScanForward64(&i, v); return (unsigned)i; }

u64 evalOp(u8 op, unsigned w, unsigned lo, u64 k, u64 a, u64 b, u64 c) {
  const u64 m = maskOf(w);
  switch (op) {
  case O_CONST: return k;
  case O_ADD: return (a + b) & m;
  case O_MUL: return (a * b) & m;
  case O_UDIV: return b == 0 ? m : (a / b);
  case O_UREM: return b == 0 ? a : (a % b);
  case O_SDIV: {
    bool na = (a >> (w - 1)) & 1, nb = (b >> (w - 1)) & 1;
    u64 ua = na ? (0 - a) & m : a, ub = nb ? (0 - b) & m : b;
    u64 q = ub == 0 ? m : ua / ub;
    return (na != nb) ? (0 - q) & m : q;
  }
  case O_SREM: {
    bool na = (a >> (w - 1)) & 1, nb = (b >> (w - 1)) & 1;
    u64 ua = na ? (0 - a) & m : a, ub = nb ? (0 - b) & m : b;
    u64 r = ub == 0 ? ua : ua % ub;
    return na ? (0 - r) & m : r;
  }
  case O_MULHU: {
    u64 hi; u64 low = _umul128(a, b, &hi);
    if (w == 64) return hi;
    return ((low >> w) | (w ? (hi << (64 - w)) : 0)) & m;
  }
  case O_MULHS: {
    i64 hi; u64 low = (u64)_mul128(sx(a, w), sx(b, w), &hi);
    if (w == 64) return (u64)hi;
    return ((low >> w) | ((u64)hi << (64 - w))) & m;
  }
  case O_NEG: return (0 - a) & m;
  case O_AND: return a & b;
  case O_OR: return a | b;
  case O_XOR: return a ^ b;
  case O_NOT: return (~a) & m;
  case O_SHL: return b >= w ? 0 : (a << b) & m;
  case O_LSHR: return b >= w ? 0 : a >> b;
  case O_ASHR: { unsigned s = b >= w ? w - 1 : (unsigned)b; return (u64)(sx(a, w) >> s) & m; }
  case O_ROL: { unsigned r = (unsigned)(b % w); return r == 0 ? a : ((a << r) | (a >> (w - r))) & m; }
  case O_ROR: { unsigned r = (unsigned)(b % w); return r == 0 ? a : ((a >> r) | (a << (w - r))) & m; }
  case O_EXTRACT: return (a >> lo) & m;
  case O_ZEXT: return a;
  case O_SEXT: return (u64)sx(a, lo) & m;
  case O_CONCAT: return ((a << lo) | b) & m;
  case O_ITE: return (a & 1) ? b : c;
  case O_EQ: return a == b;
  case O_ULT: return a < b;
  case O_ULE: return a <= b;
  case O_SLT: return sx(a, lo) < sx(b, lo);
  case O_SLE: return sx(a, lo) <= sx(b, lo);
  case O_POPCNT: return (u64)__popcnt64(a);
  case O_CLZ: return a == 0 ? lo : (lo - 1 - msb64(a));
  case O_CTZ: return a == 0 ? lo : lsb64(a);
  default: return 0;
  }
}

static inline u32 hashNode(u8 op, u8 w, u8 lo, u32 a, u32 b, u32 c, u64 k) {
  u64 h = (u64)op | ((u64)w << 8) | ((u64)lo << 16);
  h ^= (u64)a * 0x9E3779B97F4A7C15ull; h = (h ^ (h >> 29)) * 0xBF58476D1CE4E5B9ull;
  h ^= (u64)b | ((u64)c << 32); h = (h ^ (h >> 32)) * 0x94D049BB133111EBull;
  h ^= k; h = (h ^ (h >> 29)) * 0xBF58476D1CE4E5B9ull; h ^= h >> 32;
  return (u32)h;
}

Ctx::Ctx() {
  n.reserve(1 << 16);
  Node z{}; n.push_back(z);
  table.assign(1 << 16, 0); tmask = (1 << 16) - 1; tcount = 0;
  extractMemo.assign(1 << 16, EMC{0, 0, 0});
  if (const char* ro = getenv("UNSHROUD_RULES_OFF")) off = (u32)atoi(ro);
  if (const char* e = getenv("UNSHROUD_LAZYDEPTH")) lazyDepth = (unsigned)atoi(e);
  const char* ck = getenv("UNSHROUD_CHECK");
  check = ck && *ck && *ck != '0';
}

void Ctx::grow() {
  std::vector<u64> t2((size_t)(tmask + 1) * 2, 0);
  u32 m2 = (tmask + 1) * 2 - 1;
  for (u64 e : table) if (e) { u32 i = (u32)(e >> 32) & m2; while (t2[i]) i = (i + 1) & m2; t2[i] = e; }
  table.swap(t2); tmask = m2;
}

void Ctx::tableInsert(u32 h, u32 id) {
  u32 i = h & tmask;
  while (table[i]) i = (i + 1) & tmask;
  table[i] = ((u64)h << 32) | id;
  if (++tcount * 2 > tmask) grow();
}

u32 Ctx::lookupOrAdd(const Node& x) {
  lookups++;
  // looked up lately (the usual case when a trace computes the same things again): one probe of a small table
  const u64 hk = (u64)x.h << 32;
  u64& fr = front[(x.h ^ (x.h >> 12)) & 4095];
  if ((fr & 0xffffffff00000000ull) == hk) {
    const u32 id = (u32)fr; const Node& y = n[id];
    if (y.op == x.op && y.w == x.w && y.lo == x.lo && y.a == x.a && y.b == x.b && y.c == x.c && y.k == x.k) return id;
  }
  const u32 size = (u32)n.size();
  // among the recent nodes (not in the table yet)
  {
    const __m256i hv = _mm256_set1_epi32((int)x.h);
    for (u32 k = 0; k < NURSERY; k += 8) {
      u32 m = (u32)_mm256_movemask_ps(_mm256_castsi256_ps(_mm256_cmpeq_epi32(hv, _mm256_loadu_si256((const __m256i*)(ringHash + k)))));
      while (m) {
        unsigned long b; _BitScanForward(&b, m); m &= m - 1;
        const u32 slot = k + b;
        if (slot >= ringCount) continue;
        const Node& y = n[ringId[slot]];
        if (y.op == x.op && y.w == x.w && y.lo == x.lo && y.a == x.a && y.b == x.b && y.c == x.c && y.k == x.k) { fr = hk | ringId[slot]; return ringId[slot]; }
      }
    }
  }
  // in the table - unless an operand is recent: a node made of it is recent too
  const u32 newest = x.a > x.b ? (x.a > x.c ? x.a : x.c) : (x.b > x.c ? x.b : x.c);
  if (!(newest && newest + ringCount >= size)) {
    u32 i = x.h & tmask;
    while (u64 e = table[i]) {
      if ((e & 0xffffffff00000000ull) == hk) {          // the node is looked at only when the hash matches
        u32 id = (u32)e;
        const Node& y = n[id];
        if (y.op == x.op && y.w == x.w && y.lo == x.lo && y.a == x.a && y.b == x.b && y.c == x.c && y.k == x.k) { fr = e; return id; }
      }
      i = (i + 1) & tmask;
    }
  }
  const u32 id = size;
  fr = hk | id;
  if (id >= maxNodes) overBudget = true;
  n.push_back(x);
  _mm_prefetch((const char*)&table[x.h & tmask], _MM_HINT_T0);
  // the oldest of the ring goes to the table, the new node takes its place
  if (ringCount == NURSERY) { tableInsert(ringHash[ringPos], ringId[ringPos]); }
  else ringCount++;
  ringHash[ringPos] = x.h; ringId[ringPos] = id;
  ringPos = (ringPos + 1) % NURSERY;
  return id;
}

u32 Ctx::raw(u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c, u64 k) {
  Node x;
  x.op = op; x.w = (u8)w; x.lo = (u8)lo; x.a = a; x.b = b; x.c = c; x.k = k;
  x.flags = (u8)((op == O_VAR ? F_SYM : 0) | (op == O_ITE ? F_ITE : 0) | (a ? n[a].flags : 0) | (b ? n[b].flags : 0) | (c ? n[c].flags : 0));
  u64 s = 1 + (a ? n[a].size : 0) + (b ? n[b].size : 0) + (c ? n[c].size : 0);
  x.size = s > 0x7fffffff ? 0x7fffffff : (u32)s;
  x.h = hashNode(op, (u8)w, (u8)lo, a, b, c, k);
  return lookupOrAdd(x);
}

u32 Ctx::plain(u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c, u64 k) {
  if ((!a || isC(a)) && (!b || isC(b)) && (!c || isC(c)) && op != O_VAR) return cst(evalOp(op, w, lo, k, a ? cv(a) : 0, b ? cv(b) : 0, c ? cv(c) : 0), w);
  return raw(op, w, lo, a, b, c, k);
}

u32 Ctx::cst(u64 v, unsigned w) { if (lazyOn) return deferConst(v, w); return raw(O_CONST, w, 0, 0, 0, 0, v & maskOf(w)); }

u32 Ctx::var(const std::string& name, unsigned w, u64 seed) {
  u32 index = (u32)vars.size();
  vars.push_back({name, (u8)w, seed & maskOf(w)});
  u32 id = raw(O_VAR, w, 0, 0, 0, 0, index);
  varIds.push_back(id);
  return id;
}

u64 Ctx::eval(u32 root, const u64* vals) {
  newGen();
  // iterative post-order
  std::vector<u32> st; st.push_back(root);
  while (!st.empty()) {
    u32 id = st.back();
    if (stamp[id] == gen) { st.pop_back(); continue; }
    const Node& x = n[id];
    if (x.op == O_CONST) { memo[id] = x.k; stamp[id] = gen; st.pop_back(); continue; }
    if (x.op == O_VAR) { memo[id] = vals[x.k] & maskOf(x.w); stamp[id] = gen; st.pop_back(); continue; }
    bool ready = true;
    if (x.a && stamp[x.a] != gen) { st.push_back(x.a); ready = false; }
    if (x.b && stamp[x.b] != gen) { st.push_back(x.b); ready = false; }
    if (x.c && stamp[x.c] != gen) { st.push_back(x.c); ready = false; }
    if (!ready) continue;
    memo[id] = evalOp(x.op, x.w, x.lo, x.k, x.a ? memo[x.a] : 0, x.b ? memo[x.b] : 0, x.c ? memo[x.c] : 0);
    stamp[id] = gen; st.pop_back();
  }
  return memo[root];
}

u64 Ctx::evalSeed(u32 id) {
  std::vector<u64> v(vars.size());
  for (size_t i = 0; i < vars.size(); i++) v[i] = vars[i].seed;
  return eval(id, v.data());
}

u32 Ctx::countNodes(u32 root) {
  newGen();
  u32 count = 0; std::vector<u32> st{root};
  while (!st.empty()) {
    u32 id = st.back(); st.pop_back();
    if (!id || stamp[id] == gen) continue;
    stamp[id] = gen; count++;
    const Node& x = n[id];
    if (x.a) st.push_back(x.a);
    if (x.b) st.push_back(x.b);
    if (x.c) st.push_back(x.c);
  }
  return count;
}

void Ctx::collectVars(u32 root, std::vector<u32>& out) {
  newGen();
  std::vector<u32> st{root};
  while (!st.empty()) {
    u32 id = st.back(); st.pop_back();
    if (!id || stamp[id] == gen || !(n[id].flags & F_SYM)) continue;
    stamp[id] = gen;
    const Node& x = n[id];
    if (x.op == O_VAR) { out.push_back((u32)x.k); continue; }
    if (x.a) st.push_back(x.a);
    if (x.b) st.push_back(x.b);
    if (x.c) st.push_back(x.c);
  }
  std::sort(out.begin(), out.end());
  out.erase(std::unique(out.begin(), out.end()), out.end());
}

// ------------------------------------------------------------------------------------------------ checking
u32 Ctx::checkedSlow(u32 r, u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c, u64 k) {
  static std::mt19937_64 rng(12345);
  std::vector<u64> v(vars.size());
  for (int round = 0; round < 3; round++) {
    for (size_t i = 0; i < vars.size(); i++) {
      u64 x = rng();
      int kind = (int)(rng() % 6);
      if (kind == 0) x = 0; else if (kind == 1) x = ~0ull; else if (kind == 2) x &= 0xff; else if (kind == 3) x = vars[i].seed;
      v[i] = x & maskOf(vars[i].w);
    }
    u64 va = a ? eval(a, v.data()) : 0, vb = b ? eval(b, v.data()) : 0, vc = c ? eval(c, v.data()) : 0;
    u64 want = evalOp(op, w, lo, k, va, vb, vc) & maskOf(w);
    u64 got = eval(r, v.data());
    checks++;
    if (want != got || n[r].w != w) {
      fprintf(stderr, "UNSHROUD_CHECK: %s w=%u lo=%u: want %llx got %llx (width %u)\n  a=%s\n  b=%s\n  c=%s\n  r=%s\n", opName(op), w, lo,
              (unsigned long long)want, (unsigned long long)got, n[r].w, a ? str(a).c_str() : "-", b ? str(b).c_str() : "-", c ? str(c).c_str() : "-", str(r).c_str());
      abort();
    }
  }
  return r;
}

// ------------------------------------------------------------------------------------------------ linear forms
namespace {
struct LTerm { u32 t; u64 c; };
struct LForm {
  LTerm t[16]; int n = 0; u64 k = 0; bool full = false; int merged = 0;
  void addTerm(u32 e, u64 c, u64 m) {
    for (int i = 0; i < n; i++) if (t[i].t == e) { t[i].c = (t[i].c + c) & m; merged++; return; }
    if (n == 16) { full = true; return; }
    t[n++] = {e, c & m};
  }
};
}

static void gatherLinear(const Ctx& X, u32 e, u64 coef, u64 m, LForm& f, int depth) {
  const Node& x = X.N(e);
  if (x.op == O_CONST) { f.k = (f.k + coef * x.k) & m; return; }
  if (depth < 10) {
    if (x.op == O_ADD) { gatherLinear(X, x.a, coef, m, f, depth + 1); gatherLinear(X, x.b, coef, m, f, depth + 1); return; }
    if (x.op == O_NEG) { gatherLinear(X, x.a, (0 - coef) & m, m, f, depth + 1); return; }
    if (x.op == O_MUL && X.isC(x.b)) { gatherLinear(X, x.a, (coef * X.cv(x.b)) & m, m, f, depth + 1); return; }
  }
  f.addTerm(e, coef, m);
}

// a*ca + b*cb, normalized
u32 Ctx::linear(u32 a, u64 ca, u32 b, u64 cb, unsigned w) {
  const u64 m = maskOf(w);
  if (off & 8) {
    u32 x = ca == 1 ? a : (ca == m ? raw(O_NEG, w, 0, a, 0, 0, 0) : raw(O_MUL, w, 0, a, cst(ca, w), 0, 0));
    if (!b) return x;
    u32 y = cb == 1 ? b : (cb == m ? raw(O_NEG, w, 0, b, 0, 0, 0) : raw(O_MUL, w, 0, b, cst(cb, w), 0, 0));
    return raw(O_ADD, w, 0, x, y, 0, 0);
  }
  LForm f;
  gatherLinear(*this, a, ca, m, f, 0);
  if (b) gatherLinear(*this, b, cb, m, f, 0);
  if (f.full) {
    // too many terms: a plain node (constants are not moved)
    u32 x = ca == 1 ? a : (ca == m ? raw(O_NEG, w, 0, a, 0, 0, 0) : raw(O_MUL, w, 0, a, cst(ca, w), 0, 0));
    if (!b) return x;
    u32 y = cb == 1 ? b : (cb == m ? raw(O_NEG, w, 0, b, 0, 0, 0) : raw(O_MUL, w, 0, b, cst(cb, w), 0, 0));
    return raw(O_ADD, w, 0, std::min(x, y), std::max(x, y), 0, 0);
  }
  // a - d*(a/d) = a % d (also on the low bits: [a]_w - d*[a/d]_w = [a % d]_w)
  bool rem = false;
  for (int i = 0; i < f.n && !rem; i++) {
    if (f.t[i].c != 1) continue;
    for (int j = 0; j < f.n; j++) {
      if (j == i || !f.t[j].c) continue;
      const u64 d = (0 - f.t[j].c) & m;
      const Node& tj = n[f.t[j].t]; const Node& ti = n[f.t[i].t];
      u32 A = 0; bool low = false;
      if (tj.op == O_UDIV && isC(tj.b) && cv(tj.b) == d && tj.a == f.t[i].t) A = tj.a;
      else if (tj.op == O_EXTRACT && tj.lo == 0 && ti.op == O_EXTRACT && ti.lo == 0 && n[tj.a].op == O_UDIV && isC(n[tj.a].b) &&
               ((cv(n[tj.a].b) - d) & m) == 0 && n[tj.a].a == ti.a && n[n[tj.a].a].w == n[tj.a].w) { A = ti.a; low = true; }
      u32 r = 0;
      if (A) r = low ? extract(urem(A, n[n[f.t[j].t].a].b), 0, w) : urem(A, tj.b);
      else {
        // y/c1 - d * (y/(c1*d)) = (y/c1) % d: the second quotient is the first one divided again (written as one division)
        const u32 qi = ti.op == O_EXTRACT && ti.lo == 0 ? ti.a : f.t[i].t, qj = tj.op == O_EXTRACT && tj.lo == 0 ? tj.a : f.t[j].t;
        const bool lowi = qi != f.t[i].t, lowj = qj != f.t[j].t;
        const Node& ni = n[qi]; const Node& nj = n[qj];
        if (lowi == lowj && ni.op == O_UDIV && nj.op == O_UDIV && ni.a == nj.a && isC(ni.b) && isC(nj.b) && ni.w == nj.w && cv(ni.b) > 1 && cv(nj.b) % cv(ni.b) == 0) {
          const u64 dq = cv(nj.b) / cv(ni.b);
          if (dq > 1 && ((dq - d) & m) == 0) { const u32 u = urem(qi, cst(dq, ni.w)); r = lowi ? extract(u, 0, w) : u; }
        }
      }
      if (!r) continue;
      f.t[i].t = r; f.t[j].c = 0; rem = true; f.merged++;
      break;
    }
  }
  // nothing merged or cancelled: a new node over the operands as they are (keeps the sharing of long sums)
  if (!f.merged && (b || f.n > 4)) {
    auto core = [&](u32 e, u64& k) -> u32 { const Node& x = n[e]; if (x.op == O_ADD && isC(x.b)) { k = cv(x.b); return x.a; } if (x.op == O_CONST) { k = x.k; return 0; } k = 0; return e; };
    u64 ka, kb; u32 xa = core(a, ka), xb = core(b, kb);
    auto scaled = [&](u32 e, u64 c) -> u32 { if (!e) return 0; return c == 1 ? e : c == m ? raw(O_NEG, w, 0, e, 0, 0, 0) : raw(O_MUL, w, 0, e, cst(c, w), 0, 0); };
    u32 pa = scaled(xa, ca), pb = scaled(xb, cb);
    u32 acc = pa && pb ? raw(O_ADD, w, 0, std::min(pa, pb), std::max(pa, pb), 0, 0) : (pa ? pa : pb);
    u64 k = (ka * ca + kb * cb) & m;
    if (k) acc = acc ? raw(O_ADD, w, 0, acc, cst(k, w), 0, 0) : cst(k, w);
    return acc ? acc : cst(0, w);
  }
  // drop zero coefficients, sort by id
  int k = 0;
  for (int i = 0; i < f.n; i++) if (f.t[i].c) f.t[k++] = f.t[i];
  f.n = k;
  std::sort(f.t, f.t + f.n, [](const LTerm& x, const LTerm& y) { return x.t < y.t; });
  u32 acc = 0;
  for (int i = 0; i < f.n; i++) {
    u32 t = f.t[i].t; u64 c = f.t[i].c;
    u32 piece = c == 1 ? t : (c == m ? raw(O_NEG, w, 0, t, 0, 0, 0) : raw(O_MUL, w, 0, t, cst(c, w), 0, 0));
    acc = acc ? raw(O_ADD, w, 0, acc, piece, 0, 0) : piece;
  }
  if (f.k) acc = acc ? raw(O_ADD, w, 0, acc, cst(f.k, w), 0, 0) : cst(f.k, w);
  return acc ? acc : cst(0, w);
}

u32 Ctx::add(u32 a, u32 b) {
  if (lazyOn) return defer(O_ADD, W(a), 0, a, b, 0);
  if (norules) return plain(O_ADD, W(a), 0, a, b, 0, 0);
  unsigned w = W(a);
  if (isC(a) && isC(b)) return cst(cv(a) + cv(b), w);
  return checked(linear(a, 1, b, 1, w), O_ADD, w, 0, a, b, 0, 0);
}

u32 Ctx::sub(u32 a, u32 b) {
  if (lazyOn) return defer(O_SUBL, W(a), 0, a, b, 0);
  if (norules) return plain(O_ADD, W(a), 0, a, plain(O_NEG, W(b), 0, b, 0, 0, 0), 0, 0);
  unsigned w = W(a);
  if (isC(a) && isC(b)) return cst(cv(a) - cv(b), w);
  u32 r = linear(a, 1, b, maskOf(w), w);
  if (check) { u32 nb = raw(O_NEG, w, 0, b, 0, 0, 0); return checked(r, O_ADD, w, 0, a, nb, 0, 0); }
  return r;
}

u32 Ctx::neg(u32 a) {
  if (lazyOn) return defer(O_NEG, W(a), 0, a, 0, 0);
  if (norules) return plain(O_NEG, W(a), 0, a, 0, 0, 0);
  unsigned w = W(a);
  if (isC(a)) return cst(0 - cv(a), w);
  return checked(linear(a, maskOf(w), 0, 0, w), O_NEG, w, 0, a, 0, 0, 0);
}

// an expression with the same bit 0 as e, without the additions and products at its top (e itself when there are none)
u32 Ctx::bit0(u32 e, int& budget) {
  const Node x = N(e);
  if (--budget < 0) return e;
  if (x.op == O_CONST) return cst(x.k & 1, x.w);
  if (x.op == O_NEG) return bit0(x.a, budget);
  if (x.op == O_ADD) return xor_(bit0(x.a, budget), bit0(x.b, budget));
  if (x.op == O_MUL) return and_(bit0(x.a, budget), bit0(x.b, budget));
  return e;
}

u32 Ctx::mul(u32 a, u32 b) {
  if (lazyOn) return defer(O_MUL, W(a), 0, a, b, 0);
  if (norules) return plain(O_MUL, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); const u64 m = maskOf(w);
  if (isC(a) && isC(b)) return cst(cv(a) * cv(b), w);
  if (isC(a)) std::swap(a, b);
  u32 r;
  if (isC(b)) {
    u64 c = cv(b);
    if (c == 0) r = cst(0, w);
    else if (c == 1) r = a;
    else {
      // kept as a product (distributing c over a sum gives the SMT solver one multiplier per term); constants merge
      const Node y = N(a);
      if (y.op == O_MUL && isC(y.b)) r = mul(y.a, cst(cv(y.b) * c, w));
      // the top bit alone: only bit 0 of the other operand counts, and bit 0 of a sum is the XOR of the terms', of a
      // product the AND of the factors' (2^(w-1) * t * (t + 1) vanishes this way)
      else if (w > 1 && c == (1ull << (w - 1)) && (y.op == O_MUL || y.op == O_ADD)) { int budget = 48; const u32 p = bit0(a, budget); r = p == a ? raw(O_MUL, w, 0, a, b, 0, 0) : mul(p, b); }
      else if (y.op == O_NEG) r = mul(y.a, cst(0 - c, w));
      else if (y.op == O_ADD && isC(y.b)) r = add(mul(y.a, b), cst(cv(y.b) * c, w));     // (t + k) * c = t*c + k*c: the constant stays outside
      else r = raw(O_MUL, w, 0, a, b, 0, 0);
    }
  } else {
    // constants float out of products: (x*c)*y = (x*y)*c, (-x)*y = -(x*y)
    const Node x = N(a), y = N(b);
    if (x.op == O_MUL && isC(x.b)) r = mul(mul(x.a, b), x.b);
    else if (y.op == O_MUL && isC(y.b)) r = mul(mul(a, y.a), y.b);
    else if (x.op == O_NEG) r = neg(mul(x.a, b));
    else if (y.op == O_NEG) r = neg(mul(a, y.a));
    else r = raw(O_MUL, w, 0, std::min(a, b), std::max(a, b), 0, 0);
  }
  (void)m;
  return checked(r, O_MUL, w, 0, a, b, 0, 0);
}

static bool isPow2(u64 v) { return v && !(v & (v - 1)); }
static unsigned log2u(u64 v) { unsigned long i; _BitScanForward64(&i, v); return (unsigned)i; }
static u64 inverseOdd(u64 a, unsigned w) {
  u64 x = a;                            // Newton: x = x*(2 - a*x), 6 rounds give 64 bits
  for (int i = 0; i < 6; i++) x *= 2 - a * x;
  return x & maskOf(w);
}

u32 Ctx::udiv(u32 a, u32 b) {
  if (lazyOn) return defer(O_UDIV, W(a), 0, a, b, 0);
  if (norules) return plain(O_UDIV, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(a) && isC(b)) r = cst(evalOp(O_UDIV, w, 0, 0, cv(a), cv(b), 0), w);
  else if (isC(b) && cv(b) == 1) r = a;
  else if (isC(b) && isPow2(cv(b))) r = lshr(a, cst(log2u(cv(b)), w));
  else if (isC(a) && cv(a) == 0 && !isC(b)) r = raw(O_UDIV, w, 0, a, b, 0, 0);
  else {
    r = 0;
    if (isC(b) && cv(b) > 1 && !(off & 1)) {
      // (y / c1) / c2 = y / (c1 * c2), (y >> k) / c = y / (c << k): one division of the value itself (0 if the divisor is past the width)
      const u64 d = cv(b), m = maskOf(w); const Node x = N(a);
      u32 y = 0; u64 c1 = 0;
      if (x.op == O_UDIV && isC(x.b) && cv(x.b) > 1) { y = x.a; c1 = cv(x.b); }
      else if (x.op == O_ZEXT && N(x.a).op == O_EXTRACT && W(N(x.a).a) == w && N(x.a).lo + N(x.a).w == w && N(x.a).lo > 0 && N(x.a).lo < 64) { y = N(x.a).a; c1 = 1ull << N(x.a).lo; }
      if (y) { u64 hi; const u64 lo = _umul128(c1, d, &hi); r = (hi || lo > m) ? cst(0, w) : udiv(y, cst(lo, w)); }
    }
    if (!r) r = raw(O_UDIV, w, 0, a, b, 0, 0);
  }
  return checked(r, O_UDIV, w, 0, a, b, 0, 0);
}

u32 Ctx::urem(u32 a, u32 b) {
  if (lazyOn) return defer(O_UREM, W(a), 0, a, b, 0);
  if (norules) return plain(O_UREM, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(a) && isC(b)) r = cst(evalOp(O_UREM, w, 0, 0, cv(a), cv(b), 0), w);
  else if (isC(b) && cv(b) == 1) r = cst(0, w);
  else if (isC(b) && isPow2(cv(b))) r = and_(a, cst(cv(b) - 1, w));
  else r = raw(O_UREM, w, 0, a, b, 0, 0);
  return checked(r, O_UREM, w, 0, a, b, 0, 0);
}

u32 Ctx::sdiv(u32 a, u32 b) {
  if (lazyOn) return defer(O_SDIV, W(a), 0, a, b, 0);
  if (norules) return plain(O_SDIV, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(a) && isC(b)) r = cst(evalOp(O_SDIV, w, 0, 0, cv(a), cv(b), 0), w);
  else if (isC(b) && cv(b) == 1) r = a;
  else r = raw(O_SDIV, w, 0, a, b, 0, 0);
  return checked(r, O_SDIV, w, 0, a, b, 0, 0);
}

u32 Ctx::srem(u32 a, u32 b) {
  if (lazyOn) return defer(O_SREM, W(a), 0, a, b, 0);
  if (norules) return plain(O_SREM, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(a) && isC(b)) r = cst(evalOp(O_SREM, w, 0, 0, cv(a), cv(b), 0), w);
  else if (isC(b) && cv(b) == 1) r = cst(0, w);
  else r = raw(O_SREM, w, 0, a, b, 0, 0);
  return checked(r, O_SREM, w, 0, a, b, 0, 0);
}

u32 Ctx::mulhu(u32 a, u32 b) {
  if (lazyOn) return defer(O_MULHU, W(a), 0, a, b, 0);
  if (norules) return plain(O_MULHU, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(a)) std::swap(a, b);
  if (isC(a) && isC(b)) r = cst(evalOp(O_MULHU, w, 0, 0, cv(a), cv(b), 0), w);
  else if (isC(b) && (cv(b) == 0 || cv(b) == 1)) r = cst(0, w);
  else if (isC(b) && isPow2(cv(b))) r = lshr(a, cst(w - log2u(cv(b)), w));
  else r = raw(O_MULHU, w, 0, isC(b) ? a : std::min(a, b), isC(b) ? b : std::max(a, b), 0, 0);
  return checked(r, O_MULHU, w, 0, a, b, 0, 0);
}

u32 Ctx::mulhs(u32 a, u32 b) {
  if (lazyOn) return defer(O_MULHS, W(a), 0, a, b, 0);
  if (norules) return plain(O_MULHS, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(a)) std::swap(a, b);
  if (isC(a) && isC(b)) r = cst(evalOp(O_MULHS, w, 0, 0, cv(a), cv(b), 0), w);
  else if (isC(b) && cv(b) == 0) r = cst(0, w);
  else if (isC(b) && cv(b) == 1 && w > 1) r = ashr(a, cst(w - 1, w));
  else r = raw(O_MULHS, w, 0, isC(b) ? a : std::min(a, b), isC(b) ? b : std::max(a, b), 0, 0);
  return checked(r, O_MULHS, w, 0, a, b, 0, 0);
}

// ------------------------------------------------------------------------------------------------ bitwise chains
namespace {
struct BForm { u32 t[12]; int n = 0; u64 k; bool full = false; int merged = 0; };
}

static void gatherBits(const Ctx& X, u8 op, u32 e, u64 m, BForm& f, int depth) {
  const Node& x = X.N(e);
  if (x.op == O_CONST) {
    if (op == O_AND) f.k &= x.k; else if (op == O_OR) f.k |= x.k; else f.k ^= x.k;
    return;
  }
  if (depth < 6) {
    if (x.op == op) { gatherBits(X, op, x.a, m, f, depth + 1); gatherBits(X, op, x.b, m, f, depth + 1); return; }
    if (op == O_XOR && x.op == O_NOT) { f.k ^= m; gatherBits(X, op, x.a, m, f, depth + 1); return; }
  }
  for (int i = 0; i < f.n; i++) {
    if (f.t[i] == e) {
      f.merged++;
      if (op == O_XOR) { f.t[i] = f.t[--f.n]; }          // x ^ x = 0
      return;                                            // x & x = x, x | x = x
    }
  }
  if (f.n == 12) { f.full = true; return; }
  f.t[f.n++] = e;
}

u32 Ctx::andOr(u8 op, u32 a, u32 b, unsigned w) {
  const u64 m = maskOf(w);
  if (off & 32) return raw(op, w, 0, a, b, 0, 0);
  BForm f; f.k = op == O_AND ? m : 0;
  gatherBits(*this, op, a, m, f, 0);
  gatherBits(*this, op, b, m, f, 0);
  if (f.full) return raw(op, w, 0, std::min(a, b), std::max(a, b), 0, 0);
  const u64 absorb = op == O_AND ? 0 : m, ident = op == O_AND ? m : 0;
  if (f.k == absorb) return cst(absorb, w);
  bool absorbedAny = false;
  // x & ~x = 0, x | ~x = -1; absorption: x & (x | y) = x, x | (x & y) = x
  for (int i = 0; i < f.n; i++) {
    const Node& x = N(f.t[i]);
    for (int j = 0; j < f.n; j++) {
      if (i == j) continue;
      if (x.op == O_NOT && x.a == f.t[j]) return cst(absorb, w);
    }
  }
  for (int i = 0; i < f.n; i++) {
    const Node& x = N(f.t[i]);
    u8 dual = op == O_AND ? O_OR : O_AND;
    if (x.op == dual) {
      bool absorbed = false;
      for (int j = 0; j < f.n && !absorbed; j++) if (j != i && (x.a == f.t[j] || x.b == f.t[j])) absorbed = true;
      if (absorbed) { f.t[i] = f.t[--f.n]; i = -1; absorbedAny = true; continue; }
    }
  }
  if (!f.merged && !absorbedAny && f.n > 2) {
    auto core = [&](u32 e, u64& k) -> u32 {
      const Node& x = n[e];
      if (x.op == op && isC(x.b)) { k = cv(x.b); return x.a; }
      if (x.op == O_CONST) { k = x.k; return 0; }
      k = ident; return e;
    };
    u64 ka, kb; u32 xa = core(a, ka), xb = core(b, kb);
    u32 acc = xa && xb ? raw(op, w, 0, std::min(xa, xb), std::max(xa, xb), 0, 0) : (xa ? xa : xb);
    u64 k = op == O_AND ? (ka & kb) : (ka | kb);
    if (!acc) return cst(k, w);
    return k != ident ? raw(op, w, 0, acc, cst(k, w), 0, 0) : acc;
  }
  std::sort(f.t, f.t + f.n);
  u32 acc = 0;
  for (int i = 0; i < f.n; i++) acc = acc ? raw(op, w, 0, acc, f.t[i], 0, 0) : f.t[i];
  if (!acc) return cst(f.k, w);
  if (f.k != ident) {
    // x & lowmask: the low bits of x
    if (op == O_AND && f.n == 1 && ((f.k + 1) & f.k) == 0) {
      unsigned bits = f.k == 0 ? 0 : 64 - (unsigned)__lzcnt64(f.k);
      return zext(extract(acc, 0, bits), w);
    }
    acc = raw(op, w, 0, acc, cst(f.k, w), 0, 0);
  }
  return acc;
}

u32 Ctx::and_(u32 a, u32 b) {
  if (lazyOn) return defer(O_AND, W(a), 0, a, b, 0);
  if (norules) return plain(O_AND, W(a), 0, a, b, 0, 0);
  unsigned w = W(a);
  if (isC(a) && isC(b)) return cst(cv(a) & cv(b), w);
  if (!(off & 64) && N(a).op == O_NOT && N(b).op == O_NOT && a != b) return checked(not_(or_(N(a).a, N(b).a)), O_AND, w, 0, a, b, 0, 0);   // ~p & ~q = ~(p | q)
  return checked(andOr(O_AND, a, b, w), O_AND, w, 0, a, b, 0, 0);
}

u32 Ctx::or_(u32 a, u32 b) {
  if (lazyOn) return defer(O_OR, W(a), 0, a, b, 0);
  if (norules) return plain(O_OR, W(a), 0, a, b, 0, 0);
  unsigned w = W(a);
  if (isC(a) && isC(b)) return cst(cv(a) | cv(b), w);
  if (!(off & 64) && N(a).op == O_NOT && N(b).op == O_NOT && a != b) return checked(not_(and_(N(a).a, N(b).a)), O_OR, w, 0, a, b, 0, 0);   // ~p | ~q = ~(p & q)
  return checked(andOr(O_OR, a, b, w), O_OR, w, 0, a, b, 0, 0);
}

u32 Ctx::xorChain(u32 a, u32 b, unsigned w) {
  const u64 m = maskOf(w);
  if (off & 32) return b ? raw(O_XOR, w, 0, a, b, 0, 0) : raw(O_NOT, w, 0, a, 0, 0, 0);
  BForm f; f.k = 0;
  gatherBits(*this, O_XOR, a, m, f, 0);
  if (b) gatherBits(*this, O_XOR, b, m, f, 0);
  if (f.full) return b ? raw(O_XOR, w, 0, std::min(a, b), std::max(a, b), 0, 0) : raw(O_NOT, w, 0, a, 0, 0, 0);
  if (!f.merged && b && f.n > 2) {
    // nothing cancelled: the operands as they are, the constant outside
    auto core = [&](u32 e, u64& k) -> u32 {
      const Node& x = n[e];
      if (x.op == O_XOR && isC(x.b)) { k = cv(x.b); return x.a; }
      if (x.op == O_NOT) { k = m; return x.a; }
      if (x.op == O_CONST) { k = x.k; return 0; }
      k = 0; return e;
    };
    u64 ka, kb; u32 xa = core(a, ka), xb = core(b, kb);
    u32 acc = xa && xb ? raw(O_XOR, w, 0, std::min(xa, xb), std::max(xa, xb), 0, 0) : (xa ? xa : xb);
    u64 k = ka ^ kb;
    if (!acc) return cst(k, w);
    if (k == m) return raw(O_NOT, w, 0, acc, 0, 0, 0);
    return k ? raw(O_XOR, w, 0, acc, cst(k, w), 0, 0) : acc;
  }
  std::sort(f.t, f.t + f.n);
  u32 acc = 0;
  for (int i = 0; i < f.n; i++) acc = acc ? raw(O_XOR, w, 0, acc, f.t[i], 0, 0) : f.t[i];
  if (!acc) return cst(f.k, w);
  if (f.k == m) return raw(O_NOT, w, 0, acc, 0, 0, 0);
  if (f.k) return raw(O_XOR, w, 0, acc, cst(f.k, w), 0, 0);
  return acc;
}

u32 Ctx::xor_(u32 a, u32 b) {
  if (lazyOn) return defer(O_XOR, W(a), 0, a, b, 0);
  if (norules) return plain(O_XOR, W(a), 0, a, b, 0, 0);
  unsigned w = W(a);
  if (isC(a) && isC(b)) return cst(cv(a) ^ cv(b), w);
  return checked(xorChain(a, b, w), O_XOR, w, 0, a, b, 0, 0);
}

u32 Ctx::not_(u32 a) {
  if (lazyOn) return defer(O_NOT, W(a), 0, a, 0, 0);
  if (norules) return plain(O_NOT, W(a), 0, a, 0, 0, 0);
  unsigned w = W(a); u32 r;
  const Node x = N(a);
  if (x.op == O_CONST) return cst(~x.k, w);
  if (x.op == O_NOT) r = x.a;
  else if (w == 1 && x.op == O_ULT) r = ule(x.b, x.a);          // !(a < b) = b <= a
  else if (w == 1 && x.op == O_ULE) r = ult(x.b, x.a);
  else if (w == 1 && x.op == O_SLT) r = sle(x.b, x.a);
  else if (w == 1 && x.op == O_SLE) r = slt(x.b, x.a);
  // De Morgan: ~(~p & ~q) = p | q, ~(~p | ~q) = p & q (NOR/NAND compositions)
  else if (!(off & 64) && (x.op == O_AND || x.op == O_OR) && N(x.a).op == O_NOT && N(x.b).op == O_NOT)
    r = x.op == O_AND ? or_(N(x.a).a, N(x.b).a) : and_(N(x.a).a, N(x.b).a);
  else r = xorChain(a, cst(maskOf(w), w), w);
  return checked(r, O_NOT, w, 0, a, 0, 0, 0);
}

// ------------------------------------------------------------------------------------------------ shifts and rotations
u32 Ctx::shl(u32 a, u32 b) {
  if (lazyOn) return defer(O_SHL, W(a), 0, a, b, 0);
  if (norules) return plain(O_SHL, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(b)) {
    u64 s = cv(b);
    if (s >= w) r = cst(0, w);
    else if (s == 0) r = a;
    else r = mul(a, cst(1ull << s, w));
  } else r = raw(O_SHL, w, 0, a, b, 0, 0);
  return checked(r, O_SHL, w, 0, a, b, 0, 0);
}

u32 Ctx::lshr(u32 a, u32 b) {
  if (lazyOn) return defer(O_LSHR, W(a), 0, a, b, 0);
  if (norules) return plain(O_LSHR, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(a) && isC(b)) return cst(evalOp(O_LSHR, w, 0, 0, cv(a), cv(b), 0), w);
  if (isC(b)) {
    u64 s = cv(b);
    if (s >= w) r = cst(0, w);
    else if (s == 0) r = a;
    else r = zext(extract(a, (unsigned)s, w - (unsigned)s), w);
  } else r = raw(O_LSHR, w, 0, a, b, 0, 0);
  return checked(r, O_LSHR, w, 0, a, b, 0, 0);
}

u32 Ctx::ashr(u32 a, u32 b) {
  if (lazyOn) return defer(O_ASHR, W(a), 0, a, b, 0);
  if (norules) return plain(O_ASHR, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(a) && isC(b)) return cst(evalOp(O_ASHR, w, 0, 0, cv(a), cv(b), 0), w);
  if (isC(b)) {
    u64 s = cv(b);
    if (s >= w) s = w - 1;
    if (s == 0) r = a;
    else r = sext(extract(a, (unsigned)s, w - (unsigned)s), w);
  } else r = raw(O_ASHR, w, 0, a, b, 0, 0);
  return checked(r, O_ASHR, w, 0, a, b, 0, 0);
}

u32 Ctx::rol(u32 a, u32 b) {
  if (lazyOn) return defer(O_ROL, W(a), 0, a, b, 0);
  if (norules) return plain(O_ROL, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(a) && isC(b)) return cst(evalOp(O_ROL, w, 0, 0, cv(a), cv(b), 0), w);
  if (isC(b)) {
    unsigned s = (unsigned)(cv(b) % w);
    const Node x = N(a);
    if (s == 0) r = a;
    else if (w == 1) r = a;
    else if (x.op == O_ROL && isC(x.b)) r = rol(x.a, cst((cv(x.b) + s) % w, w));
    else r = raw(O_ROL, w, 0, a, cst(s, w), 0, 0);
  } else r = raw(O_ROL, w, 0, a, b, 0, 0);
  return checked(r, O_ROL, w, 0, a, b, 0, 0);
}

u32 Ctx::ror(u32 a, u32 b) {
  if (lazyOn) return defer(O_ROR, W(a), 0, a, b, 0);
  if (norules) return plain(O_ROR, W(a), 0, a, b, 0, 0);
  unsigned w = W(a); u32 r;
  if (isC(a) && isC(b)) return cst(evalOp(O_ROR, w, 0, 0, cv(a), cv(b), 0), w);
  if (isC(b)) r = rol(a, cst((w - cv(b) % w) % w, w));
  else r = raw(O_ROR, w, 0, a, b, 0, 0);
  return checked(r, O_ROR, w, 0, a, b, 0, 0);
}

// ------------------------------------------------------------------------------------------------ structure
u32 Ctx::extract(u32 a, unsigned lo, unsigned w) {
  if (lazyOn) { if (lo == 0 && w == W(a)) return a; return defer(O_EXTRACT, w, lo, a, 0, 0); }
  if (norules) { if (lo == 0 && w == W(a)) return a; return plain(O_EXTRACT, w, lo, a, 0, 0, 0); }
  const unsigned wa = W(a);
  if (lo == 0 && w == wa) return a;
  if (lo + w > wa || w == 0) { fprintf(stderr, "unshroud: bad extract %u:%u of %u bits\n", lo, w, wa); abort(); }
  const Node x = N(a);
  if (x.op == O_CONST) return cst(x.k >> lo, w);
  if (off & 128) return raw(O_EXTRACT, w, lo, a, 0, 0, 0);
  const u64 key = ((u64)a << 16) | (lo << 8) | w;
  EMC& slot = extractMemo[(u32)((key * 0x9E3779B97F4A7C15ull) >> 48)];
  if (slot.key == key) return slot.val;
  u32 r = 0;
  bool deep = ++extractDepth > 40;
  // pushing the extract into an operation copies its operands at the new width: only into small ones
  const bool small = !(off & 2) && (x.size <= 48 || (x.a && isC(x.a)) || (x.b && isC(x.b)));
  switch (x.op) {
  case O_EXTRACT: r = extract(x.a, x.lo + lo, w); break;
  case O_CONCAT: {
    unsigned wl = x.lo;
    if (lo + w <= wl) r = extract(x.b, lo, w);
    else if (lo >= wl) r = extract(x.a, lo - wl, w);
    else r = concat(extract(x.a, 0, lo + w - wl), extract(x.b, lo, wl - lo));
    break;
  }
  case O_ZEXT: {
    unsigned wx = x.lo;
    if (lo + w <= wx) r = extract(x.a, lo, w);
    else if (lo >= wx) r = cst(0, w);
    else r = zext(extract(x.a, lo, wx - lo), w);
    break;
  }
  case O_SEXT: {
    unsigned wx = x.lo;
    if (lo + w <= wx) r = extract(x.a, lo, w);
    else if (lo >= wx - 1) r = sext(extract(x.a, wx - 1, 1), w);
    else r = sext(extract(x.a, lo, wx - lo), w);
    break;
  }
  case O_AND: if (!deep && small) r = and_(extract(x.a, lo, w), extract(x.b, lo, w)); break;
  case O_OR: if (!deep && small) r = or_(extract(x.a, lo, w), extract(x.b, lo, w)); break;
  case O_XOR: if (!deep && small) r = xor_(extract(x.a, lo, w), extract(x.b, lo, w)); break;
  case O_NOT: if (!deep && small) r = not_(extract(x.a, lo, w)); break;
  case O_ITE: {
    // bits which are the same in every arm (a table whose entries are all even...)
    const Known kn = known(a);
    if ((((kn.zeros | kn.ones) >> lo) & maskOf(w)) == maskOf(w)) { r = cst(kn.ones >> lo, w); break; }
    // a tree of selections among constants keeps its shape with narrower constants
    auto leafy = [&](u32 e) { const u8 o = n[e].op; return o == O_CONST || o == O_ITE; };
    if (!deep && (small || (leafy(x.b) && leafy(x.c)))) r = ite(x.a, extract(x.b, lo, w), extract(x.c, lo, w));
    break;
  }
  case O_ADD: if (!deep && small && lo == 0) r = add(extract(x.a, 0, w), extract(x.b, 0, w)); break;
  case O_NEG: if (!deep && small && lo == 0) r = neg(extract(x.a, 0, w)); break;
  case O_MUL:
    if (isC(x.b) && isPow2(cv(x.b))) {
      unsigned s = log2u(cv(x.b));
      if (lo >= s) r = extract(x.a, lo - s, w);
      else if (lo + w <= s) r = cst(0, w);
      else r = concat(extract(x.a, 0, lo + w - s), cst(0, s - lo));
    } else if (!deep && lo >= 32 && isC(x.b) && n[x.a].op == O_ZEXT && n[x.a].lo <= 32) {
      // (zext(y) * M) >> (N + s): a division of y by a constant
      unsigned N = n[x.a].lo; u64 hi; _umul128(maskOf(N), cv(x.b), &hi);
      if (!hi && lo >= N) { u32 q = magicDiv(n[x.a].a, cv(x.b), N, lo - N); if (q) r = extract(zext(q, wa), 0, w); }
    }
    if (!r && !deep && small && lo == 0) r = mul(extract(x.a, 0, w), extract(x.b, 0, w));
    break;
  case O_MULHU:
    if (isC(x.b)) { u32 q = magicDiv(x.a, cv(x.b), wa, lo); if (q) r = (lo + w <= wa) ? extract(q, 0, w) : 0; }
    break;
  case O_UDIV:
    // (y / d) >> lo = y / (d << lo)
    if (lo > 0 && lo + w == wa && isC(x.b) && cv(x.b) > 1 && !(off & 1)) {
      const u64 d = cv(x.b);
      r = (lo >= 64 || d > (maskOf(wa) >> lo)) ? cst(0, w) : extract(udiv(x.a, cst(d << lo, wa)), 0, w);
    }
    break;
  case O_ROL:
    if (isC(x.b)) {
      unsigned s = (unsigned)cv(x.b), start = (lo + wa - s) % wa;
      if (start + w <= wa) r = extract(x.a, start, w);
      else r = concat(extract(x.a, 0, w - (wa - start)), extract(x.a, start, wa - start));
    }
    break;
  default: break;
  }
  extractDepth--;
  if (!r) r = raw(O_EXTRACT, w, lo, a, 0, 0, 0);
  r = checked(r, O_EXTRACT, w, lo, a, 0, 0, 0);
  { EMC& sl = extractMemo[(u32)((key * 0x9E3779B97F4A7C15ull) >> 48)]; sl.key = key; sl.val = r; }
  return r;
}

u32 Ctx::zext(u32 a, unsigned w) {
  if (lazyOn) { if (w == W(a)) return a; return defer(O_ZEXT, w, W(a), a, 0, 0); }
  if (norules) { if (w == W(a)) return a; return plain(O_ZEXT, w, W(a), a, 0, 0, 0); }
  const unsigned wa = W(a);
  if (w == wa) return a;
  const Node x = N(a);
  if (x.op == O_CONST) return cst(x.k, w);
  if (x.op == O_ZEXT) return zext(x.a, w);
  // zext(low k bits of b) == b when b fits in k bits
  if (x.op == O_EXTRACT && x.lo == 0 && W(x.a) == w && range(x.a).hi <= maskOf(wa)) return checked(x.a, O_ZEXT, w, wa, a, 0, 0, 0);
  return checked(raw(O_ZEXT, w, wa, a, 0, 0, 0), O_ZEXT, w, wa, a, 0, 0, 0);
}

u32 Ctx::sext(u32 a, unsigned w) {
  if (lazyOn) { if (w == W(a)) return a; return defer(O_SEXT, w, W(a), a, 0, 0); }
  if (norules) { if (w == W(a)) return a; return plain(O_SEXT, w, W(a), a, 0, 0, 0); }
  const unsigned wa = W(a);
  if (w == wa) return a;
  const Node x = N(a);
  u32 r;
  if (x.op == O_CONST) return cst((u64)sx(x.k, wa), w);
  if (x.op == O_SEXT) r = sext(x.a, w);
  else if (x.op == O_ZEXT) r = zext(a, w);          // the sign bit of zext(x) (wider than x) is 0
  else r = raw(O_SEXT, w, wa, a, 0, 0, 0);
  return checked(r, O_SEXT, w, wa, a, 0, 0, 0);
}

u32 Ctx::concat(u32 hi, u32 lo) {
  if (lazyOn) return defer(O_CONCAT, W(hi) + W(lo), W(lo), hi, lo, 0);
  if (norules) return plain(O_CONCAT, W(hi) + W(lo), W(lo), hi, lo, 0, 0);
  const unsigned wh = W(hi), wl = W(lo), w = wh + wl;
  if (w > 64) { fprintf(stderr, "unshroud: concat wider than 64 bits\n"); abort(); }
  const Node h = N(hi), l = N(lo);
  u32 r = 0;
  if (h.op == O_CONST && l.op == O_CONST) return cst((h.k << wl) | l.k, w);
  if (off & 128) return raw(O_CONCAT, w, wl, hi, lo, 0, 0);
  if (h.op == O_CONST && h.k == 0) r = zext(lo, w);
  else if (h.op == O_EXTRACT && l.op == O_EXTRACT && h.a == l.a && h.lo == l.lo + l.w) r = extract(h.a, l.lo, w);
  else if (h.op == O_EXTRACT && l.op == O_CONCAT && N(l.a).op == O_EXTRACT && N(l.a).a == h.a && h.lo == N(l.a).lo + N(l.a).w) {
    const Node l2 = N(l.a);
    r = concat(extract(h.a, l2.lo, wh + l2.w), l.b);
  } else if (h.op == O_CONCAT) r = concat(h.a, concat(h.b, lo));
  else r = raw(O_CONCAT, w, wl, hi, lo, 0, 0);
  return checked(r, O_CONCAT, w, wl, hi, lo, 0, 0);
}

u32 Ctx::ite(u32 c, u32 t, u32 f) {
  if (lazyOn) return defer(O_ITE, W(t), 0, c, t, f);
  if (norules) { if (isC(c)) return cv(c) ? t : f; return raw(O_ITE, W(t), 0, c, t, f, 0); }
  const unsigned w = W(t);
  if (isC(c)) return cv(c) ? t : f;
  if (t == f) return t;
  const Node x = N(c);
  u32 r;
  if (x.op == O_NOT) r = ite(x.a, f, t);
  else if (w == 1 && isC(t) && isC(f)) r = cv(t) ? c : not_(c);
  else if (w == 1 && isC(t)) r = cv(t) ? or_(c, f) : and_(not_(c), f);
  else if (w == 1 && isC(f)) r = cv(f) ? or_(not_(c), t) : and_(c, t);
  else if (N(t).op == O_ITE && N(t).a == c) r = ite(c, N(t).b, f);
  else if (N(f).op == O_ITE && N(f).a == c) r = ite(c, t, N(f).c);
  else r = raw(O_ITE, w, 0, c, t, f, 0);
  return checked(r, O_ITE, w, 0, c, t, f, 0);
}

// ------------------------------------------------------------------------------------------------ comparisons
// y / d compared with a constant is y compared with a multiple of d
static bool quotient(const Ctx& X, u32 e, u32& y, u64& d) {
  const Node& x = X.N(e);
  if (x.op != O_UDIV || !X.isC(x.b) || X.cv(x.b) < 2) return false;
  y = x.a; d = X.cv(x.b); return true;
}
// c * d within the width? (the product in p)
static bool mulFits(u64 c, u64 d, u64 m, u64& p) { u64 hi; p = _umul128(c, d, &hi); return !hi && p <= m; }

// a == c (a not constant): invertible operations around a variable are peeled off
u32 Ctx::eqConst(u32 a, u64 c) {
  const unsigned w = W(a); const u64 m = maskOf(w);
  const Node x = N(a);
  if (w == 1) return c ? a : not_(a);
  if (off & 16) return raw(O_EQ, 1, w, a, cst(c, w), 0, 0);
  switch (x.op) {
  case O_ADD: if (isC(x.b)) return eq(x.a, cst(c - cv(x.b), w)); break;
  case O_XOR: if (isC(x.b)) return eq(x.a, cst(c ^ cv(x.b), w)); break;
  case O_NOT: return eq(x.a, cst(~c, w));
  case O_NEG: return eq(x.a, cst(0 - c, w));
  case O_MUL:
    if (x.a == x.b && c) {
      // a square is 4^k times an odd number which is 1 modulo 8
      const unsigned tz = log2u(c & (0 - c)); const u64 odd = c >> tz; const unsigned bits = w - tz;
      if ((tz & 1) || (bits >= 3 && (odd & 7) != 1) || (bits == 2 && (odd & 3) != 1)) return cst(0, 1);
    }
    if (isC(x.b)) {
      u64 k = cv(x.b);
      if (k & 1) return eq(x.a, cst(c * inverseOdd(k, w), w));
      unsigned s = log2u(k);
      if (c & maskOf(s)) return cst(0, 1);
      return eq(extract(mul(x.a, cst(k >> s, w)), 0, w - s), cst(c >> s, w - s));
    }
    break;
  case O_ZEXT: { unsigned wx = x.lo; if (wx < 64 && (c >> wx)) return cst(0, 1); return eq(x.a, cst(c, wx)); }
  case O_SEXT: {
    unsigned wx = x.lo; u64 lowc = c & maskOf(wx);
    if (((u64)sx(lowc, wx) & m) != c) return cst(0, 1);
    return eq(x.a, cst(lowc, wx));
  }
  case O_CONCAT: { unsigned wl = x.lo; return and_(eq(x.a, cst(c >> wl, w - wl)), eq(x.b, cst(c & maskOf(wl), wl))); }
  case O_ROL: if (isC(x.b)) return eq(x.a, cst(evalOp(O_ROR, w, 0, 0, c, cv(x.b), 0), w)); break;
  case O_ITE:
    if (isC(x.b) && isC(x.c)) {
      bool t = cv(x.b) == c, f = cv(x.c) == c;
      return t && f ? cst(1, 1) : t ? x.a : f ? not_(x.a) : cst(0, 1);
    }
    break;
  case O_UDIV:
    if (isC(x.b) && cv(x.b) > 1 && !(off & 1)) {        // y / d == c: c*d <= y <= c*d + d - 1
      const u64 d = cv(x.b); u64 lo, hi;
      if (!mulFits(c, d, m, lo)) return cst(0, 1);
      const bool top = !(c < m && mulFits(c + 1, d, m, hi));
      return top ? ule(cst(lo, w), x.a) : and_(ule(cst(lo, w), x.a), ult(x.a, cst(hi, w)));
    }
    break;
  case O_EXTRACT:                                         // the low part of a value which fits in it
    if (x.lo == 0 && range(x.a).hi <= m) return eq(x.a, cst(c, W(x.a)));
    break;
  case O_AND: if (isC(x.b) && (c & ~cv(x.b))) return cst(0, 1); break;
  case O_OR: if (isC(x.b) && ((c & cv(x.b)) != cv(x.b))) return cst(0, 1); break;
  default: break;
  }
  { Range ra = range(a); if (c < ra.lo || c > ra.hi) return cst(0, 1); }
  return raw(O_EQ, 1, w, a, cst(c, w), 0, 0);
}

u32 Ctx::eq(u32 a, u32 b) {
  if (lazyOn) return defer(O_EQ, 1, W(a), a, b, 0);
  if (norules) return plain(O_EQ, 1, W(a), a, b, 0, 0);
  const unsigned w = W(a);
  if (isC(a) && isC(b)) return cst(cv(a) == cv(b), 1);
  if (a == b) return cst(1, 1);
  if (isC(a)) std::swap(a, b);
  u32 r;
  if (isC(b)) r = eqConst(a, cv(b));
  else {
    // the difference may be a constant, or one term
    u32 d = sub(a, b);
    if (isC(d)) r = cst(cv(d) == 0, 1);
    else {
      LForm f; gatherLinear(*this, d, 1, maskOf(w), f, 0);
      int live = 0, at = -1;
      for (int i = 0; i < f.n; i++) if (f.t[i].c) { live++; at = i; }
      if (!f.full && live == 1 && (f.t[at].c == 1 || f.t[at].c == maskOf(w)))
        r = eqConst(f.t[at].t, f.t[at].c == 1 ? (0 - f.k) & maskOf(w) : f.k);
      else { Range ra = range(a), rb = range(b);
        r = (ra.hi < rb.lo || rb.hi < ra.lo) ? cst(0, 1) : raw(O_EQ, 1, w, std::min(a, b), std::max(a, b), 0, 0); }
    }
  }
  return checked(r, O_EQ, 1, w, a, b, 0, 0);
}

u32 Ctx::ult(u32 a, u32 b) {
  if (lazyOn) return defer(O_ULT, 1, W(a), a, b, 0);
  if (norules) return plain(O_ULT, 1, W(a), a, b, 0, 0);
  const unsigned w = W(a); const u64 m = maskOf(w);
  u32 r;
  if (isC(a) && isC(b)) return cst(cv(a) < cv(b), 1);
  if (a == b) r = cst(0, 1);
  else if (isC(b) && cv(b) == 0) r = cst(0, 1);
  else if (isC(a) && cv(a) == m) r = cst(0, 1);
  else if (isC(b) && cv(b) == 1) r = eq(a, cst(0, w));
  else if (isC(a) && cv(a) == 0) r = not_(eq(b, cst(0, w)));
  else if (isC(b) && cv(b) == m) r = not_(eq(a, cst(m, w)));
  else if (isC(b) && N(a).op == O_ZEXT && cv(b) > maskOf(N(a).lo)) r = cst(1, 1);
  else if (w == 1) r = and_(not_(a), b);
  else {
    r = 0;
    u32 y; u64 d, p;
    if (!(off & 1) && isC(b) && quotient(*this, a, y, d)) r = mulFits(cv(b), d, m, p) ? ult(y, cst(p, w)) : cst(1, 1);                      // y/d < c: y < c*d
    else if (!(off & 1) && isC(a) && quotient(*this, b, y, d)) r = cv(a) < m && mulFits(cv(a) + 1, d, m, p) ? ule(cst(p, w), y) : cst(0, 1);   // c < y/d: (c+1)*d <= y
    if (!r) { Range ra = range(a), rb = range(b);
      if (ra.hi < rb.lo) r = cst(1, 1); else if (ra.lo >= rb.hi) r = cst(0, 1); else r = raw(O_ULT, 1, w, a, b, 0, 0); }
  }
  return checked(r, O_ULT, 1, w, a, b, 0, 0);
}

u32 Ctx::ule(u32 a, u32 b) {
  if (lazyOn) return defer(O_ULE, 1, W(a), a, b, 0);
  if (norules) return plain(O_ULE, 1, W(a), a, b, 0, 0);
  const unsigned w = W(a); const u64 m = maskOf(w);
  u32 r;
  if (isC(a) && isC(b)) return cst(cv(a) <= cv(b), 1);
  if (a == b) r = cst(1, 1);
  else if (isC(a) && cv(a) == 0) r = cst(1, 1);
  else if (isC(b) && cv(b) == m) r = cst(1, 1);
  else if (isC(b) && cv(b) == 0) r = eq(a, cst(0, w));
  else if (isC(a) && cv(a) == m) r = eq(b, cst(m, w));
  else if (isC(b) && N(a).op == O_ZEXT && cv(b) >= maskOf(N(a).lo)) r = cst(1, 1);
  else if (w == 1) r = or_(not_(a), b);
  else {
    r = 0;
    u32 y; u64 d, p;
    if (!(off & 1) && isC(b) && quotient(*this, a, y, d)) r = cv(b) < m && mulFits(cv(b) + 1, d, m, p) ? ult(y, cst(p, w)) : cst(1, 1);    // y/d <= c: y < (c+1)*d
    else if (!(off & 1) && isC(a) && quotient(*this, b, y, d)) r = mulFits(cv(a), d, m, p) ? ule(cst(p, w), y) : cst(0, 1);                // c <= y/d: c*d <= y
    if (!r) { Range ra = range(a), rb = range(b);
      if (ra.hi <= rb.lo) r = cst(1, 1); else if (ra.lo > rb.hi) r = cst(0, 1); else r = raw(O_ULE, 1, w, a, b, 0, 0); }
  }
  return checked(r, O_ULE, 1, w, a, b, 0, 0);
}

u32 Ctx::slt(u32 a, u32 b) {
  if (lazyOn) return defer(O_SLT, 1, W(a), a, b, 0);
  if (norules) return plain(O_SLT, 1, W(a), a, b, 0, 0);
  const unsigned w = W(a);
  const u64 smin = signBit(w), smax = maskOf(w) >> 1;
  u32 r;
  if (isC(a) && isC(b)) return cst(sx(cv(a), w) < sx(cv(b), w), 1);
  if (a == b) r = cst(0, 1);
  else if (isC(b) && cv(b) == smin) r = cst(0, 1);
  else if (isC(a) && cv(a) == smax) r = cst(0, 1);
  else if (isC(b) && cv(b) == 0) r = extract(a, w - 1, 1);              // x < 0: the sign bit
  else if (w == 1) r = and_(a, not_(b));
  else { Range ra = range(a), rb = range(b);
    if (ra.hi <= smax && rb.hi <= smax) r = ult(a, b); else r = raw(O_SLT, 1, w, a, b, 0, 0); }
  return checked(r, O_SLT, 1, w, a, b, 0, 0);
}

u32 Ctx::sle(u32 a, u32 b) {
  if (lazyOn) return defer(O_SLE, 1, W(a), a, b, 0);
  if (norules) return plain(O_SLE, 1, W(a), a, b, 0, 0);
  const unsigned w = W(a);
  const u64 smin = signBit(w), smax = maskOf(w) >> 1;
  u32 r;
  if (isC(a) && isC(b)) return cst(sx(cv(a), w) <= sx(cv(b), w), 1);
  if (a == b) r = cst(1, 1);
  else if (isC(a) && cv(a) == smin) r = cst(1, 1);
  else if (isC(b) && cv(b) == smax) r = cst(1, 1);
  else if (isC(b) && cv(b) == maskOf(w)) r = extract(a, w - 1, 1);      // x <= -1: the sign bit
  else if (w == 1) r = or_(a, not_(b));
  else { Range ra = range(a), rb = range(b);
    if (ra.hi <= smax && rb.hi <= smax) r = ule(a, b); else r = raw(O_SLE, 1, w, a, b, 0, 0); }
  return checked(r, O_SLE, 1, w, a, b, 0, 0);
}

u32 Ctx::popcnt(u32 a) { unsigned w = W(a); if (lazyOn) return defer(O_POPCNT, w, w, a, 0, 0); if (isC(a)) return cst(evalOp(O_POPCNT, w, w, 0, cv(a), 0, 0), w); return raw(O_POPCNT, w, w, a, 0, 0, 0); }
u32 Ctx::clz(u32 a) { unsigned w = W(a); if (lazyOn) return defer(O_CLZ, w, w, a, 0, 0); if (isC(a)) return cst(evalOp(O_CLZ, w, w, 0, cv(a), 0, 0), w); return raw(O_CLZ, w, w, a, 0, 0, 0); }
u32 Ctx::ctz(u32 a) { unsigned w = W(a); if (lazyOn) return defer(O_CTZ, w, w, a, 0, 0); if (isC(a)) return cst(evalOp(O_CTZ, w, w, 0, cv(a), 0, 0), w); return raw(O_CTZ, w, w, a, 0, 0, 0); }

u32 Ctx::make(u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c, u64 k) {
  if (lazyOn) return op == O_CONST ? deferConst(k, w) : defer(op, w, lo, a, b, c);
  switch (op) {
  case O_CONST: return cst(k, w);
  case O_ADD: return add(a, b);
  case O_MUL: return mul(a, b);
  case O_UDIV: return udiv(a, b);
  case O_UREM: return urem(a, b);
  case O_SDIV: return sdiv(a, b);
  case O_SREM: return srem(a, b);
  case O_MULHU: return mulhu(a, b);
  case O_MULHS: return mulhs(a, b);
  case O_NEG: return neg(a);
  case O_AND: return and_(a, b);
  case O_OR: return or_(a, b);
  case O_XOR: return xor_(a, b);
  case O_NOT: return not_(a);
  case O_SHL: return shl(a, b);
  case O_LSHR: return lshr(a, b);
  case O_ASHR: return ashr(a, b);
  case O_ROL: return rol(a, b);
  case O_ROR: return ror(a, b);
  case O_EXTRACT: return extract(a, lo, w);
  case O_ZEXT: return zext(a, w);
  case O_SEXT: return sext(a, w);
  case O_CONCAT: return concat(a, b);
  case O_ITE: return ite(a, b, c);
  case O_EQ: return eq(a, b);
  case O_ULT: return ult(a, b);
  case O_ULE: return ule(a, b);
  case O_SLT: return slt(a, b);
  case O_SLE: return sle(a, b);
  case O_POPCNT: return popcnt(a);
  case O_CLZ: return clz(a);
  case O_CTZ: return ctz(a);
  default: return raw(op, w, lo, a, b, c, k);
  }
}

// ------------------------------------------------------------------------------------------------ printing
std::string Ctx::str(u32 id, int depth) const {
  if (!id) return "<none>";
  const Node& x = n[id];
  char buf[96];
  if (x.op == O_CONST) {
    if (x.w == 1) return x.k ? "true" : "false";
    u64 m = maskOf(x.w);
    if (x.k > (m >> 1) && x.k != m && ((0 - x.k) & m) < 0x100000) { snprintf(buf, sizeof buf, "-0x%llx", (unsigned long long)((0 - x.k) & m)); return buf; }
    snprintf(buf, sizeof buf, "0x%llx", (unsigned long long)x.k); return buf;
  }
  if (x.op == O_VAR) return vars[x.k].name;
  if (depth <= 0) return "...";
  auto s = [&](u32 c) { return str(c, depth - 1); };
  auto bin = [&](const char* o) { return "(" + s(x.a) + " " + o + " " + s(x.b) + ")"; };
  switch (x.op) {
  case O_ADD:
    if (n[x.b].op == O_NEG) return "(" + s(x.a) + " - " + s(n[x.b].a) + ")";
    return bin("+");
  case O_MUL: return bin("*");
  case O_UDIV: return bin("/u");
  case O_UREM: return bin("%u");
  case O_SDIV: return bin("/s");
  case O_SREM: return bin("%s");
  case O_MULHU: return "mulhu(" + s(x.a) + ", " + s(x.b) + ")";
  case O_MULHS: return "mulhs(" + s(x.a) + ", " + s(x.b) + ")";
  case O_NEG: return "-" + s(x.a);
  case O_AND: return bin(x.w == 1 ? "&&" : "&");
  case O_OR: return bin(x.w == 1 ? "||" : "|");
  case O_XOR: return bin("^");
  case O_NOT: return (x.w == 1 ? "!" : "~") + s(x.a);
  case O_SHL: return bin("<<");
  case O_LSHR: return bin(">>");
  case O_ASHR: return bin(">>s");
  case O_ROL: return "rol(" + s(x.a) + ", " + s(x.b) + ")";
  case O_ROR: return "ror(" + s(x.a) + ", " + s(x.b) + ")";
  case O_EXTRACT: snprintf(buf, sizeof buf, "[%u:%u]", x.lo + x.w - 1, x.lo); return s(x.a) + buf;
  case O_ZEXT: snprintf(buf, sizeof buf, "zx%u(", x.w); return buf + s(x.a) + ")";
  case O_SEXT: snprintf(buf, sizeof buf, "sx%u(", x.w); return buf + s(x.a) + ")";
  case O_CONCAT: return "{" + s(x.a) + ", " + s(x.b) + "}";
  case O_ITE: return "(" + s(x.a) + " ? " + s(x.b) + " : " + s(x.c) + ")";
  case O_EQ: return bin("==");
  case O_ULT: return bin("<u");
  case O_ULE: return bin("<=u");
  case O_SLT: return bin("<s");
  case O_SLE: return bin("<=s");
  case O_POPCNT: return "popcnt(" + s(x.a) + ")";
  case O_CLZ: return "clz(" + s(x.a) + ")";
  case O_CTZ: return "ctz(" + s(x.a) + ")";
  default: return "?";
  }
}

std::string Ctx::smt(u32 root) const {
  std::vector<u32> order; std::vector<u8> seen(n.size(), 0);
  std::vector<std::pair<u32, int>> st{{root, 0}};
  while (!st.empty()) {
    auto& top = st.back(); u32 id = top.first;
    if (seen[id] == 2) { st.pop_back(); continue; }
    const Node& x = n[id];
    u32 kids[3] = {x.a, x.b, x.c};
    if (top.second < 3) { u32 c = kids[top.second++]; if (c && !seen[c]) st.push_back({c, 0}); continue; }
    seen[id] = 2; order.push_back(id); st.pop_back();
  }
  std::string out;
  char buf[200];
  auto name = [&](u32 id) -> std::string {
    const Node& x = n[id];
    if (x.op == O_CONST) { snprintf(buf, sizeof buf, "(_ bv%llu %u)", (unsigned long long)x.k, x.w); return buf; }
    if (x.op == O_VAR) return "|" + vars[x.k].name + "|";
    snprintf(buf, sizeof buf, "t%u", id); return buf;
  };
  for (u32 id : order) if (n[id].op == O_VAR) { snprintf(buf, sizeof buf, "(declare-fun |%s| () (_ BitVec %u))\n", vars[n[id].k].name.c_str(), n[id].w); out += buf; }
  for (u32 id : order) {
    const Node& x = n[id];
    if (x.op == O_CONST || x.op == O_VAR) continue;
    std::string e;
    auto b2 = [&](const char* o) { return std::string("(") + o + " " + name(x.a) + " " + name(x.b) + ")"; };
    auto bb = [&](const std::string& p) { return "(ite " + p + " #b1 #b0)"; };
    switch (x.op) {
    case O_ADD: e = b2("bvadd"); break;
    case O_MUL: e = b2("bvmul"); break;
    case O_UDIV: e = b2("bvudiv"); break;
    case O_UREM: e = b2("bvurem"); break;
    case O_SDIV: e = b2("bvsdiv"); break;
    case O_SREM: e = b2("bvsrem"); break;
    case O_MULHU: case O_MULHS: {
      const char* ext = x.op == O_MULHU ? "zero_extend" : "sign_extend";
      e = "((_ extract " + std::to_string(2 * x.w - 1) + " " + std::to_string(x.w) + ") (bvmul ((_ " + ext + " " + std::to_string(x.w) + ") " + name(x.a) + ") ((_ " + ext + " " + std::to_string(x.w) + ") " + name(x.b) + ")))";
      break;
    }
    case O_NEG: e = "(bvneg " + name(x.a) + ")"; break;
    case O_AND: e = b2("bvand"); break;
    case O_OR: e = b2("bvor"); break;
    case O_XOR: e = b2("bvxor"); break;
    case O_NOT: e = "(bvnot " + name(x.a) + ")"; break;
    case O_SHL: e = b2("bvshl"); break;
    case O_LSHR: e = b2("bvlshr"); break;
    case O_ASHR: e = b2("bvashr"); break;
    case O_ROL: case O_ROR: {
      const Node& s = n[x.b];
      if (s.op == O_CONST) { snprintf(buf, sizeof buf, "((_ %s %llu) %s)", x.op == O_ROL ? "rotate_left" : "rotate_right", (unsigned long long)(s.k % x.w), name(x.a).c_str()); e = buf; }
      else {
        std::string amt = "(bvurem " + name(x.b) + " (_ bv" + std::to_string(x.w) + " " + std::to_string(x.w) + "))";
        std::string back = "(bvsub (_ bv" + std::to_string(x.w) + " " + std::to_string(x.w) + ") " + amt + ")";
        if (x.op == O_ROL) e = "(bvor (bvshl " + name(x.a) + " " + amt + ") (bvlshr " + name(x.a) + " " + back + "))";
        else e = "(bvor (bvlshr " + name(x.a) + " " + amt + ") (bvshl " + name(x.a) + " " + back + "))";
      }
      break;
    }
    case O_EXTRACT: snprintf(buf, sizeof buf, "((_ extract %u %u) %s)", x.lo + x.w - 1, x.lo, name(x.a).c_str()); e = buf; break;
    case O_ZEXT: snprintf(buf, sizeof buf, "((_ zero_extend %u) %s)", x.w - x.lo, name(x.a).c_str()); e = buf; break;
    case O_SEXT: snprintf(buf, sizeof buf, "((_ sign_extend %u) %s)", x.w - x.lo, name(x.a).c_str()); e = buf; break;
    case O_CONCAT: e = b2("concat"); break;
    case O_ITE: e = "(ite (= " + name(x.a) + " #b1) " + name(x.b) + " " + name(x.c) + ")"; break;
    case O_EQ: e = bb(b2("=")); break;
    case O_ULT: e = bb(b2("bvult")); break;
    case O_ULE: e = bb(b2("bvule")); break;
    case O_SLT: e = bb(b2("bvslt")); break;
    case O_SLE: e = bb(b2("bvsle")); break;
    default: e = "(_ bv0 " + std::to_string(x.w) + ")"; break;
    }
    snprintf(buf, sizeof buf, "(define-fun t%u () (_ BitVec %u) ", id, x.w);
    out += buf; out += e; out += ")\n";
  }
  return out;
}

}  // namespace unshroud

namespace unshroud {
std::string Ctx::py(const std::vector<u32>& roots, const std::string& fname, const std::vector<u64>* defaults) const {
  std::vector<u32> order; std::vector<u8> seen(n.size(), 0);
  for (u32 root : roots) {
    std::vector<std::pair<u32, int>> st{{root, 0}};
    while (!st.empty()) {
      auto& top = st.back(); u32 id = top.first;
      if (seen[id] == 2) { st.pop_back(); continue; }
      const Node& x = n[id];
      u32 kids[3] = {x.a, x.b, x.c};
      if (top.second < 3) { u32 c = kids[top.second++]; if (c && !seen[c]) st.push_back({c, 0}); continue; }
      seen[id] = 2; order.push_back(id); st.pop_back();
    }
  }
  char buf[64];
  auto nm = [&](u32 id) -> std::string {
    const Node& x = n[id];
    if (x.op == O_CONST) { snprintf(buf, sizeof buf, "0x%llx", (unsigned long long)x.k); return buf; }
    if (x.op == O_VAR) return "(" + vars[x.k].name + " & 0x" + [&] { char b[24]; snprintf(b, sizeof b, "%llx", (unsigned long long)maskOf(x.w)); return std::string(b); }() + ")";
    snprintf(buf, sizeof buf, "t%u", id); return buf;
  };
  std::string out = "def " + fname + "(x=0, y=0, z=0, w=0";
  for (size_t i = 0; i < vars.size(); i++) {
    const std::string& vn = vars[i].name;
    if (vn == "x" || vn == "y" || vn == "z" || vn == "w") continue;
    char b[40]; snprintf(b, sizeof b, "=0x%llx", (unsigned long long)(defaults && i < defaults->size() ? (*defaults)[i] : vars[i].seed));
    out += ", " + vn + b;
  }
  out += "):\n";
  for (u32 id : order) {
    const Node& x = n[id];
    if (x.op == O_CONST || x.op == O_VAR) continue;
    snprintf(buf, sizeof buf, "%u, %u, %u", x.w, x.lo, 0u);
    std::string args = nm(x.a) + (x.b ? ", " + nm(x.b) : std::string(", 0")) + (x.c ? ", " + nm(x.c) : std::string(", 0"));
    snprintf(buf, sizeof buf, "  t%u = op(%u, %u, %u, ", id, (unsigned)x.op, (unsigned)x.w, (unsigned)x.lo);
    out += buf; out += args; out += ")\n";
  }
  out += "  return [";
  for (size_t i = 0; i < roots.size(); i++) { out += (i ? ", " : "") + nm(roots[i]); }
  out += "]\n";
  return out;
}
}  // namespace unshroud

// ================================================================================================ ranges, magic division
namespace unshroud {

Ctx::Range Ctx::range(u32 id, int depth) {
  const Node x = n[id];
  const u64 full = maskOf(x.w);
  if (x.op == O_CONST) return {x.k, x.k};
  if (off & 4) return {0, full};
  if (id < rhave.size() && rhave[id]) return rmemo[id];
  if (depth > 16) return {0, full};
  auto R = [&](u32 c) { return range(c, depth + 1); };
  auto bitlen = [](u64 v) { unsigned long b; return _BitScanReverse64(&b, v) ? (unsigned)b + 1 : 0u; };
  Range r{0, full};
  switch (x.op) {
  case O_ZEXT: r = R(x.a); break;
  case O_EXTRACT: { Range a = R(x.a); if ((a.hi >> x.lo) <= full) r = {a.lo >> x.lo, a.hi >> x.lo}; break; }
  case O_ADD: { Range a = R(x.a), b = R(x.b); if (a.hi <= full - b.hi) r = {a.lo + b.lo, a.hi + b.hi}; break; }
  case O_MUL: if (isC(x.b)) { Range a = R(x.a); u64 c = cv(x.b), hi; u64 lo = _umul128(a.hi, c, &hi); if (!hi && lo <= full) r = {a.lo * c, lo}; } break;
  case O_AND: { Range a = R(x.a), b = R(x.b); r = {0, std::min(a.hi, b.hi)}; break; }
  case O_OR: case O_XOR: { Range a = R(x.a), b = R(x.b); unsigned l = bitlen(std::max(a.hi, b.hi)); r = {x.op == O_OR ? std::max(a.lo, b.lo) : 0, l >= 64 ? ~0ull : (1ull << l) - 1}; break; }
  case O_LSHR: if (isC(x.b) && cv(x.b) < 64) { Range a = R(x.a); r = {a.lo >> cv(x.b), a.hi >> cv(x.b)}; } break;
  case O_UDIV: { Range a = R(x.a), b = R(x.b); if (b.lo > 0) r = {a.lo / b.hi, a.hi / b.lo}; break; }
  case O_UREM: { Range a = R(x.a), b = R(x.b); r = {0, b.lo > 0 ? std::min(a.hi, b.hi - 1) : a.hi}; break; }
  case O_ITE: { Range a = R(x.b), b = R(x.c); r = {std::min(a.lo, b.lo), std::max(a.hi, b.hi)}; break; }
  case O_EQ: case O_ULT: case O_ULE: case O_SLT: case O_SLE: r = {0, 1}; break;
  case O_POPCNT: case O_CLZ: case O_CTZ: r = {0, x.lo}; break;
  case O_MULHU: { Range a = R(x.a), b = R(x.b); u64 hi; u64 lo = _umul128(a.hi, b.hi, &hi);
    u64 top = x.w == 64 ? hi : ((lo >> x.w) | (hi << (64 - x.w))); if (x.w < 64 && (hi >> x.w)) top = full; r = {0, std::min(top, full)}; break; }
  default: break;
  }
  if (rhave.size() < n.size()) { rhave.resize(n.size() + n.size() / 2 + 1024, 0); rmemo.resize(n.size() + n.size() / 2 + 1024); }
  rhave[id] = 1; rmemo[id] = r;
  return r;
}

// Granlund-Montgomery: for 0 <= a < 2^N, floor(a*M / 2^(N+s)) == floor(a/d) when 2^(N+s) <= M*d <= 2^(N+s) + 2^s
u32 Ctx::magicDiv(u32 a, u64 M, unsigned N, unsigned s) {
  if (off & 1) return 0;
  // a is below 2^N by its width; its range may say less (a value shifted right before the product): less of the
  // constant is needed for the same quotient
  {
    const u64 hi = range(a).hi; unsigned long b; const unsigned bl = _BitScanReverse64(&b, hi) ? (unsigned)b + 1 : 1;
    if (bl < N) { s += N - bl; N = bl; }
  }
  const unsigned wa0 = W(a);
  if (M < 2 || N + s >= 127) return 0;
  const unsigned __int128 P = (unsigned __int128)1 << (N + s);
  u64 q0;
  if (N + s < 64) q0 = (1ull << (N + s)) / M;
  else {
    u64 rem = 1ull << (N + s - 64), q = 0;          // (rem:0) / M by long division, rem < M
    if (rem >= M) return 0;
    for (int i = 63; i >= 0; i--) { bool top = rem >> 63; rem <<= 1; if (top || rem >= M) { rem -= M; q |= 1ull << i; } }
    q0 = q;
  }
  const unsigned __int128 d0 = q0;
  for (unsigned __int128 d = d0; d <= d0 + 1; d++) {
    if (d < 2 || d > maskOf(wa0)) continue;
    unsigned __int128 md = (unsigned __int128)M * d;
    if (md >= P && md - P <= ((unsigned __int128)1 << s)) return udiv(a, cst((u64)d, wa0));
  }
  return 0;
}

}  // namespace unshroud

// ------------------------------------------------------------------------------------------------ known bits
namespace unshroud {
Ctx::Known Ctx::known(u32 root) {
  if (khave.size() < n.size()) { khave.resize(n.size() + n.size() / 2 + 64, 0); kmemo.resize(khave.size()); }
  std::vector<u32> st{root};
  while (!st.empty()) {
    const u32 id = st.back();
    if (khave[id]) { st.pop_back(); continue; }
    const Node& x = n[id];
    bool ready = true;
    if (x.op != O_CONST && x.op != O_VAR) for (u32 c : {x.a, x.b, x.c}) if (c && !khave[c]) { st.push_back(c); ready = false; }
    if (!ready) continue;
    st.pop_back();
    const unsigned w = x.w; const u64 m = maskOf(w);
    Known r{0, 0};
    const Known a = x.a ? kmemo[x.a] : Known{0, 0}, b = x.b ? kmemo[x.b] : Known{0, 0};
    auto addk = [&](Known p, Known q) {            // p + q
      const u64 maxp = ~p.zeros & m, maxq = ~q.zeros & m;
      const u64 sumZero = (maxp + maxq) & m, sumOne = (p.ones + q.ones) & m;
      const u64 carryZero = ~(sumZero ^ p.zeros ^ q.zeros), carryOne = sumOne ^ p.ones ^ q.ones;
      const u64 kn = (p.zeros | p.ones) & (q.zeros | q.ones) & (carryZero | carryOne);
      return Known{~sumZero & kn & m, sumOne & kn & m};
    };
    auto low0 = [&](Known p) -> unsigned { u64 z = p.zeros | ~m; unsigned long i; if (!_BitScanForward64(&i, ~z)) return 64; return (unsigned)i; };   // trailing bits known 0
    switch (x.op) {
    case O_CONST: r = {~x.k & m, x.k & m}; break;
    case O_AND: r = {(a.zeros | b.zeros) & m, a.ones & b.ones}; break;
    case O_OR: r = {a.zeros & b.zeros, (a.ones | b.ones) & m}; break;
    case O_XOR: r = {((a.zeros & b.zeros) | (a.ones & b.ones)) & m, ((a.zeros & b.ones) | (a.ones & b.zeros)) & m}; break;
    case O_NOT: r = {a.ones, a.zeros}; break;
    case O_ZEXT: r = {(a.zeros | ~maskOf(x.lo)) & m, a.ones}; break;
    case O_SEXT: {
      const u64 hi = m & ~maskOf(x.lo), sb = 1ull << (x.lo - 1);
      r = {a.zeros | ((a.zeros & sb) ? hi : 0), a.ones | ((a.ones & sb) ? hi : 0)};
      break;
    }
    case O_EXTRACT: r = {(a.zeros >> x.lo) & m, (a.ones >> x.lo) & m}; break;
    case O_CONCAT: r = {((a.zeros << x.lo) | b.zeros) & m, ((a.ones << x.lo) | b.ones) & m}; break;
    case O_ITE: { const Known c = kmemo[x.c]; r = {b.zeros & c.zeros, b.ones & c.ones}; break; }
    case O_ADD: r = addk(a, b); break;
    case O_NEG: { const unsigned t = std::min(low0(a), w); r = {maskOf(t) & m, 0}; break; }
    case O_MUL: {
      if (x.b && n[x.b].op == O_CONST && (n[x.b].k & (n[x.b].k - 1)) == 0 && n[x.b].k) {      // a shift to the left
        unsigned long s; _BitScanForward64(&s, n[x.b].k);
        r = {((a.zeros << s) | maskOf(s)) & m, (a.ones << s) & m};
      } else { const unsigned t = std::min<unsigned>(low0(a) + low0(b), w); r = {maskOf(t) & m, 0}; }
      break;
    }
    case O_EQ: case O_ULT: case O_ULE: case O_SLT: case O_SLE: case O_VAR: default: r = {0, 0}; break;
    }
    kmemo[id] = r; khave[id] = 1;
  }
  return kmemo[root];
}
}  // namespace unshroud

// ------------------------------------------------------------------------------------------------ deferred operations
namespace unshroud {
static inline u32 memoSlot(u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c, u64 k) {
  u64 h = ((u64)op | ((u64)w << 8) | ((u64)lo << 16)) ^ ((u64)a * 0x9E3779B97F4A7C15ull);
  h = (h ^ (h >> 29)) * 0xBF58476D1CE4E5B9ull; h ^= ((u64)b << 32 | c) + k;
  h = (h ^ (h >> 32)) * 0x94D049BB133111EBull;
  return (u32)(h >> 48);
}

u32 Ctx::deferConst(u64 v, unsigned w) {
  v &= maskOf(w);
  if (lazyMemo.empty()) lazyMemo.assign(1 << 16, 0);
  u32& m = lazyMemo[memoSlot(O_CONST, w, 0, 0, 0, 0, v)];
  if (m < tape.size()) { const TapeRec& t = tape[m]; if (t.op == O_CONST && t.w == w && t.k == v) return LAZY_BASE + m; }
  tape.push_back(TapeRec{O_CONST, (u8)w, 0, 0, 0, 0, 0, 0, v});
  m = (u32)tape.size() - 1;
  return LAZY_BASE + m;
}

u32 Ctx::defer(u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c) {
  deferred++;
  // operations on constants are done at once (a recorded constant is a constant for whoever asks)
  if ((!a || isC(a)) && (!b || isC(b)) && (!c || isC(c))) {
    const u64 v = op == O_SUBL ? cv(a) - cv(b) : evalOp(op, w, lo, 0, a ? cv(a) : 0, b ? cv(b) : 0, c ? cv(c) : 0);
    return deferConst(v, w);
  }
  if (a == b && (op == O_XOR || op == O_SUBL)) return deferConst(0, w);
  if (a == b && (op == O_AND || op == O_OR)) return a;
  // the wiring between widths (a 32-bit result is extended, then its low half is read again): undone here, or every
  // instruction would stack two records
  if (op == O_EXTRACT || op == O_ZEXT) {
    u8 xop; unsigned xw, xlo; u32 xa, xb;
    if (a >= LAZY_BASE) { const TapeRec& t = tape[a - LAZY_BASE]; xop = t.op; xw = t.w; xlo = t.lo; xa = t.a; xb = t.b; }
    else { const Node& t = n[a]; xop = t.op; xw = t.w; xlo = t.lo; xa = t.a; xb = t.b; }
    if (op == O_EXTRACT) {
      if ((xop == O_ZEXT || xop == O_SEXT) && lo + w <= xlo) return lo == 0 && w == xlo ? xa : defer(O_EXTRACT, w, lo, xa, 0, 0);
      if (xop == O_ZEXT && lo >= xlo) return deferConst(0, w);
      if (xop == O_EXTRACT) return defer(O_EXTRACT, w, xlo + lo, xa, 0, 0);
      if (xop == O_CONCAT) {
        if (lo + w <= xlo) return lo == 0 && w == xlo ? xb : defer(O_EXTRACT, w, lo, xb, 0, 0);
        if (lo >= xlo) return lo == xlo && w == xw - xlo ? xa : defer(O_EXTRACT, w, lo - xlo, xa, 0, 0);
      }
    } else if (xop == O_ZEXT) return defer(O_ZEXT, w, xlo, xa, 0, 0);
  }
  if (lazyMemo.empty()) lazyMemo.assign(1 << 16, 0);
  u32& m = lazyMemo[memoSlot(op, w, lo, a, b, c, 0)];
  if (m < tape.size()) { const TapeRec& t = tape[m]; if (t.op == op && t.w == w && t.lo == lo && t.a == a && t.b == b && t.c == c) return LAZY_BASE + m; }
  // how long the chain of unbuilt operations below is: a value which keeps being updated (a counter, a running hash) is
  // built every so often, which lets the rules fold it and keeps what is recorded short-lived
  unsigned depth = 1;
  for (u32 k : {a, b, c}) if (k >= LAZY_BASE) { const TapeRec& t = tape[k - LAZY_BASE]; if (!t.real && t.pad + 1u > depth) depth = t.pad + 1u; }
  tape.push_back(TapeRec{op, (u8)w, (u8)lo, (u8)depth, a, b, c, 0, 0});
  m = (u32)tape.size() - 1;
  if (depth >= lazyDepth) return force(LAZY_BASE + m);
  return LAZY_BASE + m;
}

u32 Ctx::force(u32 root) {
  if (root < LAZY_BASE) return root;
  if (tape[root - LAZY_BASE].real) return tape[root - LAZY_BASE].real;
  const bool was = lazyOn; lazyOn = false;
  std::vector<u32>& st = forceStack; st.clear(); st.push_back(root - LAZY_BASE);
  while (!st.empty()) {
    const u32 i = st.back();
    const TapeRec r = tape[i];
    if (r.real) { st.pop_back(); continue; }
    bool ready = true;
    for (u32 k : {r.a, r.b, r.c}) if (k >= LAZY_BASE && !tape[k - LAZY_BASE].real) { st.push_back(k - LAZY_BASE); ready = false; }
    if (!ready) continue;
    st.pop_back();
    auto real = [&](u32 k) { return k >= LAZY_BASE ? tape[k - LAZY_BASE].real : k; };
    const u32 a = real(r.a), b = real(r.b), c = real(r.c);
    u32 v;
    if (r.op == O_CONST) v = cst(r.k, r.w);
    else if (r.op == O_SUBL) v = sub(a, b);
    else v = make(r.op, r.w, r.lo, a, b, c, 0);
    tape[i].real = v;
    forcedCount++;
  }
  lazyOn = was;
  return tape[root - LAZY_BASE].real;
}
}  // namespace unshroud
