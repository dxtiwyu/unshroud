// unshroud - signatures and the table of small expressions
#include "sig.hpp"
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <mutex>

namespace unshroud {

static inline u64 mix64(u64 x) { x += 0x9E3779B97F4A7C15ull; x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ull; x = (x ^ (x >> 27)) * 0x94D049BB133111EBull; return x ^ (x >> 31); }

static const u64 kSpecial[] = {1, 0x8000000000000000ull, 0x7fffffffffffffffull, 2, 0xffffffffull, 0x5555555555555555ull, 0x100000000ull,
                               0xaaaaaaaaaaaaaaaaull, 0xff, 0x80, 0xffffffff00000000ull, 3};

// test k of input i: 0 and -1 for everybody, two tests of special values, then random ones (a few special among them)
static u64 testValue(u64 i, int k) {
  if (k == 0) return 0;
  if (k == 1) return ~0ull;
  if (k == 2 || k == 3) return kSpecial[(i * 2 + (k - 2)) % 12];
  u64 r = mix64(mix64(i * 0x100000001b3ull + 0x5eed) ^ ((u64)k * 0x9E3779B97F4A7C15ull));
  if (k >= ORA_K && (r >> 61) == 0) return kSpecial[(r >> 8) % 12];
  return r;
}

u64 oracleTest(int leaf, int k) { return testValue((u64)leaf, k); }

// sparse, small, dense, or a mix chosen per variable
static u64 diverseValue(u64 i, int k) {
  u64 r = mix64(mix64(i * 0x9E3779B97F4A7C15ull + 0xd1ce) ^ ((u64)k * 0xff51afd7ed558ccdull));
  int kind = k & 3;
  if (kind == 3) kind = (int)((r >> 50) % 5);
  const u64 sparse = (1ull << (r & 63)) | ((r >> 6) & 1 ? 1ull << ((r >> 8) & 63) : 0) | ((r >> 7) & 1 ? 1ull << ((r >> 14) & 63) : 0);
  switch (kind) {
  case 0: return sparse;
  case 1: return (r >> 20) & maskOf(8 * (1 + (unsigned)((r >> 3) % 3)));
  case 2: return ~sparse;
  case 3: return kSpecial[(r >> 30) % 12];
  default: return mix64(r);
  }
}

u64 sigTestValue(u64 var, int k, int flavor) { return flavor ? diverseValue(var, k) : testValue(var, k); }

void evalVec(u8 op, unsigned w, unsigned lo, u64 kk, const u64* a, const u64* b, const u64* c, u64* out, int n) {
  const u64 m = maskOf(w);
  switch (op) {
  case O_ADD: for (int i = 0; i < n; i++) out[i] = (a[i] + b[i]) & m; break;
  case O_MUL: for (int i = 0; i < n; i++) out[i] = (a[i] * b[i]) & m; break;
  case O_NEG: for (int i = 0; i < n; i++) out[i] = (0 - a[i]) & m; break;
  case O_AND: for (int i = 0; i < n; i++) out[i] = a[i] & b[i]; break;
  case O_OR: for (int i = 0; i < n; i++) out[i] = a[i] | b[i]; break;
  case O_XOR: for (int i = 0; i < n; i++) out[i] = a[i] ^ b[i]; break;
  case O_NOT: for (int i = 0; i < n; i++) out[i] = ~a[i] & m; break;
  case O_EXTRACT: for (int i = 0; i < n; i++) out[i] = (a[i] >> lo) & m; break;
  case O_ZEXT: for (int i = 0; i < n; i++) out[i] = a[i]; break;
  case O_CONCAT: for (int i = 0; i < n; i++) out[i] = ((a[i] << lo) | b[i]) & m; break;
  case O_ITE: for (int i = 0; i < n; i++) out[i] = (a[i] & 1) ? b[i] : c[i]; break;
  default: for (int i = 0; i < n; i++) out[i] = evalOp(op, w, lo, kk, a ? a[i] : 0, b ? b[i] : 0, c ? c[i] : 0) & m; break;
  }
}

static inline bool isCompare(u8 op) { return op == O_EQ || op == O_ULT || op == O_ULE || op == O_SLT || op == O_SLE; }

static inline u64 hashVals(const u64* v, int n, unsigned w) {
  u64 h = 0x9E3779B97F4A7C15ull ^ w;
  for (int k = 0; k < n; k++) h = (h ^ v[k]) * 0xff51afd7ed558ccdull + (h >> 31);
  return h ^ (h >> 32);
}

Sigs::~Sigs() { for (u64* c : chunks) free(c); }

void Sigs::compute(u32 root) {
  std::vector<u32> st{root};
  if (idx.size() < X.n.size()) idx.resize(X.n.size() + X.n.size() / 4 + 64, 0);
  while (!st.empty()) {
    const u32 id = st.back();
    if (idx[id]) { st.pop_back(); continue; }
    const Node& x = X.N(id);
    const bool cmp = isCompare(x.op);
    if (!cmp) {
      bool ready = true;
      if (x.a && !idx[x.a]) { st.push_back(x.a); ready = false; }
      if (x.b && !idx[x.b]) { st.push_back(x.b); ready = false; }
      if (x.c && !idx[x.c]) { st.push_back(x.c); ready = false; }
      if (!ready) continue;
    }
    st.pop_back();
    const u32 s = (u32)n++;
    if ((s >> 10) >= chunks.size()) chunks.push_back((u64*)malloc(sizeof(u64) * SIG_K * 1024));
    hashes.push_back(0);
    {
      u8 f = 0;
      for (u32 c : {x.a, x.b, x.c}) if (c && idx[c]) f |= flg[idx[c] - 1];
      if (x.op == O_ADD || x.op == O_MUL || x.op == O_NEG) f |= 1;
      if (x.op == O_EXTRACT && x.lo > 0 && (flg[idx[x.a] - 1] & 1)) f |= 2;
      if (cmp || x.op == O_ITE || x.op == O_LSHR || x.op == O_ASHR || x.op == O_UDIV || x.op == O_UREM || x.op == O_SDIV || x.op == O_SREM || x.op == O_MULHU || x.op == O_MULHS ||
          x.op == O_CLZ || x.op == O_CTZ || x.op == O_POPCNT || x.op == O_SHL || x.op == O_ROL || x.op == O_ROR) f |= 2;
      flg.push_back(f);
    }
    u64* out = slotPtr(s);
    const u64 m = maskOf(x.w);
    if (x.op == O_CONST) { for (int k = 0; k < SIG_K; k++) out[k] = x.k; }
    else if (x.op == O_VAR) { for (int k = 0; k < SIG_K; k++) out[k] = sigTestValue(x.k, k, flavor) & m; }
    else if (cmp) {
      // a <= b is !(b < a): the same bits, inverted
      u64 bits;
      if (x.op == O_ULE) bits = ~mix64(mix64(((u64)O_ULT << 32) ^ x.b) ^ x.a);
      else if (x.op == O_SLE) bits = ~mix64(mix64(((u64)O_SLT << 32) ^ x.b) ^ x.a);
      else bits = mix64(mix64(((u64)x.op << 32) ^ x.a) ^ x.b);
      for (int k = 0; k < SIG_K; k++) out[k] = (bits >> k) & 1;
    } else {
      const u64* a = x.a ? slotPtr(idx[x.a] - 1) : nullptr;
      const u64* b = x.b ? slotPtr(idx[x.b] - 1) : nullptr;
      const u64* c = x.c ? slotPtr(idx[x.c] - 1) : nullptr;
      evalVec(x.op, x.w, x.lo, x.k, a, b, c, out, SIG_K);
      // (the first two tests give every input the same value: what holds there says little; they are left out)
      bool same = true; for (int k = 3; k < SIG_K && same; k++) same = out[k] == out[2];
      if (same && (flg[s] & 2) && X.unknownBits(id) != 0) {
        suspects[id] = out[2];
        const u64 r0 = mix64(((u64)id << 20) ^ 0xf4ee ^ (u64)flavor);
        for (int k = 0; k < SIG_K; k++) out[k] = mix64(r0 + (u64)k * 0x9E3779B97F4A7C15ull) & m;
      }
    }
    hashes[s] = hashVals(out, SIG_K, x.w);
    idx[id] = s + 1;
  }
}

void evalBatch(Ctx& X, const u32* roots, int nroots, int n, u64 (*varVal)(void*, u32, int), void* ud, u64* out) {
  X.newGen();
  std::vector<u64> buf; u32 slots = 0;
  std::vector<u32> st;
  for (int r = 0; r < nroots; r++) {
    st.push_back(roots[r]);
    while (!st.empty()) {
      const u32 id = st.back();
      if (X.stamp[id] == X.gen) { st.pop_back(); continue; }
      const Node& x = X.N(id);
      bool ready = true;
      if (x.a && X.stamp[x.a] != X.gen) { st.push_back(x.a); ready = false; }
      if (x.b && X.stamp[x.b] != X.gen) { st.push_back(x.b); ready = false; }
      if (x.c && X.stamp[x.c] != X.gen) { st.push_back(x.c); ready = false; }
      if (!ready) continue;
      st.pop_back();
      const u32 s = slots++;
      buf.resize((size_t)slots * n);
      u64* o = &buf[(size_t)s * n];
      if (x.op == O_CONST) { for (int k = 0; k < n; k++) o[k] = x.k; }
      else if (x.op == O_VAR) { const u64 m = maskOf(x.w); for (int k = 0; k < n; k++) o[k] = varVal(ud, (u32)x.k, k) & m; }
      else evalVec(x.op, x.w, x.lo, x.k, x.a ? &buf[(size_t)X.memo[x.a] * n] : nullptr, x.b ? &buf[(size_t)X.memo[x.b] * n] : nullptr, x.c ? &buf[(size_t)X.memo[x.c] * n] : nullptr, o, n);
      X.memo[id] = s; X.stamp[id] = X.gen;
    }
    memcpy(out + (size_t)r * n, &buf[(size_t)X.memo[roots[r]] * n], sizeof(u64) * n);
  }
}

// ------------------------------------------------------------------------------------------------ the table
// candidate operations: 0 leaf (a: index), 1 constant (a, b: low and high halves), 2 not, 3 neg, 4 add, 5 mul, 6 and, 7 or, 8 xor, 9 sub
static inline u64 opVal(u8 op, u64 a, u64 b) {
  switch (op) { case 2: return ~a; case 3: return 0 - a; case 4: return a + b; case 5: return a * b; case 6: return a & b; case 7: return a | b; case 8: return a ^ b; default: return a - b; }
}

int Oracle::find(const u64* v) const {
  const u64 h = hashVals(v, ORA_K, w);
  const u64 tag = h & 0xffffffff00000000ull;
  for (u64 i = h & tmask;; i = (i + 1) & tmask) {
    const u64 e = tab[i];
    if (!e) return -1;
    if ((e & 0xffffffff00000000ull) == tag) return (int)(u32)e - 1;
  }
}

bool Oracle::insert(const u64* v, const Cand& c, bool keepVals) {
  const u64 h = hashVals(v, ORA_K, w);
  const u64 tag = h & 0xffffffff00000000ull;
  u64 i = h & tmask;
  for (;; i = (i + 1) & tmask) {
    const u64 e = tab[i];
    if (!e) break;
    if ((e & 0xffffffff00000000ull) == tag) return false;
  }
  tab[i] = tag | (u64)(C.size() + 1);
  C.push_back(c);
  if (keepVals) { V.insert(V.end(), v, v + ORA_K); nVals = (u32)C.size(); }
  return true;
}

void Oracle::build(unsigned width) {
  auto t0 = std::chrono::steady_clock::now();
  w = width; m = maskOf(w);
  levels = 3;
  if (const char* e = getenv("UNSHROUD_ORACLE_LEVELS")) levels = std::max(1, std::min(4, atoi(e)));
  tab.assign((size_t)1 << (levels >= 4 ? 25 : 20), 0); tmask = tab.size() - 1;
  C.reserve(levels >= 4 ? 9000000 : 400000);
  std::vector<std::vector<u32>> level(levels + 1);
  u64 v[ORA_K];
  auto add = [&](const Cand& c, bool keep) { if (insert(v, c, keep)) level[c.lvl].push_back((u32)C.size() - 1); };
  // the constant 0 is an answer, never an operand
  for (int k = 0; k < ORA_K; k++) v[k] = 0;
  insert(v, Cand{1, 0, 0, 0}, true);
  for (int i = 0; i < ORA_LEAVES; i++) { for (int k = 0; k < ORA_K; k++) v[k] = oracleTest(i, k) & m; add(Cand{0, 0, (u32)i, 0}, true); }
  for (u64 k0 : {(u64)1, m, (u64)2}) { for (int k = 0; k < ORA_K; k++) v[k] = k0 & m; add(Cand{1, 0, (u32)k0, (u32)(k0 >> 32)}, true); }
  u64 a[ORA_K], b[ORA_K];
  for (int s = 1; s <= levels; s++) {
    const bool keep = s < levels;
    const std::vector<u32> prev(level[s - 1]);
    for (u32 ia : prev) {
      memcpy(a, &V[(size_t)ia * ORA_K], sizeof a);
      for (u8 op = 2; op <= 3; op++) { for (int k = 0; k < ORA_K; k++) v[k] = opVal(op, a[k], 0) & m; add(Cand{op, (u8)s, ia, 0}, keep); }
    }
    for (int i = 0; i <= (s - 1) / 2; i++) {
      const int j = s - 1 - i;
      const std::vector<u32> L1(level[i]), L2(level[j]);
      for (u32 ia : L1) {
        memcpy(a, &V[(size_t)ia * ORA_K], sizeof a);
        for (u32 ib : L2) {
          if (i == j && ib < ia) continue;
          memcpy(b, &V[(size_t)ib * ORA_K], sizeof b);
          for (u8 op = 4; op <= 8; op++) { for (int k = 0; k < ORA_K; k++) v[k] = opVal(op, a[k], b[k]) & m; add(Cand{op, (u8)s, ia, ib}, keep); }
          for (int k = 0; k < ORA_K; k++) v[k] = (a[k] - b[k]) & m;
          add(Cand{9, (u8)s, ia, ib}, keep);
          for (int k = 0; k < ORA_K; k++) v[k] = (b[k] - a[k]) & m;
          add(Cand{9, (u8)s, ib, ia}, keep);
        }
      }
    }
  }
  buildSeconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  if (getenv("UNSHROUD_ORACLE_STATS")) fprintf(stderr, "oracle w=%u: %zu expressions (%u with values), %.3fs\n", w, C.size(), nVals, buildSeconds);
}

const Oracle& Oracle::get(unsigned w) {
  static std::mutex mu; static Oracle* tabs[65];
  std::lock_guard<std::mutex> g(mu);
  if (!tabs[w]) { Oracle* o = new Oracle(); o->build(w); tabs[w] = o; }
  return *tabs[w];
}

u32 Oracle::mk(Ctx& X, u32 i, const u32* leaves, bool& ok) const {
  const Cand c = C[i];
  switch (c.op) {
  case 0: if (!leaves[c.a]) { ok = false; return X.cst(0, w); } return leaves[c.a];
  case 1: return X.cst(((u64)c.b << 32) | c.a, w);
  case 2: return X.not_(mk(X, c.a, leaves, ok));
  case 3: return X.neg(mk(X, c.a, leaves, ok));
  case 4: return X.add(mk(X, c.a, leaves, ok), mk(X, c.b, leaves, ok));
  case 5: return X.mul(mk(X, c.a, leaves, ok), mk(X, c.b, leaves, ok));
  case 6: return X.and_(mk(X, c.a, leaves, ok), mk(X, c.b, leaves, ok));
  case 7: return X.or_(mk(X, c.a, leaves, ok), mk(X, c.b, leaves, ok));
  case 8: return X.xor_(mk(X, c.a, leaves, ok), mk(X, c.b, leaves, ok));
  default: return X.sub(mk(X, c.a, leaves, ok), mk(X, c.b, leaves, ok));
  }
}

u32 Oracle::lookup(Ctx& X, const u64* vals, const u32* leaves) const {
  int i = find(vals);
  if (i < 0) return 0;
  bool ok = true;
  u32 r = mk(X, (u32)i, leaves, ok);
  return ok ? r : 0;
}

// f = A op B: for ^ + - and * by an odd value, B's values follow from f's and A's and are looked up; for & and |, both
// operands are among the small expressions (supersets / subsets of f). The smallest result is returned.
u32 Oracle::split(Ctx& X, const u64* f, const u32* leaves) const {
  u64 need[ORA_K];
  int best = 1 << 30; u8 bop = 0; u32 bA = 0, bB = 0; bool swap = false;
  auto consider = [&](u32 ia, u8 op, bool sw) {
    int ib = find(need);
    if (ib < 0) return;
    int cost = C[ia].lvl + C[ib].lvl + 1;
    if (cost < best) { best = cost; bop = op; bA = ia; bB = (u32)ib; swap = sw; }
  };
  for (u32 ia = 1; ia < nVals; ia++) {
    if (C[ia].lvl + 1 >= best) continue;
    const u64* a = &V[(size_t)ia * ORA_K];
    for (int k = 0; k < ORA_K; k++) need[k] = (f[k] ^ a[k]) & m;
    consider(ia, 8, false);
    for (int k = 0; k < ORA_K; k++) need[k] = (f[k] - a[k]) & m;                   // f = A + B
    consider(ia, 4, false);
    for (int k = 0; k < ORA_K; k++) need[k] = (a[k] - f[k]) & m;                   // f = A - B
    consider(ia, 9, false);
    for (int k = 0; k < ORA_K; k++) need[k] = (f[k] + a[k]) & m;                   // f = B - A
    consider(ia, 9, true);
    bool odd = true; for (int k = 0; k < ORA_K && odd; k++) odd = a[k] & 1;
    if (odd && C[ia].op != 1) {
      for (int k = 0; k < ORA_K; k++) { u64 inv = a[k]; for (int t = 0; t < 6; t++) inv *= 2 - a[k] * inv; need[k] = (f[k] * inv) & m; }
      consider(ia, 5, false);
    }
  }
  // f = A & B (both contain f), f = A | B (both are contained in f)
  for (u8 op = 6; op <= 7; op++) {
    std::vector<u32> cand;
    for (u32 ia = 1; ia < nVals && cand.size() < 1500; ia++) {
      if (C[ia].op == 1) continue;
      const u64* a = &V[(size_t)ia * ORA_K]; bool ok = true;
      for (int k = 0; k < ORA_K && ok; k++) ok = op == 6 ? (f[k] & ~a[k]) == 0 : (a[k] & ~f[k]) == 0;
      if (ok) cand.push_back(ia);
    }
    for (size_t i = 0; i < cand.size(); i++) {
      const u64* a = &V[(size_t)cand[i] * ORA_K];
      if (C[cand[i]].lvl + 1 >= best) continue;
      for (size_t j = i + 1; j < cand.size(); j++) {
        const int cost = C[cand[i]].lvl + C[cand[j]].lvl + 1;
        if (cost >= best) continue;
        const u64* b = &V[(size_t)cand[j] * ORA_K]; bool ok = true;
        for (int k = 0; k < ORA_K && ok; k++) ok = ((op == 6 ? (a[k] & b[k]) : (a[k] | b[k])) & m) == f[k];
        if (ok) { best = cost; bop = op; bA = cand[i]; bB = cand[j]; swap = false; }
      }
    }
  }
  if (best == (1 << 30)) return 0;
  bool ok = true;
  u32 A = mk(X, bA, leaves, ok), B = mk(X, bB, leaves, ok);
  if (!ok) return 0;
  switch (bop) {
  case 8: return X.xor_(A, B); case 4: return X.add(A, B); case 5: return X.mul(A, B);
  case 6: return X.and_(A, B); case 7: return X.or_(A, B);
  default: return swap ? X.sub(B, A) : X.sub(A, B);
  }
}

}  // namespace unshroud
