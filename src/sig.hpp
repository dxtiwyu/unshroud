// unshroud - signatures: the values of expressions on fixed test assignments, and a table of every small expression by its values.
// Two expressions with the same signature are (very probably) the same function: the simplifier finds what a node is
// equal to by looking its values up, instead of matching rewrite rules against its shape.
#pragma once
#include "expr.hpp"
#include <unordered_map>
#include <vector>

namespace unshroud {

enum { SIG_K = 64, ORA_K = 16, ORA_LEAVES = 4 };

// value of table leaf i on test k (k < SIG_K; the tables use the first ORA_K)
u64 oracleTest(int leaf, int k);

// value of variable i on test k of a flavor (0: uniform, 1: sparse / small / dense)
u64 sigTestValue(u64 var, int k, int flavor);
// values of nodes (true semantics, comparisons included) on n assignments: out[r * n + k]; varVal(variable, k)
void evalBatch(Ctx& X, const u32* roots, int nroots, int n, u64 (*varVal)(void*, u32, int), void* ud, u64* out);

// op on n values at once
void evalVec(u8 op, unsigned w, unsigned lo, u64 k, const u64* a, const u64* b, const u64* c, u64* out, int n);

// Values of nodes on SIG_K assignments of the variables (variables 0..3: the oracle's leaves). Comparisons are free:
// each has random bits of its own, so that nothing found here depends on what a comparison computes (a condition
// which holds for one input in 2^64 is never taken for a constant).
class Sigs {
public:
  // flavor 0: uniform random values (and the oracle's leaves); 1: sparse, small and dense values (what uniform values rarely show)
  explicit Sigs(Ctx& X, int flavor = 0) : X(X), flavor(flavor) {}
  ~Sigs();
  const u64* of(u32 id) { if (id < idx.size() && idx[id]) return slotPtr(idx[id] - 1); compute(id); return slotPtr(idx[id] - 1); }
  u64 hash(u32 id) { of(id); return hashes[idx[id] - 1]; }
  bool same(u32 a, u32 b) { if (a == b) return true; if (X.W(a) != X.W(b) || hash(a) != hash(b)) return false; return memcmp(of(a), of(b), SIG_K * sizeof(u64)) == 0; }
  bool isConst(u32 id, u64& v) { const u64* s = of(id); for (int k = 1; k < SIG_K; k++) if (s[k] != s[0]) return false; v = s[0]; return true; }
  // A node with the same value on every test which is not a constant by its structure is *suspect*: a real constant
  // (an opaque expression) or a condition which almost never holds - the tests cannot tell. Its signature is made of free
  // values (nothing found by tests may rest on it), and it is listed here with the value seen, for whoever can prove it.
  bool suspect(u32 id, u64& v) { of(id); auto it = suspects.find(id); if (it == suspects.end()) return false; v = it->second; return true; }
  bool isSuspect(u32 id) { of(id); return suspects.count(id) != 0; }
  // Can the node take a value for very few inputs only (so that tests would not see it)? Below it, a bit above the lowest
  // is read out of a sum or a product (a carry decides it), or there is a comparison, a division, a count of bits.
  // Sums, products and bitwise operations of whole values do not do that: there, "the same on every test" is trusted.
  bool narrow(u32 id) { of(id); return flg[idx[id] - 1] & 2; }
  size_t count() const { return n; }
  size_t maxCount = 120000;              // 512 bytes each
  bool full() const { return n >= maxCount; }
private:
  Ctx& X; int flavor;
  std::vector<u32> idx;                  // node -> slot + 1
  std::vector<u64*> chunks;              // 1024 signatures each
  std::vector<u64> hashes;
  std::vector<u8> flg;                   // 1: arithmetic below, 2: narrow (see narrow())
  std::unordered_map<u32, u64> suspects;
  size_t n = 0;
  u64* slotPtr(u32 s) { return chunks[s >> 10] + (size_t)(s & 1023) * SIG_K; }
  void compute(u32 id);
};

// Every expression of at most `levels` operations (+ - * & | ^ ~ neg, width w) over four leaves and the constants 1, -1, 2,
// by its values on the ORA_K tests: one per function.
class Oracle {
public:
  static const Oracle& get(unsigned w);  // built on first use
  // the table's expression with these ORA_K values, over leaves[0..3] (nodes of width w; 0: no such leaf), or 0
  u32 lookup(Ctx& X, const u64* vals, const u32* leaves) const;
  // A op B, A among the small expressions, B in the table (and A & B, A | B among the small ones): the smallest found, or 0
  u32 split(Ctx& X, const u64* vals, const u32* leaves) const;
  // A op B where B is given by its values and its node (anything), A in the table
  size_t entries() const { return C.size(); }
  double buildSeconds = 0;
private:
  struct Cand { u8 op, lvl; u32 a, b; };
  unsigned w = 64; u64 m = ~0ull; int levels = 3;
  std::vector<Cand> C;
  std::vector<u64> V;                    // ORA_K values of the candidates below the last level
  u32 nVals = 0;                         // candidates which have their values in V
  std::vector<u64> tab; u64 tmask = 0;   // (hash tag << 32) | (index + 1)
  void build(unsigned w);
  int find(const u64* v) const;
  bool insert(const u64* v, const Cand& c, bool keepVals);
  u32 mk(Ctx& X, u32 i, const u32* leaves, bool& ok) const;
};

}  // namespace unshroud
