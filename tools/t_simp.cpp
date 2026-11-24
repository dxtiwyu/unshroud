// Stress test of the simplifier: random expressions (arithmetic, masks, shifts, flag tricks) wrapped in MBA identities are
// simplified; every result is compared with the original on many assignments and given to Bitwuzla for a proof or a
// counterexample. usage: t_simp [rounds] [seed] [proof ms]
#include "../src/util.hpp"
#include "../src/mba.hpp"
#include "../src/sig.hpp"
#include "../src/solver.hpp"
#include <chrono>
#include <cstdio>
#include <random>
using namespace unshroud;

static u64 rv(void* ud, u32 var, int k) { std::mt19937_64 g(((u64)var << 32) ^ (u64)k ^ *(u64*)ud); u64 r = g(); int kind = (int)(g() % 8);
  return kind == 0 ? 0 : kind == 1 ? ~0ull : kind == 2 ? r & 0xff : kind == 3 ? 1ull << (r & 63) : kind == 4 ? ~(1ull << (r & 63)) : kind == 5 ? r >> 40 : r; }

int main(int argc, char** argv) {
  unshroud::limitMemory();
  int rounds = argc > 1 ? atoi(argv[1]) : 2000; u64 seed = argc > 2 ? strtoull(argv[2], nullptr, 0) : 1; u32 proofMs = argc > 3 ? atoi(argv[3]) : 150;
  int only = argc > 4 ? atoi(argv[4]) : -1;
  std::mt19937_64 rng(seed);
  u64 simplified = 0, smaller = 0, wrong = 0, proved = 0, refuted = 0, unknown = 0, exactClaims = 0, exactWrong = 0, nodes0 = 0, nodes1 = 0, polyPairs = 0, polyEqual = 0, polyWrong = 0, takenBack = 0, takenBackFinal = 0, verifiedFinal = 0, unverifiedFinal = 0; double tsimp = 0;
  for (int round = 0; round < rounds; round++) {
    Ctx X; Solver S(X); Mba M(X, &S); M.o.budget = 2.0;
    if (const char* e = getenv("UNSHROUD_VERIFY_MS")) M.o.verifyMs = (u32)atoi(e);
    u32 v[4]; for (int i = 0; i < 4; i++) v[i] = X.var(std::string(1, "xyzw"[i]), 64, rng());
    std::vector<u32> pool(v, v + 4);
    auto pick = [&]() { return pool[rng() % pool.size()]; };
    auto K = [&]() { static const u64 ks[] = {1, 2, 3, 0xff, 0xffff, 0x8000000000000000ull, 0xffffffffull}; return X.cst(rng() % 3 ? ks[rng() % 7] : rng(), 64); };
    // an MBA form of a op b
    auto mba = [&](int op, u32 a, u32 b) -> u32 {
      switch (op * 3 + (int)(rng() % 3)) {
      case 0: return X.add(X.xor_(a, b), X.mul(X.and_(a, b), X.cst(2, 64)));
      case 1: return X.sub(X.add(X.or_(a, b), X.and_(a, b)), X.cst(0, 64));
      case 2: return X.sub(X.mul(X.or_(a, b), X.cst(2, 64)), X.xor_(a, b));
      case 3: return X.sub(X.or_(a, b), X.and_(a, b));                                             // xor
      case 4: return X.add(X.and_(a, X.not_(b)), X.and_(X.not_(a), b));
      case 5: return X.sub(X.add(a, b), X.mul(X.and_(a, b), X.cst(2, 64)));
      case 6: return X.add(X.xor_(a, X.not_(b)), X.add(X.mul(X.and_(a, X.not_(b)), X.cst(2, 64)), X.cst(1, 64)));   // sub
      case 7: return X.sub(X.xor_(a, b), X.mul(X.and_(X.not_(a), b), X.cst(2, 64)));
      case 8: return X.sub(X.and_(a, X.not_(b)), X.and_(X.not_(a), b));
      case 9: return X.sub(X.add(a, b), X.or_(a, b));                                              // and
      case 10: return X.sub(X.or_(a, b), X.xor_(a, b));
      case 11: return X.not_(X.or_(X.not_(a), X.not_(b)));
      case 12: return X.add(X.and_(a, b), X.xor_(a, b));                                           // or
      case 13: return X.sub(X.add(a, b), X.and_(a, b));
      case 14: return X.add(X.and_(a, X.not_(b)), b);
      default: return X.add(X.mul(X.and_(a, b), X.or_(a, b)), X.mul(X.and_(a, X.not_(b)), X.and_(X.not_(a), b)));   // mul
      }
    };
    int steps = 3 + (int)(rng() % 10);
    for (int i = 0; i < steps; i++) {
      u32 a = pick(), b = rng() % 4 ? pick() : K(), r;
      switch ((int)(rng() % 16)) {
      case 0: case 1: r = mba(0, a, b); break; case 2: case 3: r = mba(1, a, b); break; case 4: r = mba(2, a, b); break;
      case 5: r = mba(3, a, b); break; case 6: r = mba(4, a, b); break; case 7: r = mba(5, a, b); break;
      case 8: r = X.shl(a, X.cst(rng() % 64, 64)); break; case 9: r = X.lshr(a, X.cst(rng() % 64, 64)); break;
      case 10: r = X.and_(a, K()); break; case 11: r = X.or_(a, X.shl(b, X.cst(32 + rng() % 30, 64))); break;
      case 12: { u32 d = X.sub(a, b); r = X.xor_(X.lshr(X.or_(d, X.neg(d)), X.cst(63, 64)), X.cst(1, 64)); break; }   // a == b by arithmetic
      case 13: { u32 d = X.sub(a, b); r = X.lshr(X.or_(X.and_(X.not_(a), b), X.and_(X.not_(X.xor_(a, b)), d)), X.cst(63, 64)); break; }   // a < b by arithmetic
      case 14: r = X.mul(a, b); break;
      default: r = X.add(a, X.mul(b, K())); break;
      }
      pool.push_back(r);
    }
    u32 e = pool.back();
    if (!X.sym(e)) continue;
    // the polynomial prover on pairs which are almost always different (two entries of the pool, an entry with a constant
    // changed): whatever it calls equal must be equal on every test, and not refuted by the solver
    for (int t = 0; t < 12; t++) {
      u32 a = pick(), b = t % 3 == 0 ? X.add(a, X.cst(1ull << (rng() % 64), 64)) : t % 3 == 1 ? X.xor_(pick(), X.and_(a, K())) : pick();
      if (a == b) continue;
      polyPairs++;
      if (!M.provePoly(a, b)) continue;
      polyEqual++;
      const int n = 512; std::vector<u64> out(2 * n); u32 roots[2] = {a, b}; u64 sd = seed * 7919 + round * 13 + t;
      evalBatch(X, roots, 2, n, rv, &sd, out.data());
      bool bad = memcmp(out.data(), out.data() + n, sizeof(u64) * n) != 0;
      if (!bad) { std::vector<u64> model; SolveOptions so; so.timeoutMs = 100; so.simplify = false; so.modular = false; if (S.check({}, {X.ne(a, b)}, std::vector<u64>(X.vars.size(), 0), &model, so) == SR_SAT) bad = true; }
      if (bad) { polyWrong++; wrong++; if (polyWrong <= 3) printf("POLY WRONG: %s%c   ==  %s%c", X.str(a, 9).c_str(), 10, X.str(b, 9).c_str(), 10); }
    }
    if (only >= 0 && round != only) continue;
    if (only >= 0) { X.check = true; printf("expression: %s\n", X.str(e, 14).c_str()); }
    auto t0 = std::chrono::steady_clock::now();
    u32 r = M.simplify(e);
    tsimp += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    nodes0 += X.countNodes(e); nodes1 += X.countNodes(r); takenBack += M.st.refuted; takenBackFinal += M.st.refutedFinal; verifiedFinal += M.st.verified; unverifiedFinal += M.st.unverified;
    if (r == e) continue;
    simplified++; if (X.countNodes(r) < X.countNodes(e)) smaller++;
    if (M.lastExact) exactClaims++;
    const int n = 2048; std::vector<u64> out(2 * n); u32 roots[2] = {e, r}; u64 sd = seed * 1000003 + round;
    evalBatch(X, roots, 2, n, rv, &sd, out.data());
    bool bad = memcmp(out.data(), out.data() + n, sizeof(u64) * n) != 0;
    std::vector<u64> model; SolveOptions so; so.timeoutMs = proofMs; so.simplify = false; so.localSearch = true; so.modular = false;
    SatResult pr = S.check({}, {X.ne(e, r)}, std::vector<u64>(X.vars.size(), 0), &model, so);
    if (pr == SR_UNSAT) proved++; else if (pr == SR_SAT) { refuted++; bad = true; } else unknown++;
    if (bad) {
      wrong++; if (M.lastExact) exactWrong++;
      if (wrong <= 5) printf("WRONG (round %d, %s): %s\n   ->  %s\n", round, M.lastExact ? "claimed exact" : "tested", X.str(e, 9).c_str(), X.str(r, 9).c_str());
    }
  }
  printf("%d rounds: %llu simplified (%llu smaller), nodes %llu -> %llu, %.2fs in simplify\n", rounds, (unsigned long long)simplified, (unsigned long long)smaller, (unsigned long long)nodes0, (unsigned long long)nodes1, tsimp);
  printf("checked against Bitwuzla (%u ms each): proved %llu, counterexample %llu, undecided %llu; results claimed exact: %llu (wrong among them: %llu)\n", proofMs,
         (unsigned long long)proved, (unsigned long long)refuted, (unsigned long long)unknown, (unsigned long long)exactClaims, (unsigned long long)exactWrong);
  printf("polynomial prover on %llu pairs of pool entries: called %llu equal, %llu of them wrong%c", (unsigned long long)polyPairs, (unsigned long long)polyEqual, (unsigned long long)polyWrong, 10);
  printf("the simplifier's own check: results it had to take back %llu\n", (unsigned long long)takenBack);
  printf("   of which by the check of the whole result: %llu (it proved %llu results, left %llu undecided)%c", (unsigned long long)takenBackFinal, (unsigned long long)verifiedFinal, (unsigned long long)unverifiedFinal, 10);
  printf("%s: %llu wrong\n", wrong ? "FAILED" : "ok", (unsigned long long)wrong);
  return wrong ? 1 : 0;
}
