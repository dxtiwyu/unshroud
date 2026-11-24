// Soundness of the cheap stages of the resolver: random constraints which hold for known inputs must never be found
// unsatisfiable (modular proof, simplification, lemmas, local search - no SMT). usage: t_mod [rounds] [seed]
#include "../src/util.hpp"
#include "../src/solver.hpp"
#include <cstdio>
#include <random>
using namespace unshroud;

int main(int argc, char** argv) {
  unshroud::limitMemory();
  int rounds = argc > 1 ? atoi(argv[1]) : 20000; u64 seed = argc > 2 ? strtoull(argv[2], nullptr, 0) : 1;
  std::mt19937_64 rng(seed);
  u64 wrong = 0, unsat = 0, sat = 0, unknown = 0, modUnsat = 0;
  for (int round = 0; round < rounds; round++) {
    Ctx X; Solver S(X);
    std::vector<u64> vals;
    std::vector<u32> pool;
    const unsigned vw = rng() % 4 == 0 ? 8 : 64;
    for (int i = 0; i < 3; i++) { u64 v = rng() % 5 == 0 ? rng() % 4 : rng(); v &= maskOf(vw); vals.push_back(v); u32 n = X.var(std::string(1, "xyz"[i]), vw, v); pool.push_back(vw == 64 ? n : X.zext(n, 64)); }
    auto pick = [&]() { return pool[rng() % pool.size()]; };
    auto K = [&]() { static const u64 ks[] = {1, 2, 3, 7, 8, 0xff, 100, 0x8000000000000000ull}; return X.cst(rng() % 3 ? ks[rng() % 8] : rng(), 64); };
    int steps = 2 + (int)(rng() % 8);
    for (int i = 0; i < steps; i++) {
      u32 a = pick(), b = rng() % 3 ? pick() : K(), r;
      switch ((int)(rng() % 20)) {
      case 0: r = X.add(a, b); break; case 1: r = X.sub(a, b); break; case 2: r = X.mul(a, b); break; case 3: r = X.mul(a, a); break;
      case 4: r = X.and_(a, b); break; case 5: r = X.or_(a, b); break; case 6: r = X.xor_(a, b); break; case 7: r = X.not_(a); break;
      case 8: r = X.shl(a, X.cst(rng() % 64, 64)); break; case 9: r = X.lshr(a, X.cst(rng() % 64, 64)); break;
      case 10: r = X.rol(a, X.cst(rng() % 64, 64)); break; case 11: r = X.udiv(a, K()); break; case 12: r = X.urem(a, K()); break;
      case 13: r = X.zext(X.ult(a, b), 64); break; case 14: r = X.zext(X.eq(a, b), 64); break;
      case 15: r = X.zext(X.extract(a, (unsigned)(rng() % 32), 16), 64); break; case 16: r = X.mulhu(a, b); break;
      case 17: r = X.ite(X.extract(a, (unsigned)(rng() % 64), 1), b, X.neg(b)); break;
      case 18: r = rng() % 2 ? X.ashr(a, X.cst(rng() % 64, 64)) : X.udiv(K(), a); break;     // (a constant divided by a value: overflow checks)
      default: r = X.mul(a, X.add(a, X.cst(1, 64))); break;
      }
      pool.push_back(r);
    }
    // constraints which hold for the inputs
    std::vector<u32> conds;
    int nc = 1 + (int)(rng() % 3);
    for (int i = 0; i < nc; i++) {
      u32 e = pool[pool.size() - 1 - (rng() % std::min<size_t>(pool.size(), 4))], f = pick();
      const u64 ve = X.eval(e, vals.data()), vf = X.eval(f, vals.data());
      u32 c;
      switch ((int)(rng() % 6)) {
      case 5: {      // several bounds on one expression, and values ruled out around them (what a loop leaves)
        const u64 d1 = rng() % 40, d2 = 1 + rng() % 40;
        if (ve >= d1) conds.push_back(X.ule(X.cst(ve - d1, 64), e));
        if (ve >= d1 + 3) conds.push_back(X.ult(X.cst(ve - d1 - 3, 64), e));
        if (ve + d2 > ve) conds.push_back(X.ult(e, X.cst(ve + d2, 64)));
        if (ve + d2 + 5 > ve) conds.push_back(X.ule(e, X.cst(ve + d2 + 5, 64)));
        c = X.ne(e, X.cst(ve + 1 + rng() % 100, 64));
        break;
      }
      case 0: c = X.eq(e, X.cst(ve, 64)); break;
      case 1: c = X.eq(X.and_(e, X.cst(maskOf(1 + (unsigned)(rng() % 12)), 64)), X.and_(X.cst(ve, 64), X.cst(maskOf(12), 64))); c = X.eval(c, vals.data()) & 1 ? c : X.not_(c); break;
      case 2: if (rng() % 3 == 0) { u32 q = X.udiv(X.cst(~0ull - (rng() % 64), 64), e); const u64 vq = X.eval(q, vals.data()); c = vf <= vq ? X.ule(f, q) : X.ult(q, f); break; }   // z <= K / y, K / y < z
              c = ve < vf ? X.ult(e, f) : X.ule(f, e); break;
      case 3: c = ve == vf ? X.eq(e, f) : X.ne(e, f); break;
      default: c = X.eq(X.sub(e, f), X.cst(ve - vf, 64)); break;
      }
      conds.push_back(c);
      for (u32 cc : conds) if (!(X.eval(cc, vals.data()) & 1)) { printf("test bug: constraint does not hold: %s%c", X.str(cc, 8).c_str(), 10); return 2; }
    }
    std::vector<u32> flat;
    if (!flattenConds(X, conds, flat)) { wrong++; if (wrong <= 5) printf("WRONG (round %d): a constraint which holds was folded to false: %s%c", round, X.str(conds[0], 9).c_str(), 10); continue; }
    if (!flat.empty() && S.modular(flat, 8, 20) == SR_UNSAT) { modUnsat++; wrong++; if (wrong <= 5) { printf("WRONG (round %d): modular proof of a satisfiable query:%c", round, 10); for (u32 c : flat) printf("   %s%c", X.str(c, 9).c_str(), 10); } continue; }
    // the pipeline without the SMT solver, from other inputs
    SolveOptions o; o.smt = false; o.lsBudget = 300; o.timeoutMs = 2000;
    std::vector<u64> other(vals.size()), model;
    for (auto& v : other) v = rng() & maskOf(vw);
    const char* stage = "";
    SatResult r = S.check({}, conds, other, &model, o, &stage);
    if (r == SR_UNSAT) { unsat++; wrong++; if (wrong <= 5) { printf("WRONG (round %d): unsat by %s for a satisfiable query:%c", round, stage, 10); for (u32 c : conds) printf("   %s%c", X.str(c, 9).c_str(), 10); } }
    else if (r == SR_SAT) { sat++; for (u32 c : conds) if (!(X.eval(c, model.data()) & 1)) { wrong++; if (wrong <= 5) printf("WRONG (round %d): model by %s does not satisfy %s%c", round, stage, X.str(c, 9).c_str(), 10); break; } }
    else unknown++;
  }
  printf("%d rounds of satisfiable queries: sat %llu, unknown %llu, wrongly unsat %llu (modular %llu)%c%s: %llu wrong%c", rounds, (unsigned long long)sat, (unsigned long long)unknown,
         (unsigned long long)unsat + (unsigned long long)modUnsat, (unsigned long long)modUnsat, 10, wrong ? "FAILED" : "ok", (unsigned long long)wrong, 10);
  return wrong ? 1 : 0;
}
