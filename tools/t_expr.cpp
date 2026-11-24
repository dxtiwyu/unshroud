// Random expressions built through the simplifying constructors, every rule checked on random values (UNSHROUD_CHECK).
#include "../src/util.hpp"
#include "../src/expr.hpp"
#include <chrono>
#include <intrin.h>
#include <cstdio>
#include <random>
using namespace unshroud;

int main(int argc, char** argv) {
  unshroud::limitMemory();
  int rounds = argc > 1 ? atoi(argv[1]) : 20000;
  Ctx X; X.check = true;
  std::mt19937_64 rng(argc > 2 ? atoll(argv[2]) : 1);
  const unsigned widths[] = {1, 8, 16, 32, 64};
  std::vector<u32> pool[65];
  for (unsigned w : widths) {
    for (int i = 0; i < 3; i++) pool[w].push_back(X.var("v" + std::to_string(w) + "_" + std::to_string(i), w, rng()));
    for (u64 c : {0ull, 1ull, 2ull, ~0ull, 0x80ull, 0xffull, 0x8000000000000000ull, 0x1234567ull}) pool[w].push_back(X.cst(c, w));
  }
  auto pick = [&](unsigned w) { auto& p = pool[w]; return p[rng() % p.size()]; };
  auto t0 = std::chrono::steady_clock::now();
  for (int i = 0; i < rounds; i++) {
    unsigned w = widths[1 + rng() % 4];
    if (rng() % 8 == 0) w = 1;
    u32 a = pick(w), b = pick(w), c = pick(1), r = 0;
    switch ((int)(rng() % 30)) {
    case 0: r = X.add(a, b); break; case 1: r = X.sub(a, b); break; case 2: r = X.mul(a, b); break; case 3: r = X.neg(a); break;
    case 4: r = X.and_(a, b); break; case 5: r = X.or_(a, b); break; case 6: r = X.xor_(a, b); break; case 7: r = X.not_(a); break;
    case 8: r = X.shl(a, X.cst(rng() % (w + 2), w)); break; case 9: r = X.lshr(a, X.cst(rng() % (w + 2), w)); break;
    case 10: r = X.ashr(a, X.cst(rng() % (w + 2), w)); break; case 11: r = X.rol(a, X.cst(rng() % (2 * w), w)); break;
    case 12: r = X.ror(a, X.cst(rng() % (2 * w), w)); break;
    case 13: if (w > 1) { unsigned lo = (unsigned)(rng() % w), n = 1 + (unsigned)(rng() % (w - lo)); r = X.extract(a, lo, n); } break;
    case 14: if (w < 64) { unsigned to = w + 1 + (unsigned)(rng() % (64 - w)); r = X.zext(a, to); } break;
    case 15: if (w < 64) { unsigned to = w + 1 + (unsigned)(rng() % (64 - w)); r = X.sext(a, to); } break;
    case 16: if (w <= 32) { unsigned w2 = widths[rng() % 4]; if (w + w2 <= 64) r = X.concat(a, pick(w2)); } break;
    case 17: r = X.ite(c, a, b); break;
    case 18: r = X.eq(a, b); break; case 19: r = X.ult(a, b); break; case 20: r = X.ule(a, b); break;
    case 21: r = X.slt(a, b); break; case 22: r = X.sle(a, b); break;
    case 23: r = X.udiv(a, b); break; case 24: r = X.urem(a, b); break; case 25: r = X.sdiv(a, b); break; case 26: r = X.srem(a, b); break;
    case 27: r = X.mulhu(a, b); break; case 28: r = X.mulhs(a, b); break;
    case 29: r = X.eq(X.add(a, X.cst(rng(), w)), X.cst(rng() % 4, w)); break;
    }
    if (r && X.N(r).size < 200) { auto& p = pool[X.W(r)]; p.push_back(r); if (p.size() > 400) p.erase(p.begin() + 11 + rng() % 380); }
  }
  // division rules, where a boundary off by one would hide from random values: every value of an 8-bit input
  {
    Ctx Y; u32 y = Y.var("y", 8, 0); u64 bad = 0, n = 0;
    auto all = [&](u32 e, auto ref) { for (u64 v = 0; v < 256; v++) { u64 got = Y.eval(e, &v); n++; if (got != ref(v)) { if (!bad++) fprintf(stderr, "division rule: %s at y=%llu: got %llu want %llu\n", Y.str(e).c_str(), (unsigned long long)v, (unsigned long long)got, (unsigned long long)ref(v)); } } };
    for (u64 d : {2, 3, 5, 7, 10, 16, 25, 100, 127, 128, 200, 255}) {
      u32 q = Y.udiv(y, Y.cst(d, 8));
      for (u64 c = 0; c < 256; c++) {
        u32 C = Y.cst(c, 8);
        all(Y.ult(C, q), [&](u64 v) { return (u64)(c < v / d); });
        all(Y.ult(q, C), [&](u64 v) { return (u64)(v / d < c); });
        all(Y.ule(C, q), [&](u64 v) { return (u64)(c <= v / d); });
        all(Y.ule(q, C), [&](u64 v) { return (u64)(v / d <= c); });
        all(Y.eq(q, C), [&](u64 v) { return (u64)(v / d == c); });
      }
      for (u64 d2 : {2, 3, 7, 10, 100, 255}) all(Y.udiv(q, Y.cst(d2, 8)), [&](u64 v) { return v / d / d2; });
      for (unsigned k = 1; k < 8; k++) {
        all(Y.udiv(Y.lshr(y, Y.cst(k, 8)), Y.cst(d, 8)), [&](u64 v) { return (v >> k) / d; });
        all(Y.lshr(q, Y.cst(k, 8)), [&](u64 v) { return (v / d) >> k; });
        all(Y.zext(Y.extract(q, k, 8 - k), 8), [&](u64 v) { return (v / d) >> k; });
      }
      all(Y.sub(y, Y.mul(q, Y.cst(d, 8))), [&](u64 v) { return v % d; });
      for (u64 d2 : {2, 3, 5, 10}) if (d * d2 < 256) {     // a digit: y/d - d2 * (y/(d*d2)) = (y/d) % d2, also on the low bits
        all(Y.sub(q, Y.mul(Y.udiv(q, Y.cst(d2, 8)), Y.cst(d2, 8))), [&](u64 v) { return (v / d) % d2; });
        all(Y.sub(Y.extract(q, 0, 4), Y.mul(Y.extract(Y.udiv(y, Y.cst(d * d2, 8)), 0, 4), Y.cst(d2, 4))), [&](u64 v) { return ((v / d) % d2) & 15; });
      }
      for (u64 c = 0; c < 256; c++) all(Y.eq(Y.urem(y, Y.cst(d, 8)), Y.cst(c, 8)), [&](u64 v) { return (u64)(v % d == c); });
    }
    for (u64 c = 0; c < 256; c++) {                       // squares
      all(Y.eq(Y.mul(y, y), Y.cst(c, 8)), [&](u64 v) { return (u64)(((v * v) & 255) == c); });
      u32 t = Y.add(Y.mul(y, Y.cst(3, 8)), Y.cst(5, 8));
      all(Y.eq(Y.mul(t, t), Y.cst(c, 8)), [&](u64 v) { u64 q = (v * 3 + 5) & 255; return (u64)(((q * q) & 255) == c); });
    }
    // magic numbers: the quotient by 3..999 of a 64-bit value, as compilers write it (with and without a shift before)
    Ctx Z; u32 z = Z.var("z", 64, 0); std::mt19937_64 r2(99); u64 recognized = 0, forms = 0;
    for (u64 d = 3; d < 1000; d += (d < 40 ? 1 : 37)) {
      for (unsigned pre = 0; pre < 4; pre++) {
        if (pre && (d & ((1ull << pre) - 1))) continue;
        const u64 dd = d >> pre; if (dd < 3 || !(dd & (dd - 1))) continue;
        unsigned l = 64 - (unsigned)__lzcnt64(dd - 1);                       // ceil(log2 dd)
        // M = ceil(2^(64+l-pre... ) / dd) must fit 64 bits: usable when the input has `pre` zero bits on top
        unsigned sh = l; while (sh > 0 && (1ull << sh) >= dd) sh--;
        if ((1ull << sh) >= dd) continue;
        u64 rem = 1ull << sh, q0 = 0;                                    // floor(2^(64+sh) / dd), by long division
        for (int i = 63; i >= 0; i--) { const bool top = rem >> 63; rem <<= 1; if (top || rem >= dd) { rem -= dd; q0 |= 1ull << i; } }
        if (q0 == ~0ull) continue;
        const u64 M128 = q0 + 1;
        // valid for inputs below 2^(64-pre) when M*dd - 2^(64+sh) = dd - rem <= 2^(sh+pre)
        if (sh + pre < 64 && dd - rem > (1ull << (sh + pre))) continue;
        u32 in = pre ? Z.lshr(z, Z.cst(pre, 64)) : z;
        u32 e = Z.lshr(Z.mulhu(in, Z.cst(M128, 64)), Z.cst(sh, 64));
        forms++; if (Z.N(e).op == O_UDIV) recognized++;
        for (int k = 0; k < 4000; k++) {
          u64 v = r2(); int kind = k % 6;
          if (kind == 1) v = (r2() % 100000) * d + (r2() % 3) - 1; else if (kind == 2) v = ~0ull - (r2() % 2000); else if (kind == 3) v = (v / d) * d - (r2() % 2); else if (kind == 4) v >>= (r2() % 60);
          u64 got = Z.eval(e, &v); n++;
          if (got != v / d) { if (!bad++) fprintf(stderr, "magic division by %llu (shift %u before): %s at %llx: got %llx want %llx\n", (unsigned long long)d, pre, Z.str(e).c_str(), (unsigned long long)v, (unsigned long long)got, (unsigned long long)(v / d)); }
        }
      }
    }
    printf("division rules: %llu evaluations, %llu of %llu magic forms recognized as divisions, %llu wrong\n", (unsigned long long)n, (unsigned long long)recognized, (unsigned long long)forms, (unsigned long long)bad);
    if (bad) return 1;
  }
  double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  printf("ok: %d rounds, %zu nodes, %llu checks, %.2fs\n", rounds, X.n.size(), (unsigned long long)X.checks, dt);
  return 0;
}
