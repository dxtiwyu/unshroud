// Oracle table checks: build time, probe cost, split cost.
#include "../src/sig.hpp"
#include <chrono>
#include <cstdio>
#include <random>
using namespace unshroud;
static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }
int main(int argc, char** argv) {
  unsigned w = argc > 1 ? atoi(argv[1]) : 64;
  double t0 = now();
  const Oracle& O = Oracle::get(w);
  printf("build w=%u: %zu entries, %.3fs\n", w, O.entries(), now() - t0);
  Ctx X; u32 lv[4];
  for (int i = 0; i < 4; i++) lv[i] = X.var(std::string(1, "xyzw"[i]), w, i + 1);
  std::mt19937_64 rng(1);
  u64 v[ORA_K]; u64 hits = 0;
  t0 = now();
  const int N = 2000000;
  for (int i = 0; i < N; i++) { for (int k = 0; k < ORA_K; k++) v[k] = rng() & maskOf(w); hits += O.lookup(X, v, lv) != 0; }
  double dt = now() - t0;
  printf("random lookups: %.1f ns each (%llu hits)\n", dt / N * 1e9, (unsigned long long)hits);
  // a target: ((x + y) ^ z) * (w | x) + (y & z)
  for (int rep = 0; rep < 3; rep++) {
    for (int k = 0; k < ORA_K; k++) { u64 x = oracleTest(0, k), y = oracleTest(1, k), z = oracleTest(2, k), ww = oracleTest(3, k);
      v[k] = (rep == 0 ? (((x + y) ^ z) * (ww | x) + (y & z)) : rep == 1 ? ((x ^ y) + (z & ww)) * 3 + x : rng()) & maskOf(w); }
    t0 = now(); u32 r = 0;
    for (int i = 0; i < 20; i++) r = O.split(X, v, lv);
    printf("split %d: %.3f ms each -> %s\n", rep, (now() - t0) / 20 * 1e3, r ? X.str(r, 10).c_str() : "none");
  }
  return 0;
}
