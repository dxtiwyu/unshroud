// MBA simplifier on public data sets: lines "expression,groundtruth[,...]" in infix syntax (+ - * & | ^ ~ << and unary -,
// variables: letters, numbers decimal or 0x). Per line: nodes before / after / of the ground truth, exact (proved) or tested,
// the GAMBA criterion (expression - groundtruth simplifies to 0), a check of the result on random inputs.
//   unshroud_mbaset <file> [--limit N] [--skip N] [--width W] [--budget S] [--jsonl FILE] [--show] [--step K]
#include "../src/util.hpp"
#include "../src/mba.hpp"
#include "../src/solver.hpp"
#include <chrono>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <map>
#include <string>
using namespace unshroud;

namespace {
struct Parser {
  Ctx& X; unsigned w; const char* p; bool ok = true; std::map<std::string, u32>& vars;
  Parser(Ctx& X, unsigned w, const char* s, std::map<std::string, u32>& vars) : X(X), w(w), p(s), vars(vars) {}
  void ws() { while (*p == ' ' || *p == '\t') p++; }
  u32 atom() {
    ws();
    if (*p == '(') { p++; u32 r = orE(); ws(); if (*p == ')') p++; else ok = false; return r; }
    if (*p == '~') { p++; return X.not_(atom()); }
    if (*p == '-') { p++; return X.neg(atom()); }
    if (*p == '+') { p++; return atom(); }
    if (*p >= '0' && *p <= '9') { char* e; u64 v = strtoull(p, &e, 0); p = e; return X.cst(v & maskOf(w), w); }
    if ((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || *p == '_') {
      std::string n; while ((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || *p == '_' || (*p >= '0' && *p <= '9')) n += *p++;
      auto it = vars.find(n);
      if (it != vars.end()) return it->second;
      u64 seed = 0x9E3779B97F4A7C15ull * (vars.size() + 3) ^ 0x1234567;
      u32 v = X.var(n, w, seed & maskOf(w)); vars[n] = v; return v;
    }
    ok = false; return X.cst(0, w);
  }
  u32 mulE() { u32 r = atom(); for (;;) { ws(); if (*p == '*' && p[1] != '*') { p++; r = X.mul(r, atom()); } else return r; } }
  u32 addE() { u32 r = mulE(); for (;;) { ws(); if (*p == '+') { p++; r = X.add(r, mulE()); } else if (*p == '-') { p++; r = X.sub(r, mulE()); } else return r; } }
  u32 shE() { u32 r = addE(); for (;;) { ws(); if (*p == '<' && p[1] == '<') { p += 2; r = X.shl(r, addE()); } else if (*p == '>' && p[1] == '>') { p += 2; r = X.lshr(r, addE()); } else return r; } }
  u32 andE() { u32 r = shE(); for (;;) { ws(); if (*p == '&') { p++; r = X.and_(r, shE()); } else return r; } }
  u32 xorE() { u32 r = andE(); for (;;) { ws(); if (*p == '^') { p++; r = X.xor_(r, andE()); } else return r; } }
  u32 orE() { u32 r = xorE(); for (;;) { ws(); if (*p == '|') { p++; r = X.or_(r, xorE()); } else return r; } }
  u32 parse() { u32 r = orE(); ws(); if (*p) ok = false; return r; }
};
double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }
u64 rnd(u64& s) { s += 0x9E3779B97F4A7C15ull; u64 z = s; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull; z = (z ^ (z >> 27)) * 0x94D049BB133111EBull; return z ^ (z >> 31); }
}

int main(int argc, char** argv) {
  unshroud::limitMemory();
  if (argc < 2) { printf("usage: unshroud_mbaset <file> [--limit N] [--skip N] [--width W] [--budget S] [--jsonl FILE] [--show] [--step K]\n"); return 1; }
  size_t limit = ~(size_t)0, skip = 0, step = 1; unsigned w = 64; double budget = 1.0; const char* jsonl = nullptr; bool show = false; bool raw = false; bool wexpr = false;
  for (int i = 2; i < argc; i++) {
    if (!strcmp(argv[i], "--limit") && i + 1 < argc) limit = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--skip") && i + 1 < argc) skip = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--step") && i + 1 < argc) step = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--width") && i + 1 < argc) w = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--budget") && i + 1 < argc) budget = atof(argv[++i]);
    else if (!strcmp(argv[i], "--jsonl") && i + 1 < argc) jsonl = argv[++i];
    else if (!strcmp(argv[i], "--show")) show = true;
    else if (!strcmp(argv[i], "--raw")) raw = true;
    else if (!strcmp(argv[i], "--expr")) wexpr = true;   // the result expression in the jsonl ("r")
  }
  std::ifstream in(argv[1]);
  if (!in) { printf("cannot open %s\n", argv[1]); return 1; }
  FILE* jf = jsonl ? fopen(jsonl, "w") : nullptr;
  std::string line; size_t lineno = 0, done = 0, seen = 0;
  u64 nSolved = 0, nZero = 0, nExact = 0, nWrong = 0, nBad = 0, nSmaller = 0, nZeroExact = 0; double tAll = 0, tMax = 0; u64 sumIn = 0, sumOut = 0, sumGt = 0;
  while (std::getline(in, line)) {
    lineno++;
    if (line.empty() || line[0] == '#') continue;
    if (seen++ < skip || (seen - 1 - skip) % step) continue;
    if (done >= limit) break;
    // expression , groundtruth (the first two fields)
    size_t c1 = line.find(','); if (c1 == std::string::npos) { nBad++; continue; }
    size_t c2 = line.find(',', c1 + 1);
    std::string es = line.substr(0, c1), gs = line.substr(c1 + 1, c2 == std::string::npos ? std::string::npos : c2 - c1 - 1);
    while (!gs.empty() && (gs.back() == '\r' || gs.back() == '\n' || gs.back() == ' ')) gs.pop_back();
    // a context per expression: nothing learned from one line helps the next (each one is a problem of its own)
    Ctx X; Solver S(X); Mba M(X, &S); M.o.budget = budget;
    std::map<std::string, u32> vars;
    Parser pe(X, w, es.c_str(), vars); u32 e = pe.parse();
    Parser pg(X, w, gs.c_str(), vars); u32 g = pg.parse();
    if (!pe.ok || !pg.ok) { nBad++; if (show) printf("line %zu: parse error\n", lineno); continue; }
    const u32 nIn = X.countNodes(e), nGt = X.countNodes(g);
    const double t0 = now();
    u32 r = raw ? e : M.simplify(e);
    const bool exact = raw ? true : M.lastExact;
    const double dt = now() - t0;
    const u32 nOut = X.countNodes(r);
    // the GAMBA criterion: expression - groundtruth is 0
    const double t1 = now();
    u32 d = X.sub(e, g); u32 z = raw ? d : M.simplify(d);
    const bool zero = X.isC(z) && X.cv(z) == 0; const bool zeroExact = zero && (raw || M.lastExact);
    const double dz = now() - t1;
    // the result against the ground truth on random inputs
    bool wrong = false; u64 rs = 0x1234 + lineno;
    std::vector<u64> vals(X.vars.size());
    for (int k = 0; k < 200 && !wrong; k++) {
      for (auto& v : vals) { u64 x = rnd(rs); const int kind = (int)(rnd(rs) % 6); v = kind == 0 ? x & 0xff : kind == 1 ? ~(x & 0xff) : kind == 2 ? 1ull << (x & 63) : x; }
      if (X.eval(r, vals.data()) != X.eval(g, vals.data())) wrong = true;
    }
    const bool solved = !wrong && nOut <= nGt;
    done++; tAll += dt; if (dt > tMax) tMax = dt; sumIn += nIn; sumOut += nOut; sumGt += nGt;
    nSolved += solved; nZero += zero; nZeroExact += zeroExact; nExact += exact && !wrong; nWrong += wrong; nSmaller += !wrong && nOut < nIn;
    if (show || wrong) printf("line %zu: %u -> %u nodes (truth %u) %s%s%s  %.3fs / %.3fs   %s\n", lineno, nIn, nOut, nGt, wrong ? "WRONG " : solved ? "solved " : "", exact ? "exact " : "tested ", zero ? "zero" : "", dt, dz, X.str(r, 6).c_str());
    if (jf) fprintf(jf, "{\"line\":%zu,\"in\":%u,\"out\":%u,\"gt\":%u,\"solved\":%d,\"zero\":%d,\"zeroExact\":%d,\"exact\":%d,\"wrong\":%d,\"t\":%.5f,\"tz\":%.5f%s}\n", lineno, nIn, nOut, nGt, (int)solved, (int)zero, (int)zeroExact, (int)exact, (int)wrong, dt, dz, wexpr ? (",\"r\":\"" + X.str(r, 1 << 30) + "\"").c_str() : "");
  }
  if (jf) fclose(jf);
  printf("%s: %zu expressions  solved(size<=truth) %llu (%.1f%%)  zero(e-gt=0) %llu (%.1f%%)  zero proved %llu (%.1f%%)  result proved %llu (%.1f%%)  wrong %llu  parse errors %llu  nodes in %.1f out %.1f truth %.1f  time total %.2fs max %.3fs\n",
         argv[1], done, (unsigned long long)nSolved, 100.0 * nSolved / std::max<size_t>(1, done), (unsigned long long)nZero, 100.0 * nZero / std::max<size_t>(1, done),
         (unsigned long long)nZeroExact, 100.0 * nZeroExact / std::max<size_t>(1, done), (unsigned long long)nExact, 100.0 * nExact / std::max<size_t>(1, done),
         (unsigned long long)nWrong, (unsigned long long)nBad, (double)sumIn / std::max<size_t>(1, done), (double)sumOut / std::max<size_t>(1, done), (double)sumGt / std::max<size_t>(1, done), tAll, tMax);
  return 0;
}
