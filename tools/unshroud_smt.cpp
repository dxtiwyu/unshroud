// Resolver benchmark on SMT-LIB queries: unshroud_smt [--timeout ms] [--no-ls] [--no-mod] [--no-smt] [--baseline] file.smt2...
// --baseline: Bitwuzla alone on the original text (its own parser), same time limit.
#include "../src/util.hpp"
#include "../src/smtlib.hpp"
#include "../src/solver.hpp"
#include <bitwuzla/c/bitwuzla.h>
extern "C" {
#include <bitwuzla/c/parser.h>
}
#include <chrono>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <sstream>
using namespace unshroud;

static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

static const char* baseline(const std::string& path, u32 ms, double& dt) {
  BitwuzlaTermManager* tm = bitwuzla_term_manager_new();
  BitwuzlaOptions* op = bitwuzla_options_new();
  bitwuzla_set_option(op, BITWUZLA_OPT_TIME_LIMIT_PER, ms);
  bitwuzla_set_option(op, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  BitwuzlaParser* p = bitwuzla_parser_new(tm, op, "smt2", 2, "NUL");
  const char* err = nullptr;
  double t = now();
  bitwuzla_parser_parse(p, path.c_str(), true, true, &err);
  const char* r = "error";
  if (err) fprintf(stderr, "bitwuzla parser: %s\n", err);
  if (!err) { BitwuzlaResult res = bitwuzla_check_sat(bitwuzla_parser_get_bitwuzla(p)); r = res == BITWUZLA_SAT ? "sat" : res == BITWUZLA_UNSAT ? "unsat" : "unknown"; }
  dt = now() - t;
  bitwuzla_parser_delete(p); bitwuzla_options_delete(op); bitwuzla_term_manager_delete(tm);
  return r;
}

int main(int argc, char** argv) {
  unshroud::limitMemory();
  SolveOptions o; bool base = false; int show = 0; bool norules = false; u32 prefix = 0; int seeded = 0; std::vector<std::string> files;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--timeout")) o.timeoutMs = (u32)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--no-ls")) o.localSearch = false;
    else if (!strcmp(argv[i], "--no-mod")) o.modular = false;
    else if (!strcmp(argv[i], "--no-smt")) o.smt = false;
    else if (!strcmp(argv[i], "--no-simplify")) o.simplify = false;
    else if (!strcmp(argv[i], "--ls")) o.lsBudget = (u32)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--baseline")) base = true;
    else if (!strcmp(argv[i], "--norules")) norules = true;
    else if (!strcmp(argv[i], "--show")) show = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--prefix-seed")) prefix = (u32)atoi(argv[++i]);
    else files.push_back(argv[i]);
  }
  int nsat = 0, nunsat = 0, nunk = 0, bsat = 0, bunsat = 0, bunk = 0, bad = 0;
  double tall = 0, tbase = 0;
  for (const auto& f : files) {
    std::ifstream in(f); std::stringstream ss; ss << in.rdbuf();
    Ctx X; X.norules = norules; std::vector<u32> as; std::string err;
    double t0 = now();
    if (!parseSmt2(X, ss.str(), as, err)) { printf("%-40s parse error: %s\n", f.c_str(), err.c_str()); continue; }
    double tp = now() - t0;
    u32 nodes = 0; for (u32 a : as) nodes += X.countNodes(a);
    for (int k = 0; k < show && k < (int)as.size(); k++) { u32 a = as[as.size() - 1 - k]; printf("  assert[-%d] (%u nodes): %s\n", k + 1, X.countNodes(a), X.str(a, 7).c_str()); }
    Solver S(X);
    std::vector<u64> seed(X.vars.size(), 0), model;
    if (prefix && as.size() > 1) {   // the inputs which reach the branch: a model of everything but the last constraint (not timed)
      std::vector<u32> pre(as.begin(), as.end() - 1); std::vector<u64> m(seed);
      if (S.smt(pre, &m, prefix) == SR_SAT) { seed = m; seeded++; }
    }
    std::vector<u32> path, query;
    if (prefix && as.size() > 1) { path.assign(as.begin(), as.end() - 1); query.push_back(as.back()); } else query = as;
    const char* stage = "";
    double t1 = now();
    SatResult r = S.check(path, query, seed, &model, o, &stage);
    double dt = now() - t1;
    tall += dt + tp;
    const char* check = "";
    if (r == SR_SAT) { for (u32 a : as) if (!(X.eval(a, model.data()) & 1)) { check = "  MODEL WRONG"; bad++; break; } }
    nsat += r == SR_SAT; nunsat += r == SR_UNSAT; nunk += r == SR_UNKNOWN;
    std::string name = f.substr(f.find_last_of("/\\") + 1);
    printf("%-26s %-7s %-8s %8.4fs  parse %.3fs  nodes %6u  vars %3zu%s", name.c_str(), satName(r), stage, dt, tp, nodes, X.vars.size(), check);
    if (base) {
      double bt; const char* br = baseline(f, o.timeoutMs, bt); tbase += bt;
      bsat += !strcmp(br, "sat"); bunsat += !strcmp(br, "unsat"); bunk += strcmp(br, "sat") && strcmp(br, "unsat");
      printf("   | bitwuzla %-7s %8.4fs%s", br, bt, (strcmp(br, satName(r)) && strcmp(br, "unknown") && r != SR_UNKNOWN) ? "  DISAGREE" : "");
    }
    printf("\n");
  }
  printf("unshroud:     sat %d unsat %d unknown %d  total %.2fs%s\n", nsat, nunsat, nunk, tall, bad ? "  (WRONG MODELS!)" : "");
  if (prefix) printf("(seeds from the path prefix: %d)\n", seeded);
  if (base) printf("bitwuzla: sat %d unsat %d unknown %d  total %.2fs\n", bsat, bunsat, bunk, tbase);
  return 0;
}
