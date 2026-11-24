#include "explore.hpp"
#include <Zydis/Zydis.h>
#include <chrono>
#include <cstring>
#include <deque>

namespace unshroud {

static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

Explorer::Explorer(Engine& E, std::shared_ptr<State> start, std::vector<Input> inputs, const ExploreConfig& cfg)
    : S(E.X), E(E), start(std::move(start)), inputs(std::move(inputs)), cfg(cfg) {
  // a branch side which tested replacements rule out is listed as "likely" unless the proof comes quickly: the time goes to other branches
  if (!this->cfg.solve.confirmMs) this->cfg.solve.confirmMs = this->cfg.confirmMs;
}

PathInfo Explorer::execute(const std::vector<u64>& vals, bool probe) {
  E.restore(*start);
  for (const Input& in : inputs) {
    u64 v = vals[in.var] & maskOf(in.size * 8);
    if (in.kind == 0) E.g[in.reg] = v;
    else E.pokeConcrete(in.addr, &v, in.size);
  }
  E.path.clear(); E.folded.clear(); E.foldedTaken.clear();
  E.spinLimit = probe && cfg.spinLimit ? std::min(cfg.spinLimit, cfg.relaxSpin) : cfg.spinLimit; E.spinReset();
  E.lazy = cfg.lazy; E.runPageLimit = cfg.runPages;
  E.tableMax = cfg.tableMax; E.tableLoads = 0;
  E.loopLimit = cfg.loopLimit; E.loopMark.armed = false; E.progressSig = 0; E.progressAt = E.icount;
  const u64 ic0 = E.icount; const u64 sym0 = E.symIns;
  E.stops.insert(cfg.retAddr);
  E.runVals = &vals; E.havocTop = start->g[RSP];
  Stop s = E.run(probe ? std::min(cfg.maxIns, cfg.relaxMaxIns) : cfg.maxIns);
  if (static const bool stk = getenv("UNSHROUD_STOPSTACK") != nullptr; stk && s != ST_ADDRESS) {
    // where a path ended: the addresses of code on its stack (return addresses, most likely)
    fprintf(stderr, "stop %d (%s) at %llx, %u calls left out:", (int)s, E.stopInfo.c_str(), (unsigned long long)E.rip, E.havocked);
    for (int i = 0, n = 0; i < 400 && n < 14; i++) { u64 v = 0; E.readMem(E.g[RSP] + 8 * i, &v, 8); for (auto& r : cfg.addressRanges) if (v >= r.first && v < r.second) { fprintf(stderr, " %llx", (unsigned long long)v); n++; break; } }
    fprintf(stderr, "%c", 10);
  }
  E.runVals = nullptr;
  st.symIns += E.symIns - sym0;
  PathInfo p;
  p.inputs = vals;
  while (p.inputs.size() < E.X.vars.size()) p.inputs.push_back(E.X.vars[p.inputs.size()].seed);   // inputs the run made (decisions of the environment)
  p.stop = s; p.pc = E.rip; p.info = E.stopInfo; p.ins = E.icount - ic0;
  p.rax = {E.g[RAX], E.X.force(E.gs[RAX])};
  p.assumed = E.havocked; p.forced = E.forced;
  u64 h = 0x9E3779B97F4A7C15ull;
  for (const auto& c : E.path) p.all.push_back(c.cond);
  for (const auto& c : E.path) if (c.kind <= 2) { if (c.kind != 1) p.branch.push_back(c.cond); h = (h ^ c.pc) * 0x100000001b3ull; h = (h ^ c.taken) * 0x100000001b3ull; }
  p.sig = h;
  return p;
}

// The run ended somewhere below the function: the innermost return address into the function's own code on the stack
// (a word which follows a call instruction there) names the call.
u64 Explorer::blameCall() {
  const u64 sp = E.g[RSP], top = start->g[RSP];
  if (!cfg.fnEnd || sp >= top || (sp & 7)) return 0;
  for (u64 a = sp, n = 0; a < top && n < 65536; a += 8, n++) {
    u64 v = 0; E.readMem(a, &v, 8);
    if (v <= cfg.fnStart || v > cfg.fnEnd) continue;
    auto it = callOf.find(v);
    if (it == callOf.end()) it = callOf.emplace(v, E.callBefore(v)).first;
    if (!it->second) continue;
    // a call the compiler knows not to return (a breakpoint or ud2 follows it, or the function's end): the path ends there
    u8 nx[2] = {0, 0}; if (v < cfg.fnEnd) E.readMem(v, nx, 2);
    return v >= cfg.fnEnd || nx[0] == 0xCC || (nx[0] == 0x0F && nx[1] == 0x0B) ? 0 : it->second;
  }
  return 0;
}

// an address which can only take values close to each other: a table indexed by something small, a slot chosen by flags
bool Explorer::narrow(u32 expr) {
  Ctx::Range r = E.X.range(expr);
  return r.hi - r.lo < 0x10000;
}

bool Explorer::inRanges(u64 a) const {
  if (cfg.addressRanges.empty()) return true;
  for (auto& r : cfg.addressRanges) if (a >= r.first && a < r.second) return true;
  return false;
}

void Explorer::run() {
  const double t0 = now();
  struct Item { std::vector<u64> vals; size_t bound; bool relaxed = false; };
  std::deque<Item> work;
  std::vector<u64> seed(E.X.vars.size());
  for (size_t i = 0; i < seed.size(); i++) seed[i] = E.X.vars[i].seed;
  work.push_back({seed, 0});
  std::map<u64, std::vector<u64>> pending; bool havocPhase = false;       // calls runs ended in (with the inputs of one such run); are they left out yet?
  const auto nameCall = [&](u64 site, const std::vector<u64>& vals, bool relaxed) {
    E.addHavocSite(site); st.havocSites++;
    asked[{site ^ 0x4856000000000000ull, 2}] = cfg.attempts;            // (making the call is what was explored before)
    work.push_back({vals, 0, relaxed});
  };
  // jumps whose other side the solver could not reach, with the inputs of a run which came to them
  std::map<u64, std::vector<u64>> forceCand; int forceRound = 0;
  // the run which executed a side first (its inputs, shared by the sides of one run): what a force round runs again
  std::unordered_map<u64, std::shared_ptr<std::vector<u64>>> siteVals;
  E.covRec = cfg.force >= 2 && E.covOn;
  const auto startForce = [&]() {
    if (cfg.force <= 0 || forceRound >= cfg.forceRounds || st.runs >= cfg.maxRuns || now() - t0 >= cfg.timeLimit || E.X.overBudget) return false;
    forceRound++;
    const auto both = [&](u64 s) { return E.covOn && E.cov.count(s << 1) && E.cov.count((s << 1) | 1); };
    // the side a forced run would take is a dead one (the jump's own code rules it out): not forced
    const auto deadSide = [&](u64 s) { if (cfg.dead.empty() || !E.covOn) return false; const bool one = E.cov.count((s << 1) | 1) != 0; return cfg.dead.count((s << 1) | (one ? 0 : 1)) != 0; };
    size_t n = 0;
    for (auto& kv : forceCand) {
      if (both(kv.first) || E.forceSites.count(kv.first) || deadSide(kv.first)) continue;
      E.addForceSite(kv.first); st.forceSites++; work.push_back({kv.second, 0, false}); n++;
    }
    if (cfg.force >= 2 && E.covOn) {
      // the jumps of the function's own code which went one way only whatever the inputs: forced on the run which came
      // to them first (one run once, with all of its jumps)
      std::set<const std::vector<u64>*> runs;
      for (auto& kv : siteVals) {
        const u64 s = kv.first;
        if (both(s) || E.forceSites.count(s) || deadSide(s) || (cfg.fnEnd && (s < cfg.fnStart || s >= cfg.fnEnd))) continue;
        E.addForceSite(s); st.forceSites++;
        if (runs.insert(kv.second.get()).second) { work.push_back({*kv.second, 0, false}); n++; }
      }
    }
    return n > 0;
  };
  const auto startHavoc = [&]() {
    if (!cfg.havoc || havocPhase || pending.empty() || st.runs >= cfg.maxRuns || now() - t0 >= cfg.timeLimit || E.X.overBudget) return false;
    havocPhase = true;
    for (auto& kv : pending) nameCall(kv.first, kv.second, false);
    pending.clear();
    return true;
  };
  for (;;) {
  while (!work.empty() && st.runs < cfg.maxRuns && now() - t0 < cfg.timeLimit && !E.X.overBudget) {
    if (!havocPhase && !pending.empty() && (now() - t0 > cfg.havocAt * cfg.timeLimit || st.runs > cfg.maxRuns * cfg.havocAt)) startHavoc();
    if (!forceRound && cfg.force > 0 && (now() - t0 > cfg.forceAt * cfg.timeLimit || st.runs > cfg.maxRuns * cfg.forceAt)) startForce();
    Item it = std::move(work.front()); work.pop_front();
    double tr = now(); const double tItem = tr;
    if (it.relaxed && st.tRelax > cfg.relaxShare * cfg.timeLimit) continue;       // the share of the time for blocked sides is spent
    struct Charge { double& t; double t0; bool on; ~Charge() { if (on) t += now() - t0; } } charge{st.tRelax, tr, it.relaxed};
    PathInfo p = execute(it.vals, it.relaxed);
    if (E.covRec && !E.covNewRun.empty()) { auto sv = std::make_shared<std::vector<u64>>(p.inputs); for (u64 k : E.covNewRun) siteVals.try_emplace(k >> 1, sv); }
    it.vals = p.inputs;
    st.tRun += now() - tr; st.runs++; st.ins += p.ins;
    std::vector<PathConstraint> path = E.path;      // this run's constraints
    if (it.bound > 0 && it.bound <= path.size()) st.prefixIns += path[it.bound - 1].at - (E.icount - p.ins);
    for (const auto& c : path) if (c.kind == 0) edges.insert({c.pc, c.taken});
    for (const auto& f : E.folded) foldedSides.insert(f);
    for (const auto& f : E.foldedTaken) reachedFolded.insert(f);
    std::shared_ptr<std::vector<u32>> shared;       // this path's conditions, kept when a blocked side is met on it
    auto mix = [](u64 h, u64 v) { h ^= v + 0x9E3779B97F4A7C15ull + (h << 6) + (h >> 2); return h * 0xff51afd7ed558ccdull; };
    {
      u64 ph = 0;
      for (const auto& c : path) {
        if ((c.kind == 1 || c.kind == 2) && c.expr) values[cfg.pathMode ? mix(ph, c.expr) : c.expr].insert(c.taken);
        if (c.kind <= 2) ph = mix(mix(ph, c.pc), c.taken);
      }
    }
    u64 prefixHash = 0;
    if (!sigs.count(p.sig)) { sigs.insert(p.sig); paths.push_back(p); }
    if (cfg.havoc && !(p.stop == ST_ADDRESS && p.pc == cfg.retAddr) && !E.X.overBudget) {
      const u64 site = blameCall();
      // a call not named before: the same inputs once more - the run now carries the decision, which gets flipped below
      if (site && !E.havocSites.count(site)) { if (havocPhase) nameCall(site, it.vals, it.relaxed); else pending.emplace(site, it.vals); }
    }
    // the children: every decision after the bound, the other way
    // the conditions of the path and the hash of the decisions before each one
    std::vector<u32> conds(path.size()); std::vector<u64> before(path.size());
    for (size_t i = 0; i < path.size(); i++) {
      conds[i] = path[i].cond; before[i] = prefixHash;
      if (path[i].kind <= 2) prefixHash = mix(mix(prefixHash, path[i].pc), path[i].taken);
    }
    auto budget = [&]() {
      SolveOptions so = cfg.solve; so.timeoutMs = std::max<u32>(50, std::min<u32>(so.timeoutMs, (u32)((cfg.timeLimit - (now() - t0)) * 1000)));
      // what a blocked side's input leads to has its share of the time, and no query of it takes more than what is left of it
      if (it.relaxed) { const double left = cfg.relaxShare * cfg.timeLimit - st.tRelax - (now() - tItem); so.timeoutMs = std::max<u32>(50, std::min<u32>(std::min<u32>(so.timeoutMs, 500), (u32)(std::max(0.0, left) * 1000))); }
      return so;
    };
    // 1. the branches the other way: what opens new code
    size_t iEnd = path.size();
    for (size_t i = it.bound; i < path.size() && now() - t0 < cfg.timeLimit; i++) {
      if (it.relaxed && st.tRelax + (now() - tItem) > cfg.relaxShare * cfg.timeLimit) { iEnd = i; break; }
      if (cfg.slice > 0 && i > it.bound && !work.empty() && now() - tItem > cfg.slice * cfg.timeLimit) { work.push_back({it.vals, i, it.relaxed}); iEnd = i; break; }
      const PathConstraint& c = path[i];
      if (c.kind != 0) continue;
      std::pair<u64, u64> key{c.pc, c.other};
      const u64 pk = mix(mix(before[i], c.pc), c.other);
      bool ask = cfg.pathMode ? !tried.count(pk) : (!edges.count(key) && asked[key] < cfg.attempts);
      if (!ask) continue;
      asked[key]++; tried.insert(pk);
      std::vector<u32> prefix(conds.begin(), conds.begin() + i);
      std::vector<u64> model; const char* stage = "";
      double ts = now();
      const u32 notc = E.X.not_(c.cond);
      SatResult r = S.check(prefix, {notc}, it.vals, &model, budget(), &stage);
      st.tSolve += now() - ts; st.queries++; st.stages[stage]++;
      if (r != SR_SAT && cfg.force > 0 && !forceCand.count(c.pc)) forceCand.emplace(c.pc, it.vals);
      const double dtQuery = now() - ts;
      if (r == SR_SAT) { st.sat++; work.push_back({model, i + 1, it.relaxed}); edges.insert(key); }   // counted as reached: the child will
      else if (r == SR_UNSAT) {
        st.unsat++; refuted[key]++;
        // impossible after this path. And by itself? (asked while the answer can still change the side's label or give a visit to try again)
        auto& vs = visits[key];
        if (cfg.relax && i > 0 && (!open.count(key) || vs.size() < cfg.relax)) {
          SatResult alone; std::vector<u64> m2;
          auto memo = aloneMemo.find(notc);
          if (memo != aloneMemo.end() && memo->second != SR_SAT) alone = (SatResult)memo->second;
          else {
            // (as much time as the answer after the path took, and a little more: a side which is impossible by itself
            // is as hard to refute without the path; one the path rules out can be hard by itself, and is then left open)
            const char* stage2 = ""; ts = now();
            SolveOptions so = budget(); so.timeoutMs = std::min<u32>(so.timeoutMs, std::max<u32>(60, (u32)(4000 * dtQuery)));
            if (strcmp(stage, "modular")) so.modular = false;
            alone = S.check({}, {notc}, it.vals, &m2, so, &stage2);
            st.tSolve += now() - ts; st.queries++; st.stages[std::string("alone-") + stage2]++;
            aloneMemo[notc] = (u8)alone;
          }
          if (alone != SR_UNSAT) {
            open[key]++;
            if (alone == SR_SAT && vs.size() < cfg.relax) {
              if (!shared) shared = std::make_shared<std::vector<u32>>(conds);
              vs.push_back({shared, i, notc, it.vals, m2, false});
              if (!cfg.pathMode) { work.push_back({m2, 0, true}); st.relaxed++; }      // an input for the side by itself: tried at once (the longest prefix: when nothing else is left)
            }
          }
        }
      }
      else if (!strcmp(stage, "likely-unsat")) { st.unknown++; likely.insert(key); asked[key] = cfg.attempts; }   // no model expected, no proof: not asked again
      else { st.unknown++; undecided.insert(key); }
    }
    // 2. other values of computed targets / symbolic addresses: a few per visit, within a share of the time, continued on later visits
    for (size_t i = it.bound; i < iEnd && now() - t0 < cfg.timeLimit; i++) {
      if (it.relaxed && st.tRelax + (now() - tItem) > cfg.relaxShare * cfg.timeLimit) break;
      const PathConstraint& c = path[i];
      if (!(c.expr && (c.kind == 2 || (c.kind == 1 && cfg.addresses && (inRanges(c.taken) || narrow(c.expr)))))) continue;
      if (E.lazyMem && Engine::inZone(c.taken)) continue;                // unknown memory / an unknown function: any value is as good
      const unsigned ub = E.X.unknownBits(c.expr);
      // a share of the time for the values of data addresses; a computed target, or an address a few bits choose (a
      // virtual branch), is control flow: always asked
      if (st.tEnum > cfg.enumShare * cfg.timeLimit && c.kind != 2 && ub > 3) continue;
      // keyed by the expression: one handler of a virtual machine serves every virtual branch, with another expression each time
      const u64 vk = cfg.pathMode ? mix(before[i], c.expr) : c.expr;
      auto& seen = values[vk];
      const unsigned w = E.X.W(c.expr);
      std::vector<u32> prefix(conds.begin(), conds.begin() + i);
      // the bits of the expression which can change bound its values: every one of them seen, nothing to ask
      if (cfg.siteWaste > 0 && wasted[c.pc] > cfg.siteWaste * cfg.timeLimit) { st.skipped++; continue; }
      for (u32 k = 0; k < cfg.enumPerVisit && seen.size() < cfg.maxTargets && !complete.count(vk) && perSite[c.pc] < cfg.maxPerSite && now() - t0 < cfg.timeLimit; k++) {
        if (ub < 16 && seen.size() >= (1ull << ub)) { complete.insert(vk); st.skipped++; break; }
        perSite[c.pc]++;
        std::vector<u32> query;
        for (u64 v : seen) query.push_back(E.X.ne(c.expr, E.X.cst(v, w)));
        std::vector<u64> model; const char* stage = "";
        double ts = now();
        SatResult r = S.check(prefix, query, it.vals, &model, budget(), &stage);
        double dt = now() - ts;
        st.tSolve += dt; st.tEnum += dt; st.queries++; st.stages[stage]++;
        if (r == SR_SAT) { st.sat++; seen.insert(E.X.eval(c.expr, model.data())); work.push_back({model, i + 1, it.relaxed}); wasted[c.pc] = 0; }
        else {
          wasted[c.pc] += dt; if (r == SR_UNSAT) { st.unsat++; complete.insert(vk); } else st.unknown++; break; }
      }
    }
  }
  // blocked sides not reached since: an input which satisfies the side and the longest part of the path before it that
  // still allows it (edge mode: in path mode every prefix is tried anyway)
  if (!cfg.relax || cfg.pathMode || st.runs >= cfg.maxRuns || now() - t0 >= cfg.timeLimit || E.X.overBudget || st.tRelax > cfg.relaxShare * cfg.timeLimit) { if (work.empty() && (startHavoc() || startForce())) continue; break; }
  for (auto& kv : visits) {
    if (edges.count(kv.first) || reachedFolded.count(kv.first)) continue;
    for (Visit& v : kv.second) {
      if (v.done || now() - t0 >= cfg.timeLimit) continue;
      v.done = true;
      size_t lo = 0, hi = v.at; std::vector<u64> model = v.model;
      for (int q = 0; q < 6 && hi - lo > 1 && now() - t0 < cfg.timeLimit; q++) {
        const size_t mid = lo + (hi - lo + 1) / 2;
        std::vector<u32> prefix(v.conds->begin(), v.conds->begin() + mid); std::vector<u64> m; const char* stage = "";
        const double ts = now();
        SolveOptions so = cfg.solve; so.timeoutMs = std::max<u32>(50, std::min<u32>(250, (u32)((cfg.timeLimit - (now() - t0)) * 1000))); so.modular = false;
        const SatResult r = S.check(prefix, {v.notCond}, v.vals, &m, so, &stage);
        st.tSolve += now() - ts; st.queries++; st.stages[std::string("relax-") + stage]++;
        if (r == SR_SAT) { lo = mid; model = std::move(m); } else hi = mid;
      }
      work.push_back({std::move(model), lo, true}); st.relaxed++;
    }
  }
  if (work.empty() && !startHavoc() && !startForce()) break;
  }
  st.tAll = now() - t0;
  // a branch the rules decided on each visit, one way on some visits and the other way on others, is a decision of the
  // function all the same: both sides are edges
  {
    std::map<u64, std::set<u64>> sides;
    for (const auto& e : edges) sides[e.first].insert(e.second);
    for (const auto& f : reachedFolded) sides[f.first].insert(f.second);
    for (const auto& f : reachedFolded) if (sides[f.first].size() >= 2) edges.insert(f);
  }
  // decided by the rules on every visit: impossible (a side which some path reaches is taken out below)
  for (const auto& f : foldedSides) if (!refuted.count(f)) refuted[f] = 1;
  // what was found impossible but reached later is not impossible
  for (auto it = refuted.begin(); it != refuted.end();) { if (edges.count(it->first) || reachedFolded.count(it->first)) it = refuted.erase(it); else ++it; }
  // impossible after the paths which came to it only: blocked, not refuted
  for (auto it = refuted.begin(); it != refuted.end();) { if (open.count(it->first)) { blocked.insert(it->first); it = refuted.erase(it); } else ++it; }
  for (auto it = undecided.begin(); it != undecided.end();) { if (edges.count(*it) || refuted.count(*it) || blocked.count(*it)) it = undecided.erase(it); else ++it; }
  for (auto it = likely.begin(); it != likely.end();) { if (edges.count(*it) || refuted.count(*it) || blocked.count(*it)) it = likely.erase(it); else ++it; }
}

}  // namespace unshroud
