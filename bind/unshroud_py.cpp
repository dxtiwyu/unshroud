// unshroud - Python module (nanobind): the engine, expressions, the resolver, the MBA simplifier, the explorer.
#include "../src/engine.hpp"
#include "../src/explore.hpp"
#include "../src/mba.hpp"
#include "../src/pe.hpp"
#include "../src/solver.hpp"
#include "../src/util.hpp"
#include "../src/win.hpp"
#include <nanobind/nanobind.h>
#include <nanobind/stl/function.h>
#include <nanobind/stl/map.h>
#include <nanobind/stl/pair.h>
#include <nanobind/stl/shared_ptr.h>
#include <nanobind/stl/string.h>
#include <nanobind/stl/tuple.h>
#include <nanobind/stl/vector.h>
#include <memory>

namespace nb = nanobind;
using namespace unshroud;

namespace {
const char* REGS[16] = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"};
int regIndex(const std::string& n) {
  for (int i = 0; i < 16; i++) if (n == REGS[i]) return i;
  throw nb::value_error(("unknown register " + n + " (64-bit names: rax..r15; rip, fsbase, gsbase have their own accessors)").c_str());
}
const char* stopName(Stop s) {
  static const char* n[] = {"none", "count", "address", "return", "fault", "unsupported", "exception", "hook", "syscall", "halt"};
  return (unsigned)s < 10 ? n[s] : "?";
}

// an engine owned by Python, with the solver and simplifier which live as long as it
struct PyEngine {
  Engine E;                                    // first: a model finds the PyEngine of the Engine which calls it
  std::unique_ptr<Solver> S;
  std::unique_ptr<Mba> M;
  std::string hookError;                       // an exception raised by a hook, raised again when run() returns
  std::shared_ptr<WinEnv> env;                 // the Windows process the image runs in (load_pe(env=True)), or null
  std::shared_ptr<std::map<std::string, std::string>> apiErrors = std::make_shared<std::map<std::string, std::string>>();   // Python models which raised: name -> message
  std::map<std::string, u32> vnames;           // build(): variables by name (the same name is the same input in every call)
  WinEnv& need() { if (!env) throw std::runtime_error("no process environment (load_pe(..., env=True) builds it)"); return *env; }
  Solver& solver() { if (!S) S.reset(new Solver(E.X)); return *S; }
  Mba& mba() { if (!M) M.reset(new Mba(E.X, &solver())); return *M; }
};

struct Expr {
  std::shared_ptr<PyEngine> owner; u32 id;
  Ctx& X() const { return owner->E.X; }
};

nb::object exprOrNone(const std::shared_ptr<PyEngine>& e, u32 id) {
  if (!id) return nb::none();
  return nb::cast(Expr{e, id});
}
}  // namespace

NB_MODULE(unshroud, m) {
  nb::set_leak_warnings(false);
  m.doc() = "unshroud: a concolic x86-64 engine with an MBA simplifier, a layered resolver (local search, modular proofs, Bitwuzla) and a path explorer";
  m.def("limit_memory", [](size_t mb) { limitMemory(mb); }, nb::arg("mb") = 4096, "Caps the memory of this process (Windows job object).");

  nb::class_<State>(m, "State");

  nb::class_<Expr>(m, "Expr")
    .def("__str__", [](const Expr& x) { return x.X().str(x.id, 12); })
    .def("str", [](const Expr& x, int depth) { return x.X().str(x.id, depth); }, nb::arg("depth") = 12)
    .def("smt", [](const Expr& x) { return x.X().smt(x.id); }, "SMT-LIB define-funs of the expression")
    .def("py", [](const Expr& x) { return x.X().py({x.id}, "f"); }, "Python source of f(x, y, z, w) (helpers: unshroudpy.op)")
    .def_prop_ro("id", [](const Expr& x) { return x.id; })
    .def_prop_ro("width", [](const Expr& x) { return x.X().W(x.id); })
    .def_prop_ro("nodes", [](const Expr& x) { return x.X().countNodes(x.id); })
    .def_prop_ro("is_const", [](const Expr& x) { return x.X().isC(x.id); })
    .def_prop_ro("op", [](const Expr& x) { return std::string(opName(x.X().N(x.id).op)); })
    .def("value", [](const Expr& x) { return x.X().evalSeed(x.id); }, "value under the inputs' current (seed) values")
    .def("eval", [](const Expr& x, const std::map<u32, u64>& vals) {
      Ctx& X = x.X(); std::vector<u64> v(X.vars.size());
      for (size_t i = 0; i < v.size(); i++) v[i] = X.vars[i].seed;
      for (auto& kv : vals) if (kv.first < v.size()) v[kv.first] = kv.second;
      return X.eval(x.id, v.data());
    }, nb::arg("values"), "value with some inputs given ({input index: value}), the others at their seed")
    .def("variables", [](const Expr& x) { std::vector<u32> v; x.X().collectVars(x.id, v); return v; })
    .def("simplify", [](const Expr& x, double budget) { Mba& M = x.owner->mba(); M.o.budget = budget; u32 r = M.simplify(x.id); r = M.foldConditions(r, x.owner->solver()); return Expr{x.owner, M.simplify(r)}; },
         nb::arg("budget") = 2.0, "MBA simplification, then conditions which cannot change replaced by constants")
    .def("dag", [](const Expr& x) {
      Ctx& X = x.X(); nb::list out; std::unordered_map<u32, int> idx; std::vector<u32> st{x.id};
      while (!st.empty()) {
        const u32 id = st.back();
        if (idx.count(id)) { st.pop_back(); continue; }
        const Node d = X.N(id); const u32 ch[3] = {d.a, d.b, d.c}; const bool leaf = d.op == O_CONST || d.op == O_VAR; bool miss = false;
        if (!leaf) for (u32 c : ch) if (c && !idx.count(c)) { st.push_back(c); miss = true; }
        if (miss) continue;
        st.pop_back();
        int k[3]; for (int i = 0; i < 3; i++) k[i] = (!leaf && ch[i]) ? idx[ch[i]] : -1;
        idx[id] = (int)nb::len(out);
        out.append(nb::make_tuple(std::string(opName(d.op)), (int)d.w, (int)d.lo, k[0], k[1], k[2], d.k, d.op == O_VAR ? X.vars[d.k].name : std::string()));
      }
      return out;
    }, "the expression as a node list, children first, root last: (op, width, lo, a, b, c, k, name); a/b/c index the list (-1: none); k: constant / input index")
    .def("__eq__", [](const Expr& a, const Expr& b) { return a.id == b.id && a.owner == b.owner; })
    .def("__hash__", [](const Expr& a) { return (size_t)a.id; });

  using EP = std::shared_ptr<PyEngine>;
  nb::class_<PyEngine>(m, "Engine")
    .def(nb::new_([]() { return std::make_shared<PyEngine>(); }))
    // ---- memory
    .def("load_pe", [](EP e, const std::string& path, u64 stubBase, bool env, bool init) {
      Image img;
      if (!loadPE(e->E, path, img, stubBase)) throw nb::value_error(("cannot load " + path).c_str());
      nb::dict d; d["base"] = img.base; d["size"] = img.size; d["entry"] = img.entry; d["stubs"] = img.stubs; d["funcs"] = img.funcs;
      if (env) {
        auto w = std::make_shared<WinEnv>();
        if (w->build(e->E, img, path)) { e->env = w; w->attach(e->E); }
      }
      d["env"] = (bool)e->env; d["init"] = false;
      if (e->env) {
        d["stack"] = WinEnv::RSP0;
        std::vector<std::tuple<std::string, u64, u64>> mods; for (auto& m : e->env->order) mods.push_back({m->name, m->base, m->size});
        d["modules"] = mods;
        if (init) {
          auto before = e->E.snapshot(); std::string info;
          if (e->env->runInit(e->E, 200000000, &info)) d["init"] = true; else { e->E.restore(*before); d["init_error"] = info; }
        }
      }
      return d;
    }, nb::arg("path"), nb::arg("stub_base") = 0x7ffe00000000ull, nb::arg("env") = true, nb::arg("init") = false,
       "Maps a PE image. env=True (default): the image runs in a Windows process (TEB / PEB, loader lists, system DLLs, models of system "
       "functions on every import and export, exception dispatch); the stack is mapped, 'stack' is the stack pointer to start with. "
       "env=False: imports point at stubs which only return. init=True: the entry point runs first (DLL_PROCESS_ATTACH). "
       "Returns base, size, entry, stubs {address: name}, funcs [(rva, size)], env, modules [(name, base, size)].")
    // ---- the process environment
    .def_prop_ro("env", [](EP e) { return (bool)e->env; }, "True when the image runs in a Windows process")
    .def("share_env", [](EP e, EP other) { e->env = other->env; e->apiErrors = other->apiErrors; if (e->env) e->env->attach(e->E); },
         "Another engine's process (for an engine which restores a state saved by that one)")
    .def("env_options", [](EP e, bool exceptions, int nullFaults, bool decideSizes, bool trace) {
      WinEnv& w = e->need(); w.exceptions = exceptions; w.nullFaults = nullFaults; w.decideSizes = decideSizes; w.trace = trace;
      e->E.trap = nullptr; e->E.setGuard(0); w.attach(e->E);
    }, nb::arg("exceptions") = true, nb::arg("null_faults") = 2, nb::arg("decide_sizes") = false, nb::arg("trace") = false,
       "exceptions: int3 / ud2 / access violations / divide errors / RaiseException go to the program's handlers; null_faults: an access below "
       "0x10000 never faults (0), is an access violation when a handler is there to take it (1), or that is a decision explore() flips (2); decide_sizes: allocation sizes which depend on inputs are decisions of the path")
    .def("set_api", [](EP e, const std::string& name, nb::callable f) {
      auto errs = e->apiErrors;
      e->need().model(name, [f, errs](Api& a) {
        try {
          PyEngine* pe = reinterpret_cast<PyEngine*>(&a.E);          // the engine making the call (E is PyEngine's first member)
          nb::object r = f(nb::find(pe));
          if (r.is_none()) { a.ret(0); return; }
          if (nb::isinstance<nb::bool_>(r)) { if (nb::cast<bool>(r)) a.done = true; else a.ret(0); return; }
          a.ret(nb::cast<u64>(nb::int_(r) & nb::int_(0xffffffffffffffffull)));
        } catch (nb::python_error& err) { (*errs)[a.name] = err.what(); throw std::runtime_error(err.what()); }   // counted as a model error: the call returns 0, the path goes on
      });
    }, nb::arg("name"), nb::arg("callable"),
       "Adds or replaces the model of a system function, by name: callable(engine) runs at its entry ([rsp]: the return address; api_arg(k): "
       "the arguments). It returns the function's result (an int; None: 0) and the engine returns to the caller, or True when it moved rip itself.")
    .def("api_arg", [](EP e, int k) { static const int r[4] = {RCX, RDX, R8, R9}; if (k < 4) return e->E.g[r[k]]; u64 v = 0; e->E.readMem(e->E.g[RSP] + 8 * (u64)(k + 1), &v, 8); return v; },
         "k-th argument of the system function being entered")
    .def("has_api", [](EP e, const std::string& name) { return e->need().hasModel(name); })
    .def_prop_ro("api_calls", [](EP e) { return e->need().calls; }, "{name: calls} since clear_api_counts()")
    .def_prop_ro("api_unmodeled", [](EP e) { return e->need().unmodeled; }, "{name: calls} of functions without a model (they return 0)")
    .def_prop_ro("api_errors", [](EP e) { nb::dict d; d["counts"] = e->need().errors; d["messages"] = *e->apiErrors; return d; })
    .def("clear_api_counts", [](EP e) { WinEnv& w = e->need(); w.calls.clear(); w.unmodeled.clear(); w.errors.clear(); })
    .def("resolve", [](EP e, const std::string& dll, const std::string& name) { return e->need().resolve(e->E, dll, name); }, "address of an export (the DLL is mapped if it was not); 0: none")
    .def("api_at", [](EP e, u64 a) { return e->need().apiName(a); }, "name of the system function at an address ('' when none)")
    .def("run_init", [](EP e, u64 maxIns) { std::string info; const bool ok = e->need().runInit(e->E, maxIns, &info); return std::make_pair(ok, info); },
         nb::arg("max_ins") = 200000000ull, "Runs the image's TLS callbacks and entry point (DLL_PROCESS_ATTACH): (returned, why not)")
    .def("map", [](EP e, u64 a, u64 n) { e->E.map(a, n); })
    .def("write", [](EP e, u64 a, nb::bytes b) { e->E.writeMem(a, b.c_str(), b.size()); }, "concrete bytes (expressions there are dropped)")
    .def("poke", [](EP e, u64 a, nb::bytes b) { e->E.pokeConcrete(a, b.c_str(), b.size()); }, "concrete bytes, the expressions there are kept")
    .def("read", [](EP e, u64 a, size_t n) { std::string s(n, 0); e->E.readMem(a, s.data(), n); return nb::bytes(s.data(), n); })
    .def("load", [](EP e, u64 a, unsigned size) { Val v = e->E.load(a, size); return std::make_pair(v.c, exprOrNone(e, v.s)); }, "(value, expression or None) of size bytes")
    .def("symbolize_mem", [](EP e, u64 a, unsigned size, const std::string& name) { return (u32)e->E.X.N(e->E.symbolizeMem(a, size, name)).k; },
         nb::arg("address"), nb::arg("size"), nb::arg("name"), "Makes the bytes an input; returns its index")
    .def_prop_rw("auto_map", [](EP e) { return e->E.autoMap; }, [](EP e, bool v) { e->E.autoMap = v; })
    // ---- registers
    .def("reg", [](EP e, const std::string& r) { return e->E.g[regIndex(r)]; })
    .def("set_reg", [](EP e, const std::string& r, u64 v) { int i = regIndex(r); e->E.g[i] = v; e->E.gs[i] = 0; }, "concrete value (the expression is dropped)")
    .def("poke_reg", [](EP e, const std::string& r, u64 v) { e->E.g[regIndex(r)] = v; }, "concrete value, the expression is kept (inputs: the value they take on the next run)")
    .def("reg_expr", [](EP e, const std::string& r) { return exprOrNone(e, e->E.gs[regIndex(r)]); })
    .def("symbolize_reg", [](EP e, const std::string& r, const std::string& name) { return (u32)e->E.X.N(e->E.symbolizeReg(regIndex(r), name)).k; },
         nb::arg("reg"), nb::arg("name"), "Makes the register an input; returns its index")
    .def_prop_rw("rip", [](EP e) { return e->E.rip; }, [](EP e, u64 v) { e->E.rip = v; })
    .def_prop_rw("fsbase", [](EP e) { return e->E.fsbase; }, [](EP e, u64 v) { e->E.fsbase = v; })
    .def_prop_rw("gsbase", [](EP e) { return e->E.gsbase; }, [](EP e, u64 v) { e->E.gsbase = v; })
    .def_prop_ro("rflags", [](EP e) { return e->E.rflags(); })
    .def("xmm", [](EP e, int r) { return nb::bytes((const char*)e->E.v[r], 16); })
    .def("set_xmm", [](EP e, int r, nb::bytes b) { memcpy(e->E.v[r], b.c_str(), std::min<size_t>(32, b.size())); memset(e->E.vc[r], 0, sizeof e->E.vc[r]); e->E.vsym &= ~(1u << r); })
    // ---- inputs
    .def_prop_ro("inputs", [](EP e) { std::vector<std::tuple<std::string, unsigned, u64>> v; for (auto& x : e->E.X.vars) v.push_back({x.name, x.w, x.seed}); return v; },
                 "[(name, bits, current value)]")
    .def("set_input", [](EP e, u32 i, u64 v) { if (i >= e->E.X.vars.size()) throw nb::index_error(); e->E.X.vars[i].seed = v & maskOf(e->E.X.vars[i].w); },
         "the value an input takes in evaluations (Expr.value); the concrete state is not changed")
    // ---- execution
    .def("run", [](EP e, u64 count) {
      e->hookError.clear();
      Stop s = e->E.run(count);
      if (!e->hookError.empty()) { std::string m = e->hookError; e->hookError.clear(); throw std::runtime_error("hook: " + m); }
      return std::make_pair(std::string(stopName(s)), e->E.stopInfo);
    }, nb::arg("count") = 1000000000ull, "Runs from rip: (reason, info). Reasons: count, address (a stop), fault, unsupported, exception, hook, syscall, halt.")
    .def("stop_at", [](EP e, u64 a) { e->E.stops.insert(a); e->E.flushBlocks(); })
    .def("clear_stop", [](EP e, u64 a) { e->E.stops.erase(a); e->E.flushBlocks(); })
    .def("hook", [](EP e, u64 a, nb::callable f) {
      PyEngine* pe = e.get();
      e->E.hooks[a] = [pe, f](Engine&) -> Stop {
        try {
          nb::object r = f(nb::find(pe));
          if (r.is_none()) return ST_NONE;
          return nb::cast<bool>(r) ? ST_HOOK : ST_NONE;
        } catch (nb::python_error& err) { pe->hookError = err.what(); return ST_HOOK; }
      };
      e->E.flushBlocks();
    }, nb::arg("address"), nb::arg("callable"), "callable(engine) runs instead of the instruction at the address: it moves rip and returns None/False, or returns True to stop")
    .def("unhook", [](EP e, u64 a) { e->E.hooks.erase(a); e->E.flushBlocks(); })
    .def_prop_ro("icount", [](EP e) { return e->E.icount; })
    .def("disasm", [](EP e, u64 a) { return e->E.disasm(a); })
    .def_prop_ro("nodes", [](EP e) { return e->E.X.n.size(); })
    // ---- the path
    .def_prop_ro("path", [](EP e) {
      nb::list out;
      static const char* kinds[] = {"branch", "address", "target", "value"};
      for (auto& c : e->E.path) {
        nb::dict d; d["kind"] = kinds[c.kind & 3]; d["pc"] = c.pc; d["taken"] = c.taken; d["other"] = c.other;
        d["cond"] = exprOrNone(e, c.cond); d["expr"] = exprOrNone(e, c.expr);
        out.append(d);
      }
      return out;
    }, "constraints of the path: kind (branch, address, target, value), pc, taken, other, cond (true on this path), expr (what was made concrete)")
    .def("clear_path", [](EP e) { e->E.path.clear(); })
    .def("snapshot", [](EP e) { return e->E.snapshot(); })
    .def("restore", [](EP e, std::shared_ptr<State> s) { e->E.restore(*s); })
    // ---- resolution
    .def("solve", [](EP e, std::vector<Expr> path, std::vector<Expr> query, u32 timeoutMs, bool smt) {
      std::vector<u32> p, q; for (auto& x : path) p.push_back(x.id); for (auto& x : query) q.push_back(x.id);
      Ctx& X = e->E.X; std::vector<u64> seed(X.vars.size()), model;
      for (size_t i = 0; i < seed.size(); i++) seed[i] = X.vars[i].seed;
      SolveOptions o; o.timeoutMs = timeoutMs; o.smt = smt; const char* stage = "";
      SatResult r = e->solver().check(p, q, seed, &model, o, &stage);
      std::map<u32, u64> mm; if (r == SR_SAT) for (size_t i = 0; i < model.size(); i++) mm[(u32)i] = model[i];
      return std::make_tuple(std::string(satName(r)), mm, std::string(stage));
    }, nb::arg("path"), nb::arg("query"), nb::arg("timeout_ms") = 5000, nb::arg("smt") = true,
       "Is path + query satisfiable (the inputs' current values satisfy path)? (status, {input: value}, stage that answered)")
    .def("explore", [](EP e, std::shared_ptr<State> start, std::vector<std::tuple<u32, std::string, u64, unsigned>> ins, u64 ret, double seconds, bool paths, u64 maxIns, std::vector<std::pair<u64, u64>> ranges) {
      std::vector<Input> inputs;
      for (auto& [var, kind, where, size] : ins) {
        Input in{var, (u8)(kind == "mem"), 0, (u8)size, 0};
        if (kind == "mem") in.addr = where; else in.reg = (u8)where;
        inputs.push_back(in);
      }
      ExploreConfig cfg; cfg.retAddr = ret; cfg.timeLimit = seconds; cfg.pathMode = paths; cfg.maxIns = maxIns; cfg.addressRanges = ranges;   // the C++ tool uses the image; empty: every address
      Explorer ex(e->E, start, inputs, cfg);
      ex.run();
      nb::list ps;
      for (auto& p : ex.paths) {
        nb::dict d; d["inputs"] = p.inputs; d["stop"] = (p.stop == ST_ADDRESS && p.pc == ret) ? std::string("return") : std::string(stopName(p.stop));
        d["pc"] = p.pc; d["info"] = p.info; d["ins"] = p.ins; d["rax"] = p.rax.c; d["rax_expr"] = exprOrNone(e, p.rax.s);
        nb::list conds; for (u32 c : p.branch) conds.append(exprOrNone(e, c)); d["conds"] = conds;
        ps.append(d);
      }
      nb::dict r; r["paths"] = ps; r["edges"] = ex.edges.size(); r["runs"] = ex.st.runs; r["queries"] = ex.st.queries;
      r["refuted"] = std::vector<std::pair<u64, u64>>(ex.refuted.size()); size_t k = 0;
      std::vector<std::pair<u64, u64>> ref, und; for (auto& kv : ex.refuted) ref.push_back(kv.first); for (auto& u : ex.undecided) und.push_back(u);
      r["refuted"] = ref; r["undecided"] = und; r["time"] = ex.st.tAll; r["stages"] = ex.st.stages;
      r["blocked"] = std::vector<std::pair<u64, u64>>(ex.blocked.begin(), ex.blocked.end());
      (void)k;
      return r;
    }, nb::arg("start"), nb::arg("inputs"), nb::arg("ret"), nb::arg("seconds") = 10.0, nb::arg("paths") = false, nb::arg("max_ins") = 20000000ull, nb::arg("ranges") = std::vector<std::pair<u64, u64>>{},
       "Explores from a saved state: inputs = [(input index, 'reg' or 'mem', register index or address, size)]; a path ends at ret. Returns paths, edges, refuted / undecided branch sides.")
    .def("build", [](EP e, const std::vector<std::tuple<std::string, int, int, int, int, int, u64, std::string>>& nodes, const std::vector<int>& roots) {
      Ctx& X = e->E.X; std::vector<u32> id(nodes.size());
      for (size_t i = 0; i < nodes.size(); i++) {
        const auto& [op, w, lo, a, b, c, k, name] = nodes[i];
        auto A = [&](int j) -> u32 { if (j < 0 || (size_t)j >= i) throw nb::value_error("build: child index out of order"); return id[j]; };
        if (w < 1 || w > 64) throw nb::value_error("build: width must be 1..64");
        u32 r;
        if (op == "const") r = X.cst(k, w);
        else if (op == "var") {
          auto it = e->vnames.find(name);
          if (it != e->vnames.end()) { if (X.W(it->second) != (unsigned)w) throw nb::value_error(("build: width of " + name).c_str()); r = it->second; }
          else r = e->vnames[name] = X.var(name, w, k);
        }
        else if (op == "add") r = X.add(A(a), A(b));
        else if (op == "sub") r = X.sub(A(a), A(b));
        else if (op == "mul") r = X.mul(A(a), A(b));
        else if (op == "udiv") r = X.udiv(A(a), A(b));
        else if (op == "urem") r = X.urem(A(a), A(b));
        else if (op == "sdiv") r = X.sdiv(A(a), A(b));
        else if (op == "srem") r = X.srem(A(a), A(b));
        else if (op == "mulhu") r = X.mulhu(A(a), A(b));
        else if (op == "mulhs") r = X.mulhs(A(a), A(b));
        else if (op == "neg") r = X.neg(A(a));
        else if (op == "and") r = X.and_(A(a), A(b));
        else if (op == "or") r = X.or_(A(a), A(b));
        else if (op == "xor") r = X.xor_(A(a), A(b));
        else if (op == "not") r = X.not_(A(a));
        else if (op == "shl") r = X.shl(A(a), A(b));
        else if (op == "lshr") r = X.lshr(A(a), A(b));
        else if (op == "ashr") r = X.ashr(A(a), A(b));
        else if (op == "rol") r = X.rol(A(a), A(b));
        else if (op == "ror") r = X.ror(A(a), A(b));
        else if (op == "extract") r = X.extract(A(a), lo, w);
        else if (op == "zext") r = X.zext(A(a), w);
        else if (op == "sext") r = X.sext(A(a), w);
        else if (op == "concat") r = X.concat(A(a), A(b));
        else if (op == "ite") r = X.ite(A(a), A(b), A(c));
        else if (op == "eq") r = X.eq(A(a), A(b));
        else if (op == "ult") r = X.ult(A(a), A(b));
        else if (op == "ule") r = X.ule(A(a), A(b));
        else if (op == "slt") r = X.slt(A(a), A(b));
        else if (op == "sle") r = X.sle(A(a), A(b));
        else if (op == "popcnt") r = X.popcnt(A(a));
        else if (op == "clz") r = X.clz(A(a));
        else if (op == "ctz") r = X.ctz(A(a));
        else throw nb::value_error(("build: unknown op " + op).c_str());
        id[i] = r;
      }
      std::vector<Expr> out;
      for (int j : roots) { if (j < 0 || (size_t)j >= id.size()) throw nb::index_error(); out.push_back(Expr{e, id[j]}); }
      return out;
    }, nb::arg("nodes"), nb::arg("roots"),
       "Expressions from a node list (children first): (op, width, lo, a, b, c, k, name) as Expr.dag() gives them, plus 'sub';\n"
       "var: k = seed, the same name is the same input; extract: lo = low bit. Returns the Exprs of the roots (list indexes).")
    .def("const", [](EP e, u64 v, unsigned w) { return Expr{e, e->E.X.cst(v, w)}; }, nb::arg("value"), nb::arg("width") = 64)
    .def("eq", [](EP e, const Expr& a, const Expr& b) { return Expr{e, e->E.X.eq(a.id, b.id)}; })
    .def("ne", [](EP e, const Expr& a, const Expr& b) { return Expr{e, e->E.X.ne(a.id, b.id)}; })
    .def("lnot", [](EP e, const Expr& a) { return Expr{e, e->E.X.not_(a.id)}; });
}
