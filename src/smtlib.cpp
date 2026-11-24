#include "smtlib.hpp"
#include <cstdlib>
#include <map>
#include <memory>
#include <stdexcept>

namespace unshroud {

namespace {
struct SE { std::string atom; std::vector<SE> list; bool isList = false; };

struct Reader {
  const std::string& s; size_t i = 0;
  explicit Reader(const std::string& s) : s(s) {}
  void skip() {
    for (;;) {
      while (i < s.size() && isspace((unsigned char)s[i])) i++;
      if (i < s.size() && s[i] == ';') { while (i < s.size() && s[i] != '\n') i++; continue; }
      break;
    }
  }
  bool next(SE& out) {
    skip();
    if (i >= s.size()) return false;
    if (s[i] == '(') {
      i++; out.isList = true;
      for (;;) {
        skip();
        if (i >= s.size()) throw std::runtime_error("unbalanced parenthesis");
        if (s[i] == ')') { i++; return true; }
        out.list.emplace_back(); next(out.list.back());
      }
    }
    if (s[i] == ')') throw std::runtime_error("unexpected )");
    size_t j = i;
    if (s[i] == '|') { j++; while (j < s.size() && s[j] != '|') j++; out.atom = s.substr(i + 1, j - i - 1); i = j + 1; return true; }
    while (j < s.size() && !isspace((unsigned char)s[j]) && s[j] != '(' && s[j] != ')') j++;
    out.atom = s.substr(i, j - i); i = j;
    return true;
  }
};

struct W { u32 lo = 0, hi = 0; unsigned w = 0; };   // w <= 64: lo only; else hi holds bits 64..w-1

struct Macro { std::vector<std::string> params; SE body; };

struct Eval {
  Ctx& X;
  std::map<std::string, W> names;
  std::map<std::string, Macro> macros;
  std::vector<std::map<std::string, W>> locals;
  explicit Eval(Ctx& X) : X(X) {}

  static unsigned sortWidth(const SE& s) {
    if (!s.isList && s.atom == "Bool") return 1;
    if (s.isList && s.list.size() == 3 && s.list[0].atom == "_" && s.list[1].atom == "BitVec") return (unsigned)std::stoul(s.list[2].atom);
    throw std::runtime_error("unsupported sort");
  }
  W one(u32 n) { return W{n, 0, X.W(n)}; }
  u32 n64(const W& v) { if (v.w > 64) throw std::runtime_error("a term wider than 64 bits used where it is not supported"); return v.lo; }
  W lookup(const std::string& a) {
    for (size_t k = locals.size(); k-- > 0;) { auto it = locals[k].find(a); if (it != locals[k].end()) return it->second; }
    auto it = names.find(a);
    if (it != names.end()) return it->second;
    if (a == "true") return one(X.cst(1, 1));
    if (a == "false") return one(X.cst(0, 1));
    if (a.size() > 2 && a[0] == '#' && a[1] == 'b') { unsigned w = (unsigned)a.size() - 2; if (w > 64) throw std::runtime_error("wide literal"); return one(X.cst(strtoull(a.c_str() + 2, nullptr, 2), w)); }
    if (a.size() > 2 && a[0] == '#' && a[1] == 'x') { unsigned w = 4 * ((unsigned)a.size() - 2); if (w > 64) throw std::runtime_error("wide literal"); return one(X.cst(strtoull(a.c_str() + 2, nullptr, 16), w)); }
    throw std::runtime_error("unknown symbol " + a);
  }
  // a wide value from a 64-bit one
  W widen(const W& v, unsigned to, bool sgn) {
    W r; r.w = to;
    if (v.w > 64) throw std::runtime_error("extension of a wide term");
    unsigned hw = to - 64;
    u32 lo = v.w == 64 ? v.lo : (sgn ? X.sext(v.lo, 64) : X.zext(v.lo, 64));
    r.lo = lo;
    r.hi = sgn ? X.sext(X.extract(lo, 63, 1), hw) : X.cst(0, hw);
    return r;
  }
  bool zeroHi(const W& v) { return v.w <= 64 || (X.isC(v.hi) && X.cv(v.hi) == 0); }
  bool signHi(const W& v) {      // the high part is the sign of the low part
    if (v.w <= 64) return false;
    const Node& h = X.N(v.hi);
    return h.op == O_SEXT && X.N(h.a).op == O_EXTRACT && X.N(h.a).a == v.lo && X.N(h.a).lo == 63;
  }
  W wideBin(const std::string& op, const W& a, const W& b) {
    W r; r.w = a.w; unsigned hw = a.w - 64;
    auto hiOf = [&](const W& v) { return v.w > 64 ? v.hi : X.cst(0, hw); };
    if (op == "bvudiv" || op == "bvurem") {
      if (!zeroHi(a) || !zeroHi(b)) throw std::runtime_error("wide division of wide values");
      r.lo = op == "bvudiv" ? X.udiv(a.lo, b.lo) : X.urem(a.lo, b.lo); r.hi = X.cst(0, hw); return r;
    }
    if (op == "bvsdiv" || op == "bvsrem") {
      if (!signHi(a) || !signHi(b)) throw std::runtime_error("wide signed division of wide values");
      r.lo = op == "bvsdiv" ? X.sdiv(a.lo, b.lo) : X.srem(a.lo, b.lo); r.hi = X.sext(X.extract(r.lo, 63, 1), hw); return r;
    }
    if (op == "bvmul") {
      u32 h;
      if (zeroHi(a) && zeroHi(b)) h = X.mulhu(a.lo, b.lo);
      else if (signHi(a) && signHi(b)) h = X.mulhs(a.lo, b.lo);
      else throw std::runtime_error("wide product of wide values");
      r.lo = X.mul(a.lo, b.lo); r.hi = hw == 64 ? h : X.extract(h, 0, hw); return r;
    }
    if (op == "bvadd" || op == "bvsub") {
      bool add = op == "bvadd";
      r.lo = add ? X.add(a.lo, b.lo) : X.sub(a.lo, b.lo);
      u32 c = add ? X.ult(r.lo, a.lo) : X.ult(a.lo, b.lo);
      r.hi = add ? X.add(X.add(hiOf(a), hiOf(b)), X.zext(c, hw)) : X.sub(X.sub(hiOf(a), hiOf(b)), X.zext(c, hw));
      return r;
    }
    if (op == "bvand") { r.lo = X.and_(a.lo, b.lo); r.hi = X.and_(hiOf(a), hiOf(b)); return r; }
    if (op == "bvor") { r.lo = X.or_(a.lo, b.lo); r.hi = X.or_(hiOf(a), hiOf(b)); return r; }
    if (op == "bvxor") { r.lo = X.xor_(a.lo, b.lo); r.hi = X.xor_(hiOf(a), hiOf(b)); return r; }
    throw std::runtime_error("unsupported wide operation " + op);
  }
  W extract(const W& v, unsigned h, unsigned l) {
    unsigned w = h - l + 1;
    if (v.w <= 64) return one(X.extract(v.lo, l, w));
    if (w > 64) throw std::runtime_error("wide extract");
    if (h < 64) return one(X.extract(v.lo, l, w));
    if (l >= 64) return one(X.extract(v.hi, l - 64, w));
    return one(X.concat(X.extract(v.hi, 0, h - 63), X.extract(v.lo, l, 64 - l)));
  }
  W concat(const W& a, const W& b) {
    unsigned w = a.w + b.w;
    if (w <= 64) return one(X.concat(n64(a), n64(b)));
    if (a.w > 64 || b.w > 64) throw std::runtime_error("concat of wide terms");
    W r; r.w = w;
    if (b.w == 64) { r.lo = b.lo; r.hi = a.lo; return r; }
    unsigned take = 64 - b.w;
    r.lo = X.concat(X.extract(a.lo, 0, take), b.lo); r.hi = X.extract(a.lo, take, a.w - take);
    return r;
  }
  u32 boolOf(const W& v) { if (v.w != 1) throw std::runtime_error("a Bool was expected"); return v.lo; }

  W apply(const std::string& op, std::vector<W>& a) {
    auto N = [&](size_t i) { return n64(a[i]); };
    auto need = [&](size_t n) { if (a.size() != n) throw std::runtime_error("arity of " + op); };
    if (op == "not") { need(1); return one(X.not_(boolOf(a[0]))); }
    if (op == "and" || op == "or" || op == "xor") {
      u32 r = boolOf(a[0]);
      for (size_t i = 1; i < a.size(); i++) r = op == "and" ? X.and_(r, boolOf(a[i])) : op == "or" ? X.or_(r, boolOf(a[i])) : X.xor_(r, boolOf(a[i]));
      return one(r);
    }
    if (op == "=>") { need(2); return one(X.or_(X.not_(boolOf(a[0])), boolOf(a[1]))); }
    if (op == "=" || op == "distinct") {
      need(2);
      u32 r;
      if (a[0].w > 64) r = X.and_(X.eq(a[0].lo, a[1].lo), X.eq(a[0].hi, a[1].hi));
      else r = X.eq(N(0), N(1));
      return one(op == "=" ? r : X.not_(r));
    }
    if (op == "ite") {
      need(3); u32 c = boolOf(a[0]);
      if (a[1].w > 64) { W r; r.w = a[1].w; r.lo = X.ite(c, a[1].lo, a[2].lo); r.hi = X.ite(c, a[1].hi, a[2].hi); return r; }
      return one(X.ite(c, N(1), N(2)));
    }
    if (op == "concat") { W r = a[0]; for (size_t i = 1; i < a.size(); i++) r = concat(r, a[i]); return r; }
    if (a.size() == 2 && (a[0].w > 64 || a[1].w > 64)) return wideBin(op, a[0], a[1]);
    if (op == "bvnot") { need(1); return one(X.not_(N(0))); }
    if (op == "bvneg") { need(1); return one(X.neg(N(0))); }
    if (op == "bvadd" || op == "bvmul" || op == "bvand" || op == "bvor" || op == "bvxor") {
      u32 r = N(0);
      for (size_t i = 1; i < a.size(); i++) {
        u32 b = N(i);
        r = op == "bvadd" ? X.add(r, b) : op == "bvmul" ? X.mul(r, b) : op == "bvand" ? X.and_(r, b) : op == "bvor" ? X.or_(r, b) : X.xor_(r, b);
      }
      return one(r);
    }
    need(2);
    u32 x = N(0), y = N(1);
    if (op == "bvsub") return one(X.sub(x, y));
    if (op == "bvudiv") return one(X.udiv(x, y));
    if (op == "bvurem") return one(X.urem(x, y));
    if (op == "bvsdiv") return one(X.sdiv(x, y));
    if (op == "bvsrem") return one(X.srem(x, y));
    if (op == "bvsmod") {
      u32 u = X.srem(x, y); unsigned w = X.W(x);
      u32 same = X.eq(X.extract(x, w - 1, 1), X.extract(y, w - 1, 1));
      return one(X.ite(X.or_(X.eq(u, X.cst(0, w)), same), u, X.add(u, y)));
    }
    if (op == "bvshl") return one(X.shl(x, y));
    if (op == "bvlshr") return one(X.lshr(x, y));
    if (op == "bvashr") return one(X.ashr(x, y));
    if (op == "bvnand") return one(X.not_(X.and_(x, y)));
    if (op == "bvnor") return one(X.not_(X.or_(x, y)));
    if (op == "bvxnor") return one(X.not_(X.xor_(x, y)));
    if (op == "bvcomp") return one(X.eq(x, y));
    if (op == "bvult") return one(X.ult(x, y));
    if (op == "bvule") return one(X.ule(x, y));
    if (op == "bvugt") return one(X.ult(y, x));
    if (op == "bvuge") return one(X.ule(y, x));
    if (op == "bvslt") return one(X.slt(x, y));
    if (op == "bvsle") return one(X.sle(x, y));
    if (op == "bvsgt") return one(X.slt(y, x));
    if (op == "bvsge") return one(X.sle(y, x));
    throw std::runtime_error("unsupported operator " + op);
  }
  W term(const SE& e) {
    if (!e.isList) return lookup(e.atom);
    if (e.list.empty()) throw std::runtime_error("empty application");
    const SE& h = e.list[0];
    if (!h.isList && h.atom == "_") {               // (_ bvN W)
      if (e.list.size() == 3 && e.list[1].atom.rfind("bv", 0) == 0) {
        unsigned w = (unsigned)std::stoul(e.list[2].atom);
        if (w > 64) { u64 v = std::stoull(e.list[1].atom.substr(2)); W r; r.w = w; r.lo = X.cst(v, 64); r.hi = X.cst(0, w - 64); return r; }
        return one(X.cst(std::stoull(e.list[1].atom.substr(2)), w));
      }
      throw std::runtime_error("unsupported indexed constant");
    }
    if (h.isList) {                                  // ((_ op i j) t)
      if (h.list.size() < 3 || h.list[0].atom != "_") throw std::runtime_error("unsupported head");
      const std::string& op = h.list[1].atom;
      W t = term(e.list[1]);
      unsigned i0 = (unsigned)std::stoul(h.list[2].atom);
      if (op == "extract") return extract(t, i0, (unsigned)std::stoul(h.list[3].atom));
      if (op == "zero_extend" || op == "sign_extend") {
        if (i0 == 0) return t;
        unsigned to = t.w + i0;
        if (to <= 64) return one(op == "zero_extend" ? X.zext(n64(t), to) : X.sext(n64(t), to));
        return widen(t, to, op == "sign_extend");
      }
      if (op == "rotate_left" || op == "rotate_right") { u32 x = n64(t); u32 c = X.cst(i0 % X.W(x), X.W(x)); return one(op == "rotate_left" ? X.rol(x, c) : X.ror(x, c)); }
      if (op == "repeat") { u32 x = n64(t), r = x; for (unsigned k = 1; k < i0; k++) r = X.concat(r, x); return one(r); }
      throw std::runtime_error("unsupported indexed operator " + op);
    }
    const std::string& op = h.atom;
    if (op == "let") {
      std::map<std::string, W> scope;
      for (const SE& b : e.list[1].list) scope[b.list[0].atom] = term(b.list[1]);
      locals.push_back(std::move(scope));
      W r = term(e.list[2]);
      locals.pop_back();
      return r;
    }
    if (op == "!") return term(e.list[1]);
    std::vector<W> args;
    for (size_t k = 1; k < e.list.size(); k++) args.push_back(term(e.list[k]));
    auto m = macros.find(op);
    if (m != macros.end()) {
      std::map<std::string, W> scope;
      for (size_t k = 0; k < m->second.params.size(); k++) scope[m->second.params[k]] = args.at(k);
      locals.push_back(std::move(scope));
      W r = term(m->second.body);
      locals.pop_back();
      return r;
    }
    return apply(op, args);
  }
};
}  // namespace

bool parseSmt2(Ctx& X, const std::string& text, std::vector<u32>& asserts, std::string& err) {
  try {
    Reader rd(text); Eval ev(X);
    SE cmd;
    while (cmd = SE(), rd.next(cmd)) {
      if (!cmd.isList || cmd.list.empty()) continue;
      const std::string& c = cmd.list[0].atom;
      if (c == "declare-fun" || c == "declare-const") {
        const SE& sortE = c == "declare-fun" ? cmd.list[3] : cmd.list[2];
        unsigned w = Eval::sortWidth(sortE);
        if (w > 64) throw std::runtime_error("variable wider than 64 bits");
        ev.names[cmd.list[1].atom] = ev.one(X.var(cmd.list[1].atom, w, 0));
      } else if (c == "define-fun") {
        const SE& params = cmd.list[2];
        if (params.list.empty()) ev.names[cmd.list[1].atom] = ev.term(cmd.list[4]);
        else { Macro m; for (const SE& p : params.list) m.params.push_back(p.list[0].atom); m.body = cmd.list[4]; ev.macros[cmd.list[1].atom] = std::move(m); }
      } else if (c == "assert") {
        asserts.push_back(ev.boolOf(ev.term(cmd.list[1])));
      }
    }
    return true;
  } catch (const std::exception& e) { err = e.what(); return false; }
}

}  // namespace unshroud
