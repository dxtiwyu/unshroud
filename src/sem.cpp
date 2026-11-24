// unshroud - x86-64 semantics. Every operation computes the concrete result; an expression is built only when an operand has one.
#include "engine.hpp"
#include <Zydis/Zydis.h>
#include <intrin.h>
#include <cstdio>

namespace unshroud {

static inline u64 M(unsigned w) { return maskOf(w); }
static inline u32 SX(Ctx& X, Val a, unsigned w) { return a.s ? a.s : X.cst(a.c, w); }

// ------------------------------------------------------------------------------------------------ value operations
static inline Val vadd(Ctx& X, Val a, Val b, unsigned w) { return {(a.c + b.c) & M(w), (a.s | b.s) ? X.add(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vsub(Ctx& X, Val a, Val b, unsigned w) { return {(a.c - b.c) & M(w), (a.s | b.s) ? X.sub(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vmul(Ctx& X, Val a, Val b, unsigned w) { return {(a.c * b.c) & M(w), (a.s | b.s) ? X.mul(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vand(Ctx& X, Val a, Val b, unsigned w) { return {a.c & b.c, (a.s | b.s) ? X.and_(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vor(Ctx& X, Val a, Val b, unsigned w) { return {a.c | b.c, (a.s | b.s) ? X.or_(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vxor(Ctx& X, Val a, Val b, unsigned w) { return {a.c ^ b.c, (a.s | b.s) ? X.xor_(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vnot(Ctx& X, Val a, unsigned w) { return {(~a.c) & M(w), a.s ? X.not_(a.s) : 0}; }
static inline Val vneg(Ctx& X, Val a, unsigned w) { return {(0 - a.c) & M(w), a.s ? X.neg(a.s) : 0}; }
static inline Val vext(Ctx& X, Val a, unsigned lo, unsigned w) { return {(a.c >> lo) & M(w), a.s ? X.extract(a.s, lo, w) : 0}; }
static inline Val vzext(Ctx& X, Val a, unsigned from, unsigned w) { (void)from; return {a.c, a.s ? X.zext(a.s, w) : 0}; }
static inline Val vsext(Ctx& X, Val a, unsigned from, unsigned w) { return {(u64)sx(a.c, from) & M(w), a.s ? X.sext(a.s, w) : 0}; }
static inline Val vcat(Ctx& X, Val h, Val l, unsigned wh, unsigned wl) { return {((h.c << wl) | l.c) & M(wh + wl), (h.s | l.s) ? X.concat(SX(X, h, wh), SX(X, l, wl)) : 0}; }
static inline Val vite(Ctx& X, Val c, Val t, Val f, unsigned w) {
  if (!c.s) return (c.c & 1) ? t : f;
  return {(c.c & 1) ? t.c : f.c, X.ite(c.s, SX(X, t, w), SX(X, f, w))};
}
static inline Val vbit(Ctx& X, Val a, unsigned i) { return {(a.c >> i) & 1, a.s ? X.extract(a.s, i, 1) : 0}; }
static inline Val vb(bool c) { return {(u64)c, 0}; }
static inline Val vnot1(Ctx& X, Val a) { return {a.c ^ 1, a.s ? X.not_(a.s) : 0}; }
static inline Val vor1(Ctx& X, Val a, Val b) { return {a.c | b.c, (a.s | b.s) ? X.or_(SX(X, a, 1), SX(X, b, 1)) : 0}; }
static inline Val vand1(Ctx& X, Val a, Val b) { return {a.c & b.c, (a.s | b.s) ? X.and_(SX(X, a, 1), SX(X, b, 1)) : 0}; }
static inline Val vxor1(Ctx& X, Val a, Val b) { return {a.c ^ b.c, (a.s | b.s) ? X.xor_(SX(X, a, 1), SX(X, b, 1)) : 0}; }
static inline Val veq(Ctx& X, Val a, Val b, unsigned w) { return {a.c == b.c, (a.s | b.s) ? X.eq(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vult(Ctx& X, Val a, Val b, unsigned w) { return {a.c < b.c, (a.s | b.s) ? X.ult(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vule(Ctx& X, Val a, Val b, unsigned w) { return {a.c <= b.c, (a.s | b.s) ? X.ule(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vslt(Ctx& X, Val a, Val b, unsigned w) { return {sx(a.c, w) < sx(b.c, w), (a.s | b.s) ? X.slt(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vsle(Ctx& X, Val a, Val b, unsigned w) { return {sx(a.c, w) <= sx(b.c, w), (a.s | b.s) ? X.sle(SX(X, a, w), SX(X, b, w)) : 0}; }
static inline Val vshlc(Ctx& X, Val a, unsigned c, unsigned w) { return {c >= w ? 0 : (a.c << c) & M(w), a.s ? X.shl(a.s, X.cst(c, w)) : 0}; }
static inline Val vshrc(Ctx& X, Val a, unsigned c, unsigned w) { return {c >= w ? 0 : a.c >> c, a.s ? X.lshr(a.s, X.cst(c, w)) : 0}; }
static inline Val vsarc(Ctx& X, Val a, unsigned c, unsigned w) { return {(u64)(sx(a.c, w) >> (c >= w ? w - 1 : c)) & M(w), a.s ? X.ashr(a.s, X.cst(c, w)) : 0}; }
static inline Val vrolc(Ctx& X, Val a, unsigned c, unsigned w) { c %= w; return {c ? ((a.c << c) | (a.c >> (w - c))) & M(w) : a.c, a.s ? X.rol(a.s, X.cst(c, w)) : 0}; }
static inline Val vrorc(Ctx& X, Val a, unsigned c, unsigned w) { c %= w; return {c ? ((a.c >> c) | (a.c << (w - c))) & M(w) : a.c, a.s ? X.ror(a.s, X.cst(c, w)) : 0}; }
static inline Val vresize(Ctx& X, Val a, unsigned from, unsigned to) {
  if (from == to) return a;
  if (to < from) return vext(X, a, 0, to);
  return vzext(X, a, from, to);
}

// ------------------------------------------------------------------------------------------------ operands
struct Loc { u8 kind = 0, reg = 0, roff = 0, size = 0; u64 addr = 0; };   // kind 1: GPR, 2: memory, 3: immediate

static Val ea(Engine& E, const Insn& I, const Opnd& o) {
  Ctx& X = E.X;
  u64 k = (u64)o.disp; u64 c = (u64)o.disp; u32 parts = 0;
  if (o.base == 16) { k += I.next; c += I.next; }
  else if (o.base != 0xff) { c += E.g[o.base]; if (E.gs[o.base]) parts = E.gs[o.base]; else k += E.g[o.base]; }
  if (o.index != 0xff) {
    c += E.g[o.index] * o.scale;
    if (E.gs[o.index]) { u32 t = X.mul(E.gs[o.index], X.cst(o.scale, 64)); parts = parts ? X.add(parts, t) : t; }
    else k += E.g[o.index] * o.scale;
  }
  u32 s = parts ? X.add(parts, X.cst(k, 64)) : 0;
  if (I.asz == 4) { c &= 0xffffffffull; if (s) s = X.zext(X.extract(s, 0, 32), 64); }
  u64 seg = o.seg == RK_FS ? E.fsbase : o.seg == RK_GS ? E.gsbase : 0;
  if (seg) { c += seg; if (s) s = X.add(s, X.cst(seg, 64)); }
  return {c, s};
}

static u64 addrOf(Engine& E, const Insn& I, const Opnd& o) {
  Val a = ea(E, I, o);
  if (a.s) E.concretized(a.s, a.c, 64, I.addr, 1);
  return a.c;
}

static Loc loc(Engine& E, const Insn& I, int i) {
  const Opnd& o = I.op[i]; Loc l; l.size = o.size;
  if (o.type == OT_REG && o.rk == RK_GPR) { l.kind = 1; l.reg = o.reg; l.roff = o.roff; }
  else if (o.type == OT_MEM) { l.kind = 2; l.addr = addrOf(E, I, o); }
  else if (o.type == OT_IMM) { l.kind = 3; l.addr = (u64)o.disp; }
  else throw (int)ST_UNSUPPORTED;
  return l;
}

static Val rdGpr(Engine& E, int r, unsigned size, unsigned roff) {
  u64 c = E.g[r]; u32 s = E.gs[r];
  if (size == 8) return {c, s};
  unsigned w = size * 8;
  return {(c >> (roff * 8)) & M(w), s ? E.X.extract(s, roff * 8, w) : 0};
}

static void wrGpr(Engine& E, int r, unsigned size, unsigned roff, Val v) {
  Ctx& X = E.X;
  if (v.s && v.s < LAZY_BASE && E.plainConst(v.s)) v.s = 0;
  if (size == 8) { E.g[r] = v.c; E.gs[r] = v.s; return; }
  if (size == 4) { E.g[r] = v.c & 0xffffffffull; E.gs[r] = v.s ? X.zext(v.s, 64) : 0; return; }
  unsigned w = size * 8, sh = roff * 8;
  u64 m = M(w) << sh, old = E.g[r]; u32 olds = E.gs[r];
  E.g[r] = (old & ~m) | ((v.c << sh) & m);
  if (!v.s && !olds) { E.gs[r] = 0; return; }
  u32 oe = olds ? olds : X.cst(old, 64), ve = SX(X, v, w);
  if (sh == 0) E.gs[r] = X.concat(X.extract(oe, w, 64 - w), ve);
  else E.gs[r] = X.concat(X.extract(oe, sh + w, 64 - sh - w), X.concat(ve, X.extract(oe, 0, sh)));
  if (E.gs[r] < LAZY_BASE && E.plainConst(E.gs[r])) E.gs[r] = 0;
}

static Val get(Engine& E, const Loc& l, unsigned w) {
  if (l.kind == 1) return rdGpr(E, l.reg, l.size, l.roff);
  if (l.kind == 2) return E.load(l.addr, l.size);
  return {l.addr & M(w), 0};
}

static void put(Engine& E, const Loc& l, Val v) {
  if (l.kind == 1) wrGpr(E, l.reg, l.size, l.roff, v);
  else if (l.kind == 2) E.store(l.addr, l.size, v);
}

// read operand i at width w (immediates: their sign-extended value masked to w)
static Val rd(Engine& E, const Insn& I, int i, unsigned w) {
  const Opnd& o = I.op[i];
  if (o.type == OT_IMM) return {(u64)o.disp & M(w), 0};
  if (o.type == OT_REG && o.rk == RK_GPR) return rdGpr(E, o.reg, o.size, o.roff);
  if (o.type == OT_MEM) {
    Val a = ea(E, I, o);
    if (a.s) { if (E.dbWatch) E.dataCheck(a.c, o.size, false); Val v; if (E.tableLoad(a, o.size, v)) return v; E.concretized(a.s, a.c, 64, I.addr, 1); }
    return E.load(a.c, o.size);
  }
  if (o.type == OT_REG && o.rk == RK_RIP) return {I.next, 0};
  if (o.type == OT_REG && (o.rk == RK_SEG0 || o.rk == RK_FS || o.rk == RK_GS)) {
    static const u64 sel[6] = {0x2b, 0x33, 0x2b, 0x2b, 0x53, 0x2b};      // es cs ss ds fs gs of a 64-bit Windows process
    return {(o.reg == 2 ? E.ssSel : sel[o.reg < 6 ? o.reg : 0]) & M(w), 0};
  }
  throw (int)ST_UNSUPPORTED;
}

static void wr(Engine& E, const Insn& I, int i, Val v) {
  const Opnd& o = I.op[i];
  if (o.type == OT_REG && o.rk == RK_GPR) wrGpr(E, o.reg, o.size, o.roff, v);
  else if (o.type == OT_MEM) E.store(addrOf(E, I, o), o.size, v);
  else if (o.type == OT_REG && (o.rk == RK_SEG0 || o.rk == RK_FS || o.rk == RK_GS)) {}
  else throw (int)ST_UNSUPPORTED;
}

// (a stack pointer which holds an expression keeps it exact: the expression moves with the value)
static inline void spMove(Engine& E, i64 d) { E.g[RSP] += (u64)d; if (E.gs[RSP]) E.gs[RSP] = E.X.add(E.gs[RSP], E.X.cst((u64)d, 64)); }
static void push(Engine& E, Val v, unsigned size) { spMove(E, -(i64)size); E.store(E.g[RSP], size, v); }
static Val pop(Engine& E, unsigned size) { Val v = E.load(E.g[RSP], size); spMove(E, size); return v; }

// ------------------------------------------------------------------------------------------------ flags
static inline unsigned bitpos(u32 bit) { unsigned long i; _BitScanForward(&i, bit); return (unsigned)i; }
static inline u64 parity8(u64 v) { return (~__popcnt((unsigned)(v & 0xff))) & 1; }

static u64 lazyFlagC(const Flags& f, u32 bit) {
  const unsigned w = f.w; const u64 a = f.a, b = f.b, r = f.r, x = f.x, sb = signBit(w);
  switch (bit) {
  case FL_CF:
    switch (f.op) {
    case LF_ADD: return r < a;
    case LF_ADC: return x ? r <= a : r < a;
    case LF_SUB: return a < b;
    case LF_SBB: return x ? a <= b : a < b;
    case LF_NEG: return a != 0;
    case LF_SHL: return x > w ? 0 : (a >> (w - x)) & 1;
    case LF_SHR: return x > w ? 0 : (a >> (x - 1)) & 1;
    case LF_SAR: return (u64)(sx(a, w) >> (x >= w ? w - 1 : x - 1)) & 1;
    case LF_MUL: return x != 0;
    case LF_IMUL: return x != ((u64)(sx(r, w) >> (w - 1)) & M(w));
    case LF_IMUL2: return evalOp(O_MULHS, w, 0, 0, a, b, 0) != ((u64)(sx(r, w) >> (w - 1)) & M(w));
    case LF_ROL: return r & 1;
    case LF_ROR: return (r >> (w - 1)) & 1;
    default: return 0;
    }
  case FL_OF:
    switch (f.op) {
    case LF_ADD: case LF_ADC: return (((a ^ r) & (b ^ r)) & sb) != 0;
    case LF_SUB: case LF_SBB: return (((a ^ b) & (a ^ r)) & sb) != 0;
    case LF_INC: return r == sb;
    case LF_DEC: return a == sb;
    case LF_NEG: return a == sb;
    case LF_SHL: return x > w ? 0 : (((r & sb) != 0) ^ ((a >> (w - x)) & 1));
    case LF_SHR: return ((r >> (w - 1)) ^ (r >> (w - 2))) & 1;      // (one bit: the sign changed; more: what this CPU gives)
    case LF_MUL: return x != 0;
    case LF_IMUL: return x != ((u64)(sx(r, w) >> (w - 1)) & M(w));
    case LF_IMUL2: return evalOp(O_MULHS, w, 0, 0, a, b, 0) != ((u64)(sx(r, w) >> (w - 1)) & M(w));
    case LF_ROL: return ((r >> (w - 1)) ^ r) & 1;
    case LF_ROR: return ((r >> (w - 1)) ^ (r >> (w - 2))) & 1;
    default: return 0;
    }
  case FL_ZF: return r == 0;
  case FL_SF: return (r & sb) != 0;
  case FL_PF: return parity8(r);
  case FL_AF:
    switch (f.op) {
    case LF_ADD: case LF_ADC: case LF_SUB: case LF_SBB: return ((a ^ b ^ r) >> 4) & 1;
    case LF_INC: case LF_DEC: return ((a ^ 1 ^ r) >> 4) & 1;
    case LF_NEG: return ((a ^ r) >> 4) & 1;
    case LF_SHL: case LF_SHR: case LF_SAR: return 1;     // undefined in the manuals: set on AMD Zen
    default: return 0;
    }
  }
  return 0;
}

static u32 parityExpr(Ctx& X, u32 R) {
  u32 b = X.extract(R, 0, 8);
  u32 p = X.extract(b, 0, 1);
  for (unsigned i = 1; i < 8; i++) p = X.xor_(p, X.extract(b, i, 1));
  return X.not_(p);
}

static u32 lazyFlagS(Engine& E, const Flags& f, u32 bit) {
  Ctx& X = E.X; const unsigned w = f.w;
  auto A = [&]() { return SX(X, {f.a, f.sa}, w); };
  auto B = [&]() { return SX(X, {f.b, f.sb}, w); };
  auto R = [&]() { return SX(X, {f.r, f.sr}, w); };
  auto C1 = [&]() { return SX(X, {f.x, f.sx}, 1); };
  switch (bit) {
  case FL_CF:
    switch (f.op) {
    case LF_ADD: return X.ult(R(), A());
    case LF_ADC: return X.ite(C1(), X.ule(R(), A()), X.ult(R(), A()));
    case LF_SUB: return X.ult(A(), B());
    case LF_SBB: return X.ite(C1(), X.ule(A(), B()), X.ult(A(), B()));
    case LF_NEG: return X.not_(X.eq(A(), X.cst(0, w)));
    case LF_SHL:
      if (f.sx) return X.extract(X.lshr(A(), X.sub(X.cst(w, w), X.zext(f.sx, w))), 0, 1);       // bit w - count
      return f.x > w ? X.cst(0, 1) : X.extract(A(), w - (unsigned)f.x, 1);
    case LF_SHR:
      if (f.sx) return X.extract(X.lshr(A(), X.sub(X.zext(f.sx, w), X.cst(1, w))), 0, 1);       // bit count - 1
      return f.x > w ? X.cst(0, 1) : X.extract(A(), (unsigned)f.x - 1, 1);
    case LF_SAR:
      if (f.sx) return X.extract(X.ashr(A(), X.sub(X.zext(f.sx, w), X.cst(1, w))), 0, 1);
      return X.extract(A(), f.x >= w ? w - 1 : (unsigned)f.x - 1, 1);
    case LF_MUL: return X.not_(X.eq(SX(X, {f.x, f.sx}, w), X.cst(0, w)));
    case LF_IMUL: return X.not_(X.eq(SX(X, {f.x, f.sx}, w), X.ashr(R(), X.cst(w - 1, w))));
    case LF_IMUL2: return X.not_(X.eq(X.mulhs(A(), B()), X.ashr(R(), X.cst(w - 1, w))));
    case LF_ROL: return X.extract(R(), 0, 1);
    case LF_ROR: return X.extract(R(), w - 1, 1);
    default: return X.cst(0, 1);
    }
  case FL_OF: {
    u32 msb;
    switch (f.op) {
    case LF_ADD: case LF_ADC: return X.extract(X.and_(X.xor_(A(), R()), X.xor_(B(), R())), w - 1, 1);
    case LF_SUB: case LF_SBB: return X.extract(X.and_(X.xor_(A(), B()), X.xor_(A(), R())), w - 1, 1);
    case LF_INC: return X.eq(R(), X.cst(signBit(w), w));
    case LF_DEC: case LF_NEG: return X.eq(A(), X.cst(signBit(w), w));
    case LF_SHL:
      if (f.sx) return X.xor_(X.extract(R(), w - 1, 1), X.extract(X.lshr(A(), X.sub(X.cst(w, w), X.zext(f.sx, w))), 0, 1));
      if (f.x > w) return X.cst(0, 1);
      msb = X.extract(R(), w - 1, 1);
      return X.xor_(msb, X.extract(A(), w - (unsigned)f.x, 1));
    case LF_SHR: return X.xor_(X.extract(R(), w - 1, 1), X.extract(R(), w - 2, 1));
    case LF_MUL: return X.not_(X.eq(SX(X, {f.x, f.sx}, w), X.cst(0, w)));
    case LF_IMUL: return X.not_(X.eq(SX(X, {f.x, f.sx}, w), X.ashr(R(), X.cst(w - 1, w))));
    case LF_IMUL2: return X.not_(X.eq(X.mulhs(A(), B()), X.ashr(R(), X.cst(w - 1, w))));
    case LF_ROL: return X.xor_(X.extract(R(), w - 1, 1), X.extract(R(), 0, 1));
    case LF_ROR: return X.xor_(X.extract(R(), w - 1, 1), X.extract(R(), w - 2, 1));
    default: return X.cst(0, 1);
    }
  }
  case FL_ZF: return X.eq(R(), X.cst(0, w));
  case FL_SF: return X.extract(R(), w - 1, 1);
  case FL_PF: return parityExpr(X, R());
  case FL_AF:
    switch (f.op) {
    case LF_ADD: case LF_ADC: case LF_SUB: case LF_SBB: return w >= 8 ? X.extract(X.xor_(X.xor_(A(), B()), R()), 4, 1) : X.cst(0, 1);
    case LF_INC: case LF_DEC: return w >= 8 ? X.extract(X.xor_(X.xor_(A(), X.cst(1, w)), R()), 4, 1) : X.cst(0, 1);
    case LF_NEG: return w >= 8 ? X.extract(X.xor_(A(), R()), 4, 1) : X.cst(0, 1);
    case LF_SHL: case LF_SHR: case LF_SAR: return X.cst(1, 1);
    default: return X.cst(0, 1);
    }
  }
  return X.cst(0, 1);
}

static Flags fromPrev(const Flags& f) {
  Flags g; g.op = f.prev.op; g.w = f.prev.w; g.lazy = f.prev.lazy; g.a = f.prev.a; g.b = f.prev.b; g.r = f.prev.r; g.x = f.prev.x;
  g.sa = f.prev.sa; g.sb = f.prev.sb; g.sr = f.prev.sr; g.sx = f.prev.sx; return g;
}

Val Engine::flag(u32 bit) {
  unsigned pos = bitpos(bit);
  if (fl.lazy & bit) {
    u64 c = lazyFlagC(fl, bit);
    u32 s = 0;
    if (fl.sa | fl.sb | fl.sr | fl.sx) { s = lazyFlagS(*this, fl, bit); if (X.isC(s)) s = 0; }
    return {c, s};
  }
  if (fl.prev.lazy & bit) {
    Flags g = fromPrev(fl);
    u64 c = lazyFlagC(g, bit);
    u32 s = 0;
    if (g.sa | g.sb | g.sr | g.sx) { s = lazyFlagS(*this, g, bit); if (X.isC(s)) s = 0; }
    return {c, s};
  }
  return {(fl.bits >> pos) & 1, fl.sym[pos]};
}

u32 Engine::flagExpr(u32 bit) { return flag(bit).s; }

static void setFlag(Engine& E, u32 bit, Val v) {
  unsigned pos = bitpos(bit);
  E.fl.lazy &= ~bit; E.fl.prev.lazy &= ~bit;
  E.fl.bits = (E.fl.bits & ~(1ull << pos)) | ((v.c & 1) << pos);
  E.fl.sym[pos] = (v.s && !E.X.isC(v.s)) ? v.s : 0;
  if (v.s && !E.fl.sym[pos]) E.fl.folded |= bit; else E.fl.folded &= ~bit;
}

static void materialize(Engine& E, u32 mask) {
  mask &= (E.fl.lazy | E.fl.prev.lazy);
  for (u32 bit : {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF})
    if (mask & bit) { Val v = E.flag(bit); unsigned pos = bitpos(bit); E.fl.bits = (E.fl.bits & ~(1ull << pos)) | ((v.c & 1) << pos); E.fl.sym[pos] = v.s; }
  E.fl.lazy &= ~mask; E.fl.prev.lazy &= ~mask;
}

static void setLazy(Engine& E, u8 op, unsigned w, Val a, Val b, Val r, u32 mask = FL_ARITH, Val x = {0, 0}) {
  Flags& f = E.fl;
  // the flags of the current record this instruction does not set stay deferred, in the second record
  const u32 rest = f.lazy & ~mask;
  if (rest) {
    const u32 older = f.prev.lazy & ~mask & ~rest;          // a third generation: built now (rare)
    if (older) materialize(E, older);
    f.prev.op = f.op; f.prev.w = f.w; f.prev.lazy = rest; f.prev.a = f.a; f.prev.b = f.b; f.prev.r = f.r; f.prev.x = f.x;
    f.prev.sa = f.sa; f.prev.sb = f.sb; f.prev.sr = f.sr; f.prev.sx = f.sx;
  } else f.prev.lazy &= ~mask;
  f.op = op; f.w = (u8)w; f.a = a.c; f.sa = a.s; f.b = b.c; f.sb = b.s; f.r = r.c; f.sr = r.s; f.x = x.c; f.sx = x.s;
  f.lazy = mask; f.folded &= ~mask;
  for (u32 bit : {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF}) if (mask & bit) f.sym[bitpos(bit)] = 0;
}

// condition codes, Intel order: o no b ae e ne be a s ns p np l ge le g
Val Engine::cond(unsigned cc) {
  const unsigned base = cc >> 1; const bool inv = cc & 1;
  static const u32 need[8] = {FL_OF, FL_CF, FL_ZF, FL_CF | FL_ZF, FL_SF, FL_PF, FL_SF | FL_OF, FL_ZF | FL_SF | FL_OF};
  Val r{0, 0};
  bool done = false;
  if ((fl.lazy & need[base]) == need[base] && (fl.op == LF_SUB || fl.op == LF_LOGIC)) {
    const unsigned w = fl.w; Val a{fl.a, fl.sa}, b{fl.b, fl.sb}, res{fl.r, fl.sr}, z{0, 0};
    done = true;
    if (fl.op == LF_SUB) {
      switch (base) {
      case 1: r = vult(X, a, b, w); break;
      case 2: r = veq(X, a, b, w); break;
      case 3: r = vule(X, a, b, w); break;
      case 6: r = vslt(X, a, b, w); break;
      case 7: r = vsle(X, a, b, w); break;
      default: done = false;
      }
    } else {
      switch (base) {
      case 0: case 1: r = vb(false); break;
      case 2: case 3: r = veq(X, res, z, w); break;
      case 6: r = vslt(X, res, z, w); break;
      case 7: r = vsle(X, res, z, w); break;
      default: done = false;
      }
    }
  }
  if (!done) {
    switch (base) {
    case 0: r = flag(FL_OF); break;
    case 1: r = flag(FL_CF); break;
    case 2: r = flag(FL_ZF); break;
    case 3: r = vor1(X, flag(FL_CF), flag(FL_ZF)); break;
    case 4: r = flag(FL_SF); break;
    case 5: r = flag(FL_PF); break;
    case 6: r = vxor1(X, flag(FL_SF), flag(FL_OF)); break;
    default: r = vor1(X, flag(FL_ZF), vxor1(X, flag(FL_SF), flag(FL_OF))); break;
    }
  }
  // decided by flags made from values which depend on the inputs, and a constant all the same: the rules proved it
  if (r.s && X.isC(r.s)) r.s = 0;
  condFolded = false;
  if (!r.s) {
    for (u32 bit : {FL_OF, FL_CF, FL_ZF, FL_SF, FL_PF}) {
      if (!(need[base] & bit)) continue;
      if (fl.lazy & bit) condFolded = condFolded || (fl.sa | fl.sb | fl.sr | fl.sx) != 0;
      else if (fl.prev.lazy & bit) condFolded = condFolded || (fl.prev.sa | fl.prev.sb | fl.prev.sr | fl.prev.sx) != 0;
      else condFolded = condFolded || (fl.folded & bit) != 0;
    }
  }
  return inv ? vnot1(X, r) : r;
}

u64 Engine::rflags() {
  // the values only: no expression is built (this is what native execution and snapshots of the flags ask for)
  u64 v = (fl.bits & ~(u64)FL_ARITH) | 2;
  for (u32 bit : {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF}) {
    const unsigned pos = bitpos(bit);
    u64 c;
    if (fl.lazy & bit) c = lazyFlagC(fl, bit);
    else if (fl.prev.lazy & bit) c = lazyFlagC(fromPrev(fl), bit);
    else c = (fl.bits >> pos) & 1;
    v |= (c & 1) << pos;
  }
  return v;
}

// a flag made from values which depend on the inputs, constant by the rules (see Engine::cond)
static bool flagFolded(Engine& E, u32 bit) {
  const Flags& fl = E.fl;
  if (fl.lazy & bit) return (fl.sa | fl.sb | fl.sr | fl.sx) != 0;
  if (fl.prev.lazy & bit) return (fl.prev.sa | fl.prev.sb | fl.prev.sr | fl.prev.sx) != 0;
  return (fl.folded & bit) != 0;
}

static Val flagsVal(Engine& E) {
  Ctx& X = E.X;
  u64 c = E.rflags(); u32 s = 0; bool folded = false;
  for (u32 bit : {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF}) {
    Val f = E.flag(bit);
    if (!f.s) { folded = folded || flagFolded(E, bit); continue; }
    if (!s) s = X.cst(c, 64);
    unsigned pos = bitpos(bit);
    s = X.or_(X.and_(s, X.cst(~(1ull << pos), 64)), X.shl(X.zext(f.s, 64), X.cst(pos, 64)));
  }
  if (!s && folded) s = X.cst(c, 64);       // the value keeps saying where it comes from (a constant expression): popfq gives the mark back
  return {c, s};
}

static void setFlagsVal(Engine& E, Val v, u32 mask) {
  Ctx& X = E.X;
  for (u32 bit : {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF}) {
    if (!(mask & bit)) continue;
    unsigned pos = bitpos(bit);
    setFlag(E, bit, Val{(v.c >> pos) & 1, v.s ? X.extract(v.s, pos, 1) : 0});
  }
  if (mask & FL_DF) E.fl.bits = (E.fl.bits & ~(u64)FL_DF) | (v.c & FL_DF);
}

static inline bool df(Engine& E) { return (E.fl.bits & FL_DF) != 0; }

// a value made concrete: the path keeps the constraint which says so
static u64 concretize(Engine& E, const Insn& I, Val v, unsigned w) {
  if (v.s) E.concretized(v.s, v.c, w, I.addr, 3);
  return v.c;
}

static unsigned ccOf(u16 mn) {
  switch (mn) {
  case ZYDIS_MNEMONIC_JO: case ZYDIS_MNEMONIC_SETO: case ZYDIS_MNEMONIC_CMOVO: return 0;
  case ZYDIS_MNEMONIC_JNO: case ZYDIS_MNEMONIC_SETNO: case ZYDIS_MNEMONIC_CMOVNO: return 1;
  case ZYDIS_MNEMONIC_JB: case ZYDIS_MNEMONIC_SETB: case ZYDIS_MNEMONIC_CMOVB: return 2;
  case ZYDIS_MNEMONIC_JNB: case ZYDIS_MNEMONIC_SETNB: case ZYDIS_MNEMONIC_CMOVNB: return 3;
  case ZYDIS_MNEMONIC_JZ: case ZYDIS_MNEMONIC_SETZ: case ZYDIS_MNEMONIC_CMOVZ: return 4;
  case ZYDIS_MNEMONIC_JNZ: case ZYDIS_MNEMONIC_SETNZ: case ZYDIS_MNEMONIC_CMOVNZ: return 5;
  case ZYDIS_MNEMONIC_JBE: case ZYDIS_MNEMONIC_SETBE: case ZYDIS_MNEMONIC_CMOVBE: return 6;
  case ZYDIS_MNEMONIC_JNBE: case ZYDIS_MNEMONIC_SETNBE: case ZYDIS_MNEMONIC_CMOVNBE: return 7;
  case ZYDIS_MNEMONIC_JS: case ZYDIS_MNEMONIC_SETS: case ZYDIS_MNEMONIC_CMOVS: return 8;
  case ZYDIS_MNEMONIC_JNS: case ZYDIS_MNEMONIC_SETNS: case ZYDIS_MNEMONIC_CMOVNS: return 9;
  case ZYDIS_MNEMONIC_JP: case ZYDIS_MNEMONIC_SETP: case ZYDIS_MNEMONIC_CMOVP: return 10;
  case ZYDIS_MNEMONIC_JNP: case ZYDIS_MNEMONIC_SETNP: case ZYDIS_MNEMONIC_CMOVNP: return 11;
  case ZYDIS_MNEMONIC_JL: case ZYDIS_MNEMONIC_SETL: case ZYDIS_MNEMONIC_CMOVL: return 12;
  case ZYDIS_MNEMONIC_JNL: case ZYDIS_MNEMONIC_SETNL: case ZYDIS_MNEMONIC_CMOVNL: return 13;
  case ZYDIS_MNEMONIC_JLE: case ZYDIS_MNEMONIC_SETLE: case ZYDIS_MNEMONIC_CMOVLE: return 14;
  case ZYDIS_MNEMONIC_JNLE: case ZYDIS_MNEMONIC_SETNLE: case ZYDIS_MNEMONIC_CMOVNLE: return 15;
  default: return 16;
  }
}

Stop execVector(Engine& E, const Insn& I);   // sem_vec.cpp
static Stop execString(Engine& E, const Insn& I);

// ------------------------------------------------------------------------------------------------ 128-bit division (rare: rdx holds bits)
static bool udiv128(u64 hi, u64 lo, u64 d, u64& q, u64& r) {
  if (d == 0 || hi >= d) return false;
  u64 rem = hi, quo = 0;
  for (int i = 63; i >= 0; i--) {
    bool top = rem >> 63;
    rem = (rem << 1) | ((lo >> i) & 1);
    if (top || rem >= d) { rem -= d; quo |= 1ull << i; }
  }
  q = quo; r = rem; return true;
}

static void setFlag(Engine& E, u32 bit, Val v);
// after a division (undefined in the manuals; AMD Zen: PF = ZF = SF = 0, AF = 1, CF and OF kept)
static void divFlags(Engine& E) { setFlag(E, FL_PF, {0, 0}); setFlag(E, FL_AF, {1, 0}); setFlag(E, FL_ZF, {0, 0}); setFlag(E, FL_SF, {0, 0}); }

static Val bswapVal(Ctx& X, Val v, unsigned w) {
  u64 c = w == 64 ? _byteswap_uint64(v.c) : w == 32 ? _byteswap_ulong((unsigned long)v.c) : v.c;
  u32 s = 0;
  if (v.s) {
    for (unsigned i = 0; i < w / 8; i++) { u32 b = X.extract(v.s, i * 8, 8); s = s ? X.concat(s, b) : b; }
  }
  return {c, s};
}

#define C(m) case ZYDIS_MNEMONIC_##m:

Stop Engine::exec(const Insn& I) {
  Engine& E = *this;
  const unsigned w0 = I.op[0].size * 8;
  switch (I.mn) {
  // no shadow stack in this process: rdssp leaves its register as it was (longjmp reads it to see whether there is one)
  C(RDSSPD) C(RDSSPQ) return ST_NONE;
  C(NOP) C(ENDBR64) C(ENDBR32) C(PAUSE) C(LFENCE) C(MFENCE) C(SFENCE) C(PREFETCH) C(PREFETCHT0) C(PREFETCHT1)
  C(PREFETCHT2) C(PREFETCHNTA) C(PREFETCHW) C(CLFLUSH) C(CLFLUSHOPT) C(VZEROUPPER) C(EMMS)
    if (I.mn == ZYDIS_MNEMONIC_VZEROUPPER) { for (int r = 0; r < 16; r++) { memset(v[r] + 16, 0, 16); memset(vc[r] + 16, 0, 16 * sizeof(Cell)); } }
    return ST_NONE;

  C(MOV) {
    // control and debug registers are not a user program's: a privileged instruction
    if ((I.op[0].type == OT_REG && I.op[0].rk == RK_SYS) || (I.op[1].type == OT_REG && I.op[1].rk == RK_SYS)) { stopInfo = "privileged instruction"; trapKind = TK_PRIV; rip = I.addr; return ST_EXCEPTION; }
    if (I.op[0].type == OT_REG && I.op[0].rk != RK_GPR) {                    // segment registers
      if (I.op[0].reg != 2) return ST_NONE;                                   // (es ds fs gs: nothing a program sees changes)
      // ss: the selector is read (a fault there is this instruction's) and must be one a stack of user code may use, else
      // a general protection fault; a pending single step then waits for the next instruction (the CPU holds it back)
      const unsigned ws = I.op[1].size * 8;                                  // (mov ss, rax reads the low 16 bits)
      const u64 sel = concretize(E, I, rd(E, I, 1, ws), ws) & 0xffff;
      if (sel != 0x2b && sel != 0x53) { stopInfo = "general protection"; trapKind = TK_GP; rip = I.addr; return ST_EXCEPTION; }
      ssSel = (u16)sel; movSS = 1; dbgOn = 1;
      return ST_NONE;
    }
    wr(E, I, 0, rd(E, I, 1, w0));
    return ST_NONE;
  }
  C(MOVZX) { unsigned ws = I.op[1].size * 8; wr(E, I, 0, vzext(X, rd(E, I, 1, ws), ws, w0)); return ST_NONE; }
  C(MOVSX) C(MOVSXD) { unsigned ws = I.op[1].size * 8; Val s = rd(E, I, 1, ws); wr(E, I, 0, ws == w0 ? s : vsext(X, s, ws, w0)); return ST_NONE; }
  C(LEA) { Val a = ea(E, I, I.op[1]); a.c -= (I.op[1].seg == RK_FS ? fsbase : I.op[1].seg == RK_GS ? gsbase : 0); wr(E, I, 0, vresize(X, a, 64, w0)); return ST_NONE; }
  C(PUSH) { unsigned sz = I.opsz ? I.opsz : 8; push(E, rd(E, I, 0, sz * 8), sz); return ST_NONE; }
  C(POP) { unsigned sz = I.opsz ? I.opsz : 8; Val v = pop(E, sz); wr(E, I, 0, v); return ST_NONE; }
  C(PUSHFQ) C(PUSHF) { unsigned sz = I.mn == ZYDIS_MNEMONIC_PUSHF ? 2 : 8; Val f = flagsVal(E); push(E, sz == 8 ? f : vext(X, f, 0, 16), sz); return ST_NONE; }
  C(POPFQ) C(POPF) {
    unsigned sz = I.mn == ZYDIS_MNEMONIC_POPF ? 2 : 8; Val f = pop(E, sz); if (sz == 2) f = vzext(X, f, 16, 64);
    setFlagsVal(E, f, FL_ARITH | FL_DF);
    // ID, AC, NT and TF are the program's to write (IF and IOPL are not: they stay); TF: one more instruction, then a single-step trap
    const u64 keep = sz == 2 ? 0x4100ull : 0x244100ull;
    fl.bits = (fl.bits & ~keep) | (f.c & keep);
    if ((f.c & 0x100) && !tf) { tf = 1; dbgOn = 1; }   // (with TF on already, the trap comes after this very instruction)
    return ST_NONE;
  }
  C(LAHF) {
    Val r{2, 0};
    for (u32 bit : {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF}) { Val f = flag(bit); r = vor(X, r, vshlc(X, vzext(X, f, 1, 8), bitpos(bit), 8), 8); }
    wrGpr(E, RAX, 1, 1, r);
    return ST_NONE;
  }
  C(SAHF) { Val ah = rdGpr(E, RAX, 1, 1); setFlagsVal(E, vzext(X, ah, 8, 64), FL_CF | FL_PF | FL_AF | FL_ZF | FL_SF); return ST_NONE; }
  C(XCHG) { Loc a = loc(E, I, 0), b = loc(E, I, 1); Val va = get(E, a, w0), vb2 = get(E, b, w0); put(E, a, vb2); put(E, b, va); return ST_NONE; }
  C(XADD) {
    Loc d = loc(E, I, 0), s = loc(E, I, 1); Val a = get(E, d, w0), b = get(E, s, w0), r = vadd(X, a, b, w0);
    put(E, s, a); put(E, d, r); setLazy(E, LF_ADD, w0, a, b, r);
    return ST_NONE;
  }
  C(CMPXCHG) {
    Loc d = loc(E, I, 0); Val dv = get(E, d, w0), acc = rdGpr(E, RAX, w0 / 8, 0), sv = rd(E, I, 1, w0);
    Val r = vsub(X, acc, dv, w0); setLazy(E, LF_SUB, w0, acc, dv, r);
    Val same = veq(X, acc, dv, w0);
    if (!same.s) { if (same.c) put(E, d, sv); else { put(E, d, dv); wrGpr(E, RAX, w0 / 8, 0, dv); } }
    else { put(E, d, vite(X, same, sv, dv, w0)); wrGpr(E, RAX, w0 / 8, 0, vite(X, same, acc, dv, w0)); }
    return ST_NONE;
  }
  C(BSWAP) { Val a = rd(E, I, 0, w0); wr(E, I, 0, bswapVal(X, a, w0)); return ST_NONE; }
  C(MOVBE) { unsigned w = I.op[1].size * 8; wr(E, I, 0, bswapVal(X, rd(E, I, 1, w), w)); return ST_NONE; }
  C(CBW) { wrGpr(E, RAX, 2, 0, vsext(X, rdGpr(E, RAX, 1, 0), 8, 16)); return ST_NONE; }
  C(CWDE) { wrGpr(E, RAX, 4, 0, vsext(X, rdGpr(E, RAX, 2, 0), 16, 32)); return ST_NONE; }
  C(CDQE) { wrGpr(E, RAX, 8, 0, vsext(X, rdGpr(E, RAX, 4, 0), 32, 64)); return ST_NONE; }
  C(CWD) { wrGpr(E, RDX, 2, 0, vsarc(X, rdGpr(E, RAX, 2, 0), 15, 16)); return ST_NONE; }
  C(CDQ) { wrGpr(E, RDX, 4, 0, vsarc(X, rdGpr(E, RAX, 4, 0), 31, 32)); return ST_NONE; }
  C(CQO) { wrGpr(E, RDX, 8, 0, vsarc(X, rdGpr(E, RAX, 8, 0), 63, 64)); return ST_NONE; }
  C(CLC) { setFlag(E, FL_CF, {0, 0}); return ST_NONE; }
  C(STC) { setFlag(E, FL_CF, {1, 0}); return ST_NONE; }
  C(CMC) { setFlag(E, FL_CF, vnot1(X, flag(FL_CF))); return ST_NONE; }
  C(CLD) { fl.bits &= ~(u64)FL_DF; return ST_NONE; }
  C(STD) { fl.bits |= FL_DF; return ST_NONE; }
  C(CMOVO) C(CMOVNO) C(CMOVB) C(CMOVNB) C(CMOVZ) C(CMOVNZ) C(CMOVBE) C(CMOVNBE) C(CMOVS) C(CMOVNS) C(CMOVP) C(CMOVNP)
  C(CMOVL) C(CMOVNL) C(CMOVLE) C(CMOVNLE) {
    Val c = cond(ccOf(I.mn)); Val s = rd(E, I, 1, w0), d = rd(E, I, 0, w0);
    wr(E, I, 0, vite(X, c, s, d, w0));
    return ST_NONE;
  }
  C(SETO) C(SETNO) C(SETB) C(SETNB) C(SETZ) C(SETNZ) C(SETBE) C(SETNBE) C(SETS) C(SETNS) C(SETP) C(SETNP)
  C(SETL) C(SETNL) C(SETLE) C(SETNLE) {
    Val c = cond(ccOf(I.mn));
    wr(E, I, 0, vzext(X, c, 1, 8));
    return ST_NONE;
  }

  // ---- arithmetic and logic
  C(ADD) { Loc d = loc(E, I, 0); Val a = get(E, d, w0), b = rd(E, I, 1, w0), r = vadd(X, a, b, w0); put(E, d, r); setLazy(E, LF_ADD, w0, a, b, r); return ST_NONE; }
  C(SUB) { Loc d = loc(E, I, 0); Val a = get(E, d, w0), b = rd(E, I, 1, w0), r = vsub(X, a, b, w0); put(E, d, r); setLazy(E, LF_SUB, w0, a, b, r); return ST_NONE; }
  C(CMP) { Val a = rd(E, I, 0, w0), b = rd(E, I, 1, w0), r = vsub(X, a, b, w0); setLazy(E, LF_SUB, w0, a, b, r); return ST_NONE; }
  C(ADC) {
    Loc d = loc(E, I, 0); Val a = get(E, d, w0), b = rd(E, I, 1, w0), cf = flag(FL_CF);
    Val r = vadd(X, vadd(X, a, b, w0), vzext(X, cf, 1, w0), w0);
    put(E, d, r); setLazy(E, LF_ADC, w0, a, b, r, FL_ARITH, cf);
    return ST_NONE;
  }
  C(SBB) {
    Loc d = loc(E, I, 0); Val a = get(E, d, w0), b = rd(E, I, 1, w0), cf = flag(FL_CF);
    Val r = vsub(X, vsub(X, a, b, w0), vzext(X, cf, 1, w0), w0);
    put(E, d, r); setLazy(E, LF_SBB, w0, a, b, r, FL_ARITH, cf);
    return ST_NONE;
  }
  C(AND) { Loc d = loc(E, I, 0); Val a = get(E, d, w0), b = rd(E, I, 1, w0), r = vand(X, a, b, w0); put(E, d, r); setLazy(E, LF_LOGIC, w0, a, b, r); return ST_NONE; }
  C(OR) { Loc d = loc(E, I, 0); Val a = get(E, d, w0), b = rd(E, I, 1, w0), r = vor(X, a, b, w0); put(E, d, r); setLazy(E, LF_LOGIC, w0, a, b, r); return ST_NONE; }
  C(XOR) { Loc d = loc(E, I, 0); Val a = get(E, d, w0), b = rd(E, I, 1, w0), r = vxor(X, a, b, w0); put(E, d, r); setLazy(E, LF_LOGIC, w0, a, b, r); return ST_NONE; }
  C(TEST) { Val a = rd(E, I, 0, w0), b = rd(E, I, 1, w0), r = vand(X, a, b, w0); setLazy(E, LF_LOGIC, w0, a, b, r); return ST_NONE; }
  C(NOT) { Loc d = loc(E, I, 0); put(E, d, vnot(X, get(E, d, w0), w0)); return ST_NONE; }
  C(NEG) { Loc d = loc(E, I, 0); Val a = get(E, d, w0), r = vneg(X, a, w0); put(E, d, r); setLazy(E, LF_NEG, w0, a, {0, 0}, r); return ST_NONE; }
  C(INC) { Loc d = loc(E, I, 0); Val a = get(E, d, w0), r = vadd(X, a, {1, 0}, w0); put(E, d, r); setLazy(E, LF_INC, w0, a, {1, 0}, r, FL_ARITH & ~FL_CF); return ST_NONE; }
  C(DEC) { Loc d = loc(E, I, 0); Val a = get(E, d, w0), r = vsub(X, a, {1, 0}, w0); put(E, d, r); setLazy(E, LF_DEC, w0, a, {1, 0}, r, FL_ARITH & ~FL_CF); return ST_NONE; }

  C(MUL) {
    Val s = rd(E, I, 0, w0);
    if (w0 == 8) {
      Val a = rdGpr(E, RAX, 1, 0); Val p = vmul(X, vzext(X, a, 8, 16), vzext(X, s, 8, 16), 16);
      wrGpr(E, RAX, 2, 0, p);
      setLazy(E, LF_MUL, 8, a, s, vext(X, p, 0, 8), FL_CF | FL_OF, vext(X, p, 8, 8));   // CF = OF = high half != 0, when read
      return ST_NONE;
    }
    Val a = rdGpr(E, RAX, w0 / 8, 0);
    Val lo = vmul(X, a, s, w0);
    Val hi{evalOp(O_MULHU, w0, 0, 0, a.c, s.c, 0), (a.s | s.s) ? X.mulhu(SX(X, a, w0), SX(X, s, w0)) : 0};
    wrGpr(E, RAX, w0 / 8, 0, lo); wrGpr(E, RDX, w0 / 8, 0, hi);
    setLazy(E, LF_MUL, w0, a, s, lo, FL_CF | FL_OF, hi);
    return ST_NONE;
  }
  C(IMUL) {
    if (I.nops == 1) {
      Val s = rd(E, I, 0, w0);
      if (w0 == 8) {
        Val a = rdGpr(E, RAX, 1, 0); Val p = vmul(X, vsext(X, a, 8, 16), vsext(X, s, 8, 16), 16);
        wrGpr(E, RAX, 2, 0, p);
        setLazy(E, LF_IMUL, 8, a, s, vext(X, p, 0, 8), FL_CF | FL_OF, vext(X, p, 8, 8));
        return ST_NONE;
      }
      Val a = rdGpr(E, RAX, w0 / 8, 0);
      Val lo = vmul(X, a, s, w0);
      Val hi{evalOp(O_MULHS, w0, 0, 0, a.c, s.c, 0), (a.s | s.s) ? X.mulhs(SX(X, a, w0), SX(X, s, w0)) : 0};
      wrGpr(E, RAX, w0 / 8, 0, lo); wrGpr(E, RDX, w0 / 8, 0, hi);
      setLazy(E, LF_IMUL, w0, a, s, lo, FL_CF | FL_OF, hi);
      return ST_NONE;
    }
    Val a = I.nops == 2 ? rd(E, I, 0, w0) : rd(E, I, 1, w0);
    Val b = I.nops == 2 ? rd(E, I, 1, w0) : rd(E, I, 2, w0);
    Val lo = vmul(X, a, b, w0);
    wr(E, I, 0, lo);
    setLazy(E, LF_IMUL2, w0, a, b, lo, FL_CF | FL_OF);                 // the high half only if CF / OF are read
    return ST_NONE;
  }
  C(DIV) C(IDIV) {
    const bool sgn = I.mn == ZYDIS_MNEMONIC_IDIV;
    Val d = rd(E, I, 0, w0);
    if (E.trap && d.s) {                              // where exceptions have handlers, a zero divisor is another way through the function
      const Val z = veq(X, d, {0, 0}, w0); const bool zero = z.c & 1;
      if (z.s) E.addConstraint(zero ? z.s : X.not_(z.s), I.addr, zero ? 1 : 2, zero ? 2 : 1, 0);
    }
    if ((d.c & M(w0)) == 0) { stopInfo = "divide error"; trapKind = TK_DIVZERO; rip = I.addr; return ST_EXCEPTION; }
    if (w0 <= 32) {
      // the dividend fits in 64 bits
      unsigned w2 = 2 * w0;
      Val hi = w0 == 8 ? rdGpr(E, RAX, 1, 1) : rdGpr(E, RDX, w0 / 8, 0);
      Val lo = rdGpr(E, RAX, w0 / 8, 0);
      Val n = vcat(X, hi, lo, w0, w0);
      Val dd = sgn ? vsext(X, d, w0, w2) : vzext(X, d, w0, w2);
      u64 qc = evalOp(sgn ? O_SDIV : O_UDIV, w2, 0, 0, n.c, dd.c, 0), rc = evalOp(sgn ? O_SREM : O_UREM, w2, 0, 0, n.c, dd.c, 0);
      bool fits = sgn ? (sx(qc, w2) == sx(qc & M(w0), w0)) : (qc >> w0) == 0;
      if (!fits) { stopInfo = "divide error"; trapKind = TK_DIVOVF; rip = I.addr; return ST_EXCEPTION; }
      Val q{qc & M(w0), 0}, r{rc & M(w0), 0};
      if (n.s | dd.s) {
        u32 N = SX(X, n, w2), D = SX(X, dd, w2);
        q.s = X.extract(sgn ? X.sdiv(N, D) : X.udiv(N, D), 0, w0);
        r.s = X.extract(sgn ? X.srem(N, D) : X.urem(N, D), 0, w0);
      }
      if (w0 == 8) { wrGpr(E, RAX, 1, 0, q); wrGpr(E, RAX, 1, 1, r); }
      else { wrGpr(E, RAX, w0 / 8, 0, q); wrGpr(E, RDX, w0 / 8, 0, r); }
      divFlags(E);
      return ST_NONE;
    }
    Val hi = rdGpr(E, RDX, 8, 0), lo = rdGpr(E, RAX, 8, 0);
    // 64 bits: rdx must be zero (div) or the sign of rax (idiv) for the symbolic form
    bool plain = sgn ? (hi.c == (u64)(sx(lo.c, 64) >> 63)) : hi.c == 0;
    if (plain) {
      if (hi.s) E.addConstraint(sgn ? X.eq(hi.s, X.ashr(SX(X, lo, 64), X.cst(63, 64))) : X.eq(hi.s, X.cst(0, 64)), I.addr, 0, 0, 3);
      if (sgn && lo.c == 0x8000000000000000ull && d.c == ~0ull) { stopInfo = "divide error"; trapKind = TK_DIVOVF; rip = I.addr; return ST_EXCEPTION; }
      Val q{evalOp(sgn ? O_SDIV : O_UDIV, 64, 0, 0, lo.c, d.c, 0), 0}, r{evalOp(sgn ? O_SREM : O_UREM, 64, 0, 0, lo.c, d.c, 0), 0};
      if (lo.s | d.s) { u32 N = SX(X, lo, 64), D = SX(X, d, 64); q.s = sgn ? X.sdiv(N, D) : X.udiv(N, D); r.s = sgn ? X.srem(N, D) : X.urem(N, D); }
      wrGpr(E, RAX, 8, 0, q); wrGpr(E, RDX, 8, 0, r);
      divFlags(E);
      return ST_NONE;
    }
    // full 128-bit dividend: computed on concrete values
    u64 hc = concretize(E, I, hi, 64), lc = concretize(E, I, lo, 64), dc = concretize(E, I, d, 64), q, r;
    if (!sgn) { if (!udiv128(hc, lc, dc, q, r)) { stopInfo = "divide error"; trapKind = TK_DIVOVF; rip = I.addr; return ST_EXCEPTION; } }
    else {
      bool nn = (i64)hc < 0, nd = (i64)dc < 0;
      u64 ah = hc, al = lc; if (nn) { al = 0 - lc; ah = ~hc + (lc == 0); }
      u64 ad = nd ? 0 - dc : dc;
      if (!udiv128(ah, al, ad, q, r)) { stopInfo = "divide error"; trapKind = TK_DIVOVF; rip = I.addr; return ST_EXCEPTION; }
      if (nn != nd) { if (q > 0x8000000000000000ull) { stopInfo = "divide error"; trapKind = TK_DIVOVF; rip = I.addr; return ST_EXCEPTION; } q = 0 - q; }
      else if (q > 0x7fffffffffffffffull) { stopInfo = "divide error"; trapKind = TK_DIVOVF; rip = I.addr; return ST_EXCEPTION; }
      if (nn) r = 0 - r;
    }
    wrGpr(E, RAX, 8, 0, {q, 0}); wrGpr(E, RDX, 8, 0, {r, 0});
    divFlags(E);
    return ST_NONE;
  }

  // ---- shifts and rotations
  C(SHL) C(SHR) C(SAR) C(ROL) C(ROR) C(RCL) C(RCR) {
    Loc d = loc(E, I, 0); Val a = get(E, d, w0);
    Val cnt = I.nops > 1 ? rd(E, I, 1, 8) : Val{1, 0};
    const u8 cm = w0 == 64 ? 63 : 31;
    if (cnt.s && I.mn != ZYDIS_MNEMONIC_RCL && I.mn != ZYDIS_MNEMONIC_RCR) {
      Val mc = vand(X, cnt, {cm, 0}, 8);
      Val zero = veq(X, mc, {0, 0}, 8);
      // zero or not is a fork (a zero count changes nothing): a branch with two pseudo targets (1: zero, 2: not zero)
      if (zero.s) E.addConstraint((zero.c & 1) ? zero.s : X.not_(zero.s), I.addr, (zero.c & 1) ? 1 : 2, (zero.c & 1) ? 2 : 1, 0);
      if (zero.c & 1) { if (w0 == 32) put(E, d, a); return ST_NONE; }
      if (mc.s && !X.isC(mc.s)) {
        Val cw = vzext(X, mc, 8, w0); Val r;
        u8 op = I.mn == ZYDIS_MNEMONIC_SHL ? O_SHL : I.mn == ZYDIS_MNEMONIC_SHR ? O_LSHR : I.mn == ZYDIS_MNEMONIC_SAR ? O_ASHR : I.mn == ZYDIS_MNEMONIC_ROL ? O_ROL : O_ROR;
        r.c = evalOp(op, w0, 0, 0, a.c, cw.c, 0);
        r.s = X.make(op, w0, 0, SX(X, a, w0), cw.s, 0, 0);
        if (X.isC(r.s)) r.s = 0;
        put(E, d, r);
        if (op == O_ROL) setLazy(E, LF_ROL, w0, a, {0, 0}, r, FL_CF | FL_OF);
        else if (op == O_ROR) setLazy(E, LF_ROR, w0, a, {0, 0}, r, FL_CF | FL_OF);
        else setLazy(E, op == O_SHL ? LF_SHL : op == O_LSHR ? LF_SHR : LF_SAR, w0, a, {0, 0}, r, FL_ARITH, mc);
        return ST_NONE;
      }
      cnt = mc;   // the masked count is concrete after all
    }
    unsigned c = (unsigned)(concretize(E, I, cnt, 8) & cm);
    if (c == 0) { if (w0 == 32) put(E, d, a); return ST_NONE; }   // a 32-bit register is still written (upper half cleared)
    Val r;
    switch (I.mn) {
    case ZYDIS_MNEMONIC_SHL: r = vshlc(X, a, c, w0); put(E, d, r); setLazy(E, LF_SHL, w0, a, {0, 0}, r, FL_ARITH, {c, 0}); break;
    case ZYDIS_MNEMONIC_SHR: r = vshrc(X, a, c, w0); put(E, d, r); setLazy(E, LF_SHR, w0, a, {0, 0}, r, FL_ARITH, {c, 0}); break;
    case ZYDIS_MNEMONIC_SAR: r = vsarc(X, a, c, w0); put(E, d, r); setLazy(E, LF_SAR, w0, a, {0, 0}, r, FL_ARITH, {c, 0}); break;
    case ZYDIS_MNEMONIC_ROL: r = vrolc(X, a, c, w0); put(E, d, r); setLazy(E, LF_ROL, w0, a, {0, 0}, r, FL_CF | FL_OF); break;
    case ZYDIS_MNEMONIC_ROR: r = vrorc(X, a, c, w0); put(E, d, r); setLazy(E, LF_ROR, w0, a, {0, 0}, r, FL_CF | FL_OF); break;
    default: {
      unsigned k = c % (w0 + 1);
      if (k == 0) { if (w0 == 32) put(E, d, a); return ST_NONE; }
      Val cf = flag(FL_CF), cfw = vzext(X, cf, 1, w0), ncf;
      if (I.mn == ZYDIS_MNEMONIC_RCL) {
        r = vor(X, vor(X, vshlc(X, a, k, w0), vshlc(X, cfw, k - 1, w0), w0), vshrc(X, a, w0 + 1 - k, w0), w0);
        ncf = vbit(X, a, w0 - k);
        put(E, d, r); setFlag(E, FL_CF, ncf); setFlag(E, FL_OF, vxor1(X, vbit(X, r, w0 - 1), ncf));
      } else {
        r = vor(X, vor(X, vshrc(X, a, k, w0), vshlc(X, cfw, w0 - k, w0), w0), vshlc(X, a, w0 + 1 - k, w0), w0);
        ncf = vbit(X, a, k - 1);
        put(E, d, r); setFlag(E, FL_CF, ncf); setFlag(E, FL_OF, vxor1(X, vbit(X, r, w0 - 1), vbit(X, r, w0 - 2)));
      }
    }
    }
    return ST_NONE;
  }
  C(SHLD) C(SHRD) {
    Loc d = loc(E, I, 0); Val a = get(E, d, w0), s = rd(E, I, 1, w0);
    Val cnt = rd(E, I, 2, 8);
    unsigned c = (unsigned)(concretize(E, I, cnt, 8) & (w0 == 64 ? 63 : 31));
    if (c == 0) { if (w0 == 32) put(E, d, a); return ST_NONE; }
    if (c >= w0) c = w0 - 1;   // 16-bit with a count above 15: undefined
    Val r;
    if (I.mn == ZYDIS_MNEMONIC_SHLD) { r = vor(X, vshlc(X, a, c, w0), vshrc(X, s, w0 - c, w0), w0); put(E, d, r); setLazy(E, LF_SHL, w0, a, {0, 0}, r, FL_ARITH, {c, 0}); }
    else { r = vor(X, vshrc(X, a, c, w0), vshlc(X, s, w0 - c, w0), w0); put(E, d, r); setLazy(E, LF_SHR, w0, a, {0, 0}, r, FL_ARITH, {c, 0}); }
    return ST_NONE;
  }
  // ---- bits
  C(BT) C(BTS) C(BTR) C(BTC) {
    Val off = rd(E, I, 1, w0);
    Loc d;
    if (I.op[0].type == OT_MEM && I.op[1].type != OT_IMM) {
      // a bit string in memory: the offset selects the word
      i64 o = sx(concretize(E, I, off, w0), w0);
      d = loc(E, I, 0);
      i64 words = o >= 0 ? o / (i64)w0 : -((-o + (i64)w0 - 1) / (i64)w0);
      d.addr += (u64)(words * (i64)(w0 / 8));
      off = {(u64)(o - words * (i64)w0), 0};
    } else d = loc(E, I, 0);
    Val a = get(E, d, w0);
    Val bit, mask;
    if (!off.s) {
      unsigned b = (unsigned)(off.c & (w0 - 1));
      bit = vbit(X, a, b); mask = {1ull << b, 0};
    } else {
      u32 sh = X.and_(off.s, X.cst(w0 - 1, w0));
      u64 b = off.c & (w0 - 1);
      bit = {(a.c >> b) & 1, X.extract(X.lshr(SX(X, a, w0), sh), 0, 1)};
      mask = {1ull << b, X.shl(X.cst(1, w0), sh)};
    }
    setFlag(E, FL_CF, bit);
    if (I.mn == ZYDIS_MNEMONIC_BTS) put(E, d, vor(X, a, mask, w0));
    else if (I.mn == ZYDIS_MNEMONIC_BTR) put(E, d, vand(X, a, vnot(X, mask, w0), w0));
    else if (I.mn == ZYDIS_MNEMONIC_BTC) put(E, d, vxor(X, a, mask, w0));
    return ST_NONE;
  }
  C(BSF) C(BSR) {
    Val s = rd(E, I, 1, w0), d = rd(E, I, 0, w0);
    Val zero = veq(X, s, {0, 0}, w0);
    bool fwd = I.mn == ZYDIS_MNEMONIC_BSF;
    unsigned long ix = 0;
    if (s.c) { if (fwd) _BitScanForward64(&ix, s.c); else _BitScanReverse64(&ix, s.c); }
    Val idx{ix, 0};
    if (s.s) idx.s = fwd ? X.ctz(s.s) : X.sub(X.cst(w0 - 1, w0), X.clz(s.s));
    if (zero.s || !zero.c) {
      if (w0 == 32 && I.op[0].type == OT_REG) {     // the destination is the whole 64-bit register when nothing is written
        Val old = rdGpr(E, I.op[0].reg, 8, 0);
        wrGpr(E, I.op[0].reg, 8, 0, vite(X, zero, old, vzext(X, idx, 32, 64), 64));
      } else wr(E, I, 0, vite(X, zero, d, idx, w0));
    }
    setFlag(E, FL_ZF, zero);
    return ST_NONE;
  }
  C(TZCNT) C(LZCNT) C(POPCNT) {
    Val s = rd(E, I, 1, w0);
    u8 op = I.mn == ZYDIS_MNEMONIC_TZCNT ? O_CTZ : I.mn == ZYDIS_MNEMONIC_LZCNT ? O_CLZ : O_POPCNT;
    Val r{evalOp(op, w0, w0, 0, s.c, 0, 0), s.s ? X.make(op, w0, w0, s.s, 0, 0, 0) : 0};
    wr(E, I, 0, r);
    Val zs = veq(X, s, {0, 0}, w0);
    if (op == O_POPCNT) { setLazy(E, LF_LOGIC, w0, {0, 0}, {0, 0}, {1, 0}); setFlag(E, FL_ZF, zs); }
    else { setFlag(E, FL_CF, zs); setFlag(E, FL_ZF, veq(X, r, {0, 0}, w0)); setFlag(E, FL_PF, {0, 0}); setFlag(E, FL_AF, {0, 0}); setFlag(E, FL_SF, {0, 0}); }   // (OF kept: AMD Zen)
    return ST_NONE;
  }
  C(ANDN) { Val a = rd(E, I, 1, w0), b = rd(E, I, 2, w0), r = vand(X, vnot(X, a, w0), b, w0); wr(E, I, 0, r); setLazy(E, LF_LOGIC, w0, a, b, r); return ST_NONE; }
  C(BLSI) C(BLSR) C(BLSMSK) {
    Val s = rd(E, I, 1, w0), r;
    if (I.mn == ZYDIS_MNEMONIC_BLSI) r = vand(X, s, vneg(X, s, w0), w0);
    else if (I.mn == ZYDIS_MNEMONIC_BLSR) r = vand(X, s, vsub(X, s, {1, 0}, w0), w0);
    else r = vxor(X, s, vsub(X, s, {1, 0}, w0), w0);
    wr(E, I, 0, r);
    setLazy(E, LF_LOGIC, w0, s, s, r);
    Val z = veq(X, s, {0, 0}, w0);
    setFlag(E, FL_CF, I.mn == ZYDIS_MNEMONIC_BLSI ? vnot1(X, z) : z);
    return ST_NONE;
  }
  C(BEXTR) {
    Val s = rd(E, I, 1, w0); u64 ctl = concretize(E, I, rd(E, I, 2, w0), w0);
    unsigned st = ctl & 0xff, ln = (ctl >> 8) & 0xff;
    Val r = st >= w0 || ln == 0 ? Val{0, 0} : vext(X, s, st, std::min(ln, w0 - st));
    r = vzext(X, r, 0, w0); if (!(st >= w0 || ln == 0) && std::min(ln, w0 - st) == w0) r = s;
    wr(E, I, 0, r); setLazy(E, LF_LOGIC, w0, r, r, r);
    return ST_NONE;
  }
  C(BZHI) {
    Val s = rd(E, I, 1, w0); unsigned n = (unsigned)(concretize(E, I, rd(E, I, 2, w0), w0) & 0xff);
    Val r = n >= w0 ? s : vand(X, s, {M(n), 0}, w0);
    wr(E, I, 0, r); setLazy(E, LF_LOGIC, w0, r, r, r); setFlag(E, FL_CF, {n > w0 - 1, 0});
    return ST_NONE;
  }
  C(RORX) { Val s = rd(E, I, 1, w0); wr(E, I, 0, vrorc(X, s, (unsigned)(I.op[2].disp & (w0 - 1)), w0)); return ST_NONE; }
  C(SARX) C(SHLX) C(SHRX) {
    Val s = rd(E, I, 1, w0), c = rd(E, I, 2, w0);
    u64 cc = c.c & (w0 - 1);
    u8 op = I.mn == ZYDIS_MNEMONIC_SARX ? O_ASHR : I.mn == ZYDIS_MNEMONIC_SHLX ? O_SHL : O_LSHR;
    Val r{evalOp(op, w0, 0, 0, s.c, cc, 0), 0};
    if (s.s | c.s) r.s = X.make(op, w0, 0, SX(X, s, w0), c.s ? X.and_(c.s, X.cst(w0 - 1, w0)) : X.cst(cc, w0), 0, 0);
    wr(E, I, 0, r);
    return ST_NONE;
  }
  C(MULX) {
    Val a = rdGpr(E, RDX, w0 / 8, 0), b = rd(E, I, 2, w0);
    Val lo = vmul(X, a, b, w0);
    Val hi{evalOp(O_MULHU, w0, 0, 0, a.c, b.c, 0), (a.s | b.s) ? X.mulhu(SX(X, a, w0), SX(X, b, w0)) : 0};
    wr(E, I, 1, lo); wr(E, I, 0, hi);
    return ST_NONE;
  }
  C(PEXT) C(PDEP) {
    Val s = rd(E, I, 1, w0); u64 m = concretize(E, I, rd(E, I, 2, w0), w0);
    u64 c = 0; u32 e = 0; unsigned k = 0;
    if (I.mn == ZYDIS_MNEMONIC_PEXT) {
      for (unsigned i = 0; i < w0; i++) if ((m >> i) & 1) { c |= ((s.c >> i) & 1) << k; if (s.s) { u32 b = X.extract(s.s, i, 1); e = e ? X.concat(b, e) : b; } k++; }
      if (s.s) e = e ? X.zext(e, w0) : X.cst(0, w0);
    } else {
      u32 acc = 0; unsigned filled = 0;
      for (unsigned i = 0; i < w0; i++) if ((m >> i) & 1) {
        c |= ((s.c >> k) & 1) << i;
        if (s.s) { if (i > filled) { u32 z = X.cst(0, i - filled); acc = acc ? X.concat(z, acc) : z; } u32 b = X.extract(s.s, k, 1); acc = acc ? X.concat(b, acc) : b; filled = i + 1; }
        k++;
      }
      if (s.s) { if (!acc) e = X.cst(0, w0); else e = filled < w0 ? X.zext(acc, w0) : acc; }
    }
    wr(E, I, 0, {c, e});
    return ST_NONE;
  }
  // ---- control flow
  C(JMP) C(CALL) {
    if (I.mn == ZYDIS_MNEMONIC_CALL && !havocSites.empty() && havocSites.count(I.addr) && havocCall(I)) return ST_NONE;
    u64 target;
    if (I.op[0].type == OT_IMM) target = (u64)I.op[0].disp;
    else {
      Val t = rd(E, I, 0, 64);
      if (t.s) E.concretized(t.s, t.c, 64, I.addr, 2);
      target = t.c;
      if (I.mn == ZYDIS_MNEMONIC_JMP && !E.switchTargets.empty()) target = E.forceSwitch(I.addr, target);
    }
    if (I.mn == ZYDIS_MNEMONIC_CALL) push(E, {I.next, 0}, 8);
    rip = target;
    return ST_NONE;
  }
  C(JO) C(JNO) C(JB) C(JNB) C(JZ) C(JNZ) C(JBE) C(JNBE) C(JS) C(JNS) C(JP) C(JNP) C(JL) C(JNL) C(JLE) C(JNLE) {
    Val c = cond(ccOf(I.mn)); u64 target = (u64)I.op[0].disp; bool taken = c.c & 1;
    if (!E.forceSites.empty() && E.forceSites.count(I.addr) && E.forceBranch(I.addr)) taken = !taken;   // forced: against the condition
    else if (c.s) E.addConstraint(taken ? c.s : X.not_(c.s), I.addr, taken ? target : I.next, taken ? I.next : target, 0);
    else if (E.condFolded) E.noteFolded(I.addr, taken ? target : I.next, taken ? I.next : target);
    if (E.covOn) E.covNote(I.addr, taken);
    rip = taken ? target : I.next;
    return ST_NONE;
  }
  C(JRCXZ) C(JECXZ) {
    Val r = rdGpr(E, RCX, I.mn == ZYDIS_MNEMONIC_JRCXZ ? 8 : 4, 0); unsigned w = I.mn == ZYDIS_MNEMONIC_JRCXZ ? 64 : 32;
    Val c = veq(X, r, {0, 0}, w); u64 target = (u64)I.op[0].disp; bool taken = c.c & 1;
    if (c.s) E.addConstraint(taken ? c.s : X.not_(c.s), I.addr, taken ? target : I.next, taken ? I.next : target, 0);
    rip = taken ? target : I.next;
    return ST_NONE;
  }
  C(LOOP) C(LOOPE) C(LOOPNE) {
    unsigned sz = I.asz; Val r = vsub(X, rdGpr(E, RCX, sz, 0), {1, 0}, sz * 8); wrGpr(E, RCX, sz, 0, r);
    Val c = vnot1(X, veq(X, r, {0, 0}, sz * 8));
    if (I.mn == ZYDIS_MNEMONIC_LOOPE) c = vand1(X, c, flag(FL_ZF));
    else if (I.mn == ZYDIS_MNEMONIC_LOOPNE) c = vand1(X, c, vnot1(X, flag(FL_ZF)));
    u64 target = (u64)I.op[0].disp; bool taken = c.c & 1;
    if (c.s) E.addConstraint(taken ? c.s : X.not_(c.s), I.addr, taken ? target : I.next, taken ? I.next : target, 0);
    rip = taken ? target : I.next;
    return ST_NONE;
  }
  C(RET) {
    Val t = pop(E, 8);
    if (I.nops > 0 && I.op[0].type == OT_IMM) spMove(E, (i64)((u64)I.op[0].disp & 0xffff));
    if (t.s) E.concretized(t.s, t.c, 64, I.addr, 2);
    rip = t.c;
    return ST_NONE;
  }
  C(IRETQ) {
    // a return through an interrupt frame (rip, cs, rflags, rsp, ss) at the program's own privilege level: to 64-bit code
    // only. A selector user code may not load, or a non-canonical rip, is a general protection fault (nothing changes).
    Val v[5];
    for (int k = 0; k < 5; k++) v[k] = E.load(g[RSP] + 8 * (u64)k, 8);
    const u64 cs = concretize(E, I, v[1], 64) & 0xffff, ss = concretize(E, I, v[4], 64) & 0xffff;
    if (cs == 0x23) { stopInfo = "unsupported: iretq to 32-bit code"; rip = I.addr; return ST_UNSUPPORTED; }
    if (v[0].s) E.concretized(v[0].s, v[0].c, 64, I.addr, 2);
    const u64 to = v[0].c, top = to >> 47;
    if (cs != 0x33 || (ss != 0x2b && ss != 0x53) || (top != 0 && top != 0x1ffff)) { stopInfo = "general protection"; trapKind = TK_GP; rip = I.addr; return ST_EXCEPTION; }
    // the flags a program may write: CF PF AF ZF SF TF DF OF NT AC ID (IF and IOPL stay); TF: one instruction, then a single step
    setFlagsVal(E, v[2], FL_ARITH | FL_DF);
    fl.bits = (fl.bits & ~0x244100ull) | (v[2].c & 0x244100ull);
    if ((v[2].c & 0x100) && !tf) { tf = 1; dbgOn = 1; }
    g[RSP] = v[3].c; gs[RSP] = v[3].s; ssSel = (u16)ss;
    rip = to;
    return ST_NONE;
  }
  C(LEAVE) { g[RSP] = g[RBP]; gs[RSP] = gs[RBP]; Val v = pop(E, 8); g[RBP] = v.c; gs[RBP] = v.s; return ST_NONE; }
  C(INT3) { stopInfo = "breakpoint"; trapKind = TK_BREAKPOINT; trapArg = 0; rip = I.addr; return ST_EXCEPTION; }
  C(UD0) C(UD1) C(UD2) { stopInfo = "invalid opcode"; trapKind = TK_INVALID; rip = I.addr; return ST_EXCEPTION; }
  C(INT) C(INT1) C(INTO) {
    // (0x101: the one-byte icebp, a single-step trap; int 1 written with its number is a general protection fault)
    const u64 vec = I.mn == ZYDIS_MNEMONIC_INT ? ((u64)I.op[0].disp & 0xff) : I.mn == ZYDIS_MNEMONIC_INT1 ? 0x101 : 4;
    char b[48]; snprintf(b, sizeof b, "int 0x%llx", (unsigned long long)vec); stopInfo = b; trapKind = TK_INT; trapArg = vec; rip = I.addr; return ST_EXCEPTION;
  }
  C(HLT) { stopInfo = "hlt"; trapKind = TK_PRIV; rip = I.addr; return ST_HALT; }
  // what only the kernel may run: a privileged-instruction exception of the program (anti-debugging code counts on it)
  C(CLI) C(STI) C(IN) C(OUT) C(INSB) C(INSW) C(INSD) C(OUTSB) C(OUTSW) C(OUTSD) C(RDMSR) C(WRMSR) C(LGDT) C(LIDT) C(INVLPG) C(SWAPGS) C(SYSRET)
  C(RDPMC) C(CLTS) C(INVD) C(WBINVD) C(LMSW) C(LTR) C(LLDT) { stopInfo = "privileged instruction"; trapKind = TK_PRIV; rip = I.addr; return ST_EXCEPTION; }
  // descriptor tables and the machine status word: readable by a program (values of a 64-bit Windows; the bases are the kernel's)
  C(SIDT) C(SGDT) {
    const u64 a = addrOf(E, I, I.op[0]); const bool idt = I.mn == ZYDIS_MNEMONIC_SIDT;
    E.store(a, 2, {idt ? 0x0fffull : 0x007full, 0}); E.store(a + 2, 8, {idt ? 0xfffff80000001000ull : 0xfffff80000000000ull, 0});
    return ST_NONE;
  }
  C(SLDT) C(STR) C(SMSW) {
    const u64 v = I.mn == ZYDIS_MNEMONIC_SLDT ? 0 : I.mn == ZYDIS_MNEMONIC_STR ? 0x40 : 0x80050031ull;
    wr(E, I, 0, {v & M(w0), 0});
    return ST_NONE;
  }
  // the segments a 64-bit Windows process can name: 33 code, 23 32-bit code, 2b data, 53 the thread's block
  C(LAR) C(LSL) C(VERR) C(VERW) {
    const bool two = I.mn == ZYDIS_MNEMONIC_LAR || I.mn == ZYDIS_MNEMONIC_LSL;
    const unsigned ws = I.op[two ? 1 : 0].size * 8;
    const u64 s = concretize(E, I, rd(E, I, two ? 1 : 0, ws), ws) & 0xffff;
    u64 lar = 0, lsl = 0; bool ok = true, wrt = false;
    switch (s) {
    case 0x33: lar = 0x20fb00; lsl = 0; break;
    case 0x23: lar = 0xcffb00; lsl = 0xffffffffull; break;
    case 0x2b: lar = 0xcff300; lsl = 0xffffffffull; wrt = true; break;
    case 0x53: lar = 0x40f300; lsl = 0x3c00; wrt = true; break;
    default: ok = false;
    }
    if (I.mn == ZYDIS_MNEMONIC_VERW) ok = ok && wrt;
    if (two && ok) wr(E, I, 0, {(I.mn == ZYDIS_MNEMONIC_LAR ? lar : lsl) & M(w0), 0});
    setFlag(E, FL_ZF, {ok ? 1ull : 0ull, 0});
    return ST_NONE;
  }
  C(SYSCALL) { stopInfo = "syscall"; return ST_SYSCALL; }
  C(SYSENTER) { stopInfo = "invalid opcode"; trapKind = TK_INVALID; rip = I.addr; return ST_EXCEPTION; }   // not an instruction of 64-bit code on this kind of CPU
  C(CPUID) {
    int r[4]; unsigned leaf = (unsigned)concretize(E, I, rdGpr(E, RAX, 4, 0), 32), sub = (unsigned)concretize(E, I, rdGpr(E, RCX, 4, 0), 32);
    __cpuidex(r, (int)leaf, (int)sub);
    // which core the thread happens to be on must not show (two runs of the same code give the same results): core 0
    // ... nor whether this machine happens to run under a hypervisor: the program sees bare metal, here and everywhere
    if (leaf == 1) { r[1] &= 0x00ffffff; r[2] &= 0x7fffffff; }
    else if (leaf >= 0x40000000u && leaf < 0x50000000u) r[0] = r[1] = r[2] = r[3] = 0;
    else if (leaf == 0xb || leaf == 0x1f) r[3] = 0;
    else if (leaf == 0x8000001e) { r[0] = 0; r[1] &= ~0xff; r[2] &= ~0xff; }
    if (E.cpuidSym) {
      const u64 key = I.addr ^ 0x6370756964000000ull; const u32 occ = E.envOcc(key);
      static const int out4[4] = {RAX, RBX, RCX, RDX};
      for (int k = 0; k < 4; k++) wrGpr(E, out4[k], 4, 0, E.envValue(key + 1 + (u64)k, occ, (u32)r[k], 32));
      return ST_NONE;
    }
    wrGpr(E, RAX, 4, 0, {(u32)r[0], 0}); wrGpr(E, RBX, 4, 0, {(u32)r[1], 0}); wrGpr(E, RCX, 4, 0, {(u32)r[2], 0}); wrGpr(E, RDX, 4, 0, {(u32)r[3], 0});
    return ST_NONE;
  }
  C(RDTSC) C(RDTSCP) {
    u64 t = 0x100000000ull + icount * 7;
    wrGpr(E, RAX, 4, 0, {t & 0xffffffff, 0}); wrGpr(E, RDX, 4, 0, {t >> 32, 0});
    if (I.mn == ZYDIS_MNEMONIC_RDTSCP) wrGpr(E, RCX, 4, 0, {0, 0});
    return ST_NONE;
  }
  C(RDPID) { wr(E, I, 0, {0, 0}); return ST_NONE; }                       // the processor's number: 0, as rdtscp gives it
  C(RDRAND) C(RDSEED) {
    // a random number is no fact of a run: an input where unknown values are explored, else the same sequence every time
    Val v = lazyMem ? ucValue(I.addr, "rnd") : Val{((icount + 1) * 0x9E3779B97F4A7C15ull) ^ 0x243F6A8885A308D3ull, 0};
    wr(E, I, 0, vext(X, v, 0, w0));
    for (u32 bit : {FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF}) setFlag(E, bit, {0, 0});
    setFlag(E, FL_CF, {1, 0});
    return ST_NONE;
  }
  C(XGETBV) {
    // register 0 (and 1: what is in use) only; any other number is a general protection fault
    if (concretize(E, I, rdGpr(E, RCX, 4, 0), 32) > 1) { stopInfo = "general protection"; trapKind = TK_GP; rip = I.addr; return ST_EXCEPTION; }
    wrGpr(E, RAX, 4, 0, {7, 0}); wrGpr(E, RDX, 4, 0, {0, 0}); return ST_NONE;
  }
  // control and status words: MXCSR is kept; the x87 control word reads as the default (no x87 state is modelled)
  C(STMXCSR) C(VSTMXCSR) { wr(E, I, 0, {mxcsr, 0}); return ST_NONE; }
  C(LDMXCSR) C(VLDMXCSR) { mxcsr = (u32)concretize(E, I, rd(E, I, 0, 32), 32); return ST_NONE; }
  C(FNSTCW) { wr(E, I, 0, {0x27f, 0}); return ST_NONE; }
  C(FLDCW) { (void)rd(E, I, 0, 16); return ST_NONE; }
  C(FNSTSW) { wr(E, I, 0, {0, 0}); return ST_NONE; }
  default: break;
  }
  return execString(E, I);
}

// ------------------------------------------------------------------------------------------------ string instructions
static Stop execString(Engine& E, const Insn& I) {
  Ctx& X = E.X;
  unsigned sz = 0; int kind = 0;
  switch (I.mn) {
  C(MOVSB) sz = 1; kind = 1; break;  C(MOVSW) sz = 2; kind = 1; break;  C(MOVSD) sz = 4; kind = 1; break;  C(MOVSQ) sz = 8; kind = 1; break;
  C(STOSB) sz = 1; kind = 2; break;  C(STOSW) sz = 2; kind = 2; break;  C(STOSD) sz = 4; kind = 2; break;  C(STOSQ) sz = 8; kind = 2; break;
  C(LODSB) sz = 1; kind = 3; break;  C(LODSW) sz = 2; kind = 3; break;  C(LODSD) sz = 4; kind = 3; break;  C(LODSQ) sz = 8; kind = 3; break;
  C(CMPSB) sz = 1; kind = 4; break;  C(CMPSW) sz = 2; kind = 4; break;  C(CMPSD) sz = 4; kind = 4; break;  C(CMPSQ) sz = 8; kind = 4; break;
  C(SCASB) sz = 1; kind = 5; break;  C(SCASW) sz = 2; kind = 5; break;  C(SCASD) sz = 4; kind = 5; break;  C(SCASQ) sz = 8; kind = 5; break;
  default: return execVector(E, I);
  }
  for (unsigned i = 0; i < I.nops; i++) if (I.op[i].type == OT_REG && I.op[i].rk == RK_VEC) return execVector(E, I);   // SSE movsd / cmpsd
  const unsigned aw = I.asz * 8;
  const i64 step = (E.fl.bits & FL_DF) ? -(i64)sz : (i64)sz;
  u64 si = concretize(E, I, rdGpr(E, RSI, I.asz, 0), aw), di = concretize(E, I, rdGpr(E, RDI, I.asz, 0), aw);
  u64 count = 1;
  if (I.rep) {
    const Val cnt = rdGpr(E, RCX, I.asz, 0);
    count = concretize(E, I, cnt, aw); if (count == 0) return ST_NONE;
    // a count which is an input and huge: the copy cannot end here (like a loop bounded by an input)
    if (cnt.s && E.spinLimit && count > (u64)E.spinLimit * 64) E.spinning = true;
  }
  u64 done = 0;
  const u64 sm = M(aw);
  const u64 chunk = std::min<u64>(count, 4096);
  bool stopped = false;
  while (done < chunk) {
    switch (kind) {
    case 1: { Val v = E.load(si, sz); E.store(di, sz, v); si = (si + step) & sm; di = (di + step) & sm; break; }
    case 2: { Val v = rdGpr(E, RAX, sz, 0); E.store(di, sz, v); di = (di + step) & sm; break; }
    case 3: { Val v = E.load(si, sz); wrGpr(E, RAX, sz, 0, v); si = (si + step) & sm; break; }
    case 4: { Val a = E.load(si, sz), b = E.load(di, sz), r = vsub(X, a, b, sz * 8); setLazy(E, LF_SUB, sz * 8, a, b, r); si = (si + step) & sm; di = (di + step) & sm; break; }
    case 5: { Val a = rdGpr(E, RAX, sz, 0), b = E.load(di, sz), r = vsub(X, a, b, sz * 8); setLazy(E, LF_SUB, sz * 8, a, b, r); di = (di + step) & sm; break; }
    }
    done++;
    if (I.rep && (kind == 4 || kind == 5)) {
      Val z = E.flag(FL_ZF);
      bool cont = I.rep == 1 ? (z.c & 1) : !(z.c & 1);
      if (z.s) E.addConstraint((z.c & 1) ? z.s : X.not_(z.s), I.addr, 0, 0, 0);
      if (!cont) { stopped = true; break; }
    }
    if (E.dataHits) break;                            // a data breakpoint: the #DB comes between iterations
  }
  if (kind != 2 && kind != 5) wrGpr(E, RSI, I.asz, 0, {si, 0});
  if (kind != 3) wrGpr(E, RDI, I.asz, 0, {di, 0});
  if (I.rep) wrGpr(E, RCX, I.asz, 0, {(count - done) & sm, 0});
  if (done > 1) E.icount += done - 1;                 // each iteration counts as an instruction
  if (I.rep && !stopped && done < count) E.rip = I.addr;   // the rest on the next execution (an interrupted rep)
  return ST_NONE;
}

}  // namespace unshroud

// ================================================================================================ vectors
namespace unshroud {

// A vector value: bytes, and cells only when `sym` (otherwise the cells are not looked at: all bytes are concrete)
struct VBuf { u8 b[32]; bool sym = false; Cell c[32]; };

static inline unsigned vlen(const Insn& I) { return I.vex && I.vl ? I.vl : 16; }
static inline bool isVec(const Opnd& o) { return o.type == OT_REG && o.rk == RK_VEC; }
static inline void symOn(VBuf& v) { if (!v.sym) { memset(v.c, 0, sizeof v.c); v.sym = true; } }

static Val laneGet(Ctx& X, const VBuf& v, unsigned o, unsigned k) {
  u64 c = 0; memcpy(&c, v.b + o, k);
  if (!v.sym) return {c, 0};
  u32 any = 0; for (unsigned i = 0; i < k; i++) any |= v.c[o + i].e;
  return {c, any ? cellsExpr(X, v.b + o, v.c + o, k) : 0};
}
static void laneSet(Ctx& X, VBuf& v, unsigned o, unsigned k, Val x) {
  memcpy(v.b + o, &x.c, k);
  u32 s = (x.s && !X.isC(x.s)) ? x.s : 0;
  if (s) { symOn(v); for (unsigned i = 0; i < k; i++) v.c[o + i] = Cell{s, i}; }
  else if (v.sym) for (unsigned i = 0; i < k; i++) v.c[o + i] = Cell{0, 0};
}
static void vzero(VBuf& v) { memset(v.b, 0, 32); v.sym = false; }
// n bytes of src at soff go to dst at doff
static void vcopy(VBuf& dst, unsigned doff, const VBuf& src, unsigned soff, unsigned n) {
  memcpy(dst.b + doff, src.b + soff, n);
  if (src.sym) { symOn(dst); memcpy(dst.c + doff, src.c + soff, n * sizeof(Cell)); }
  else if (dst.sym) memset(dst.c + doff, 0, n * sizeof(Cell));
}

// operand i as n bytes
static void rdv(Engine& E, const Insn& I, int i, unsigned n, VBuf& o) {
  const Opnd& op = I.op[i];
  if (isVec(op)) {
    int r = op.reg;
    if (n == 16) memcpy(o.b, E.v[r], 16); else memcpy(o.b, E.v[r], n);
    o.sym = (E.vsym >> r) & 1;
    if (o.sym) memcpy(o.c, E.vc[r], n * sizeof(Cell));
  } else if (op.type == OT_MEM) {
    o.sym = E.loadCells(addrOf(E, I, op), n, o.b, o.c);
  } else if (op.type == OT_REG && op.rk == RK_GPR) { vzero(o); laneSet(E.X, o, 0, op.size, rdGpr(E, op.reg, op.size, op.roff)); }
  else throw (int)ST_UNSUPPORTED;
}

// write n bytes to operand i; VEX forms clear the register above n bytes
static void wrv(Engine& E, const Insn& I, int i, const VBuf& v, unsigned n) {
  const Opnd& op = I.op[i];
  if (isVec(op)) {
    int r = op.reg; const u32 bit = 1u << r;
    if (n == 16) memcpy(E.v[r], v.b, 16); else memcpy(E.v[r], v.b, n);
    bool clearUpper = I.vex && n < 32;
    if (clearUpper) memset(E.v[r] + n, 0, 32 - n);
    if (v.sym) {
      if (!(E.vsym & bit)) memset(E.vc[r], 0, sizeof E.vc[r]);
      memcpy(E.vc[r], v.c, n * sizeof(Cell));
      if (clearUpper) memset(E.vc[r] + n, 0, (32 - n) * sizeof(Cell));
      E.vsym |= bit;
    } else if (E.vsym & bit) {
      memset(E.vc[r], 0, n * sizeof(Cell));
      if (clearUpper || n == 32) { memset(E.vc[r] + n, 0, (32 - n) * sizeof(Cell)); E.vsym &= ~bit; }
      else { u32 any = 0; for (unsigned k = n; k < 32; k++) any |= E.vc[r][k].e; if (!any) E.vsym &= ~bit; }
    }
  } else if (op.type == OT_MEM) E.storeCells(addrOf(E, I, op), n, v.b, v.sym ? v.c : nullptr);
  else if (op.type == OT_REG && op.rk == RK_GPR) wrGpr(E, op.reg, op.size, op.roff, laneGet(E.X, v, 0, op.size));
  else throw (int)ST_UNSUPPORTED;
}

static void permute(const VBuf& a, const VBuf& b, const u8* sel, unsigned n, VBuf& r);

static Val vop2(Ctx& X, u8 op, Val a, Val b, unsigned w) {
  bool cmp = op >= O_EQ && op <= O_SLE;
  Val r{evalOp(op, cmp ? 1 : w, cmp ? w : 0, 0, a.c, b.c, 0), 0};
  if (a.s | b.s) { r.s = X.make(op, cmp ? 1 : w, cmp ? w : 0, SX(X, a, w), SX(X, b, w), 0, 0); if (X.isC(r.s)) r.s = 0; }
  return r;
}
static Val vmask(Ctx& X, Val bit, unsigned w) { return {(bit.c & 1) ? M(w) : 0, bit.s ? X.sext(bit.s, w) : 0}; }
static Val vsat(Ctx& X, Val x, unsigned from, unsigned to, bool srcSigned, bool dstSigned) {
  // narrow x (from bits) to `to` bits with saturation
  i64 lo = dstSigned ? -(i64)(1ull << (to - 1)) : 0, hi = dstSigned ? (i64)((1ull << (to - 1)) - 1) : (i64)M(to);
  i64 v = srcSigned ? sx(x.c, from) : (i64)x.c;
  u64 c = (u64)(v < lo ? lo : v > hi ? hi : v) & M(to);
  if (!x.s) return {c, 0};
  Val L{(u64)lo & M(from), 0}, H{(u64)hi & M(from), 0};
  Val below = srcSigned ? vslt(X, x, L, from) : Val{0, 0};
  Val above = srcSigned ? vslt(X, H, x, from) : vult(X, H, x, from);
  Val r = vite(X, below, {(u64)lo & M(to), 0}, vite(X, above, {(u64)hi & M(to), 0}, vext(X, x, 0, to), to), to);
  r.c = c;
  return r;
}

#define V(m) case ZYDIS_MNEMONIC_##m: case ZYDIS_MNEMONIC_V##m:

static Stop vecMove(Engine& E, const Insn& I) {
  Ctx& X = E.X; VBuf a; const unsigned n = vlen(I);
  switch (I.mn) {
  V(MOVDQA) V(MOVDQU) V(MOVAPS) V(MOVUPS) V(MOVAPD) V(MOVUPD) V(LDDQU) V(MOVNTDQ) V(MOVNTPS) V(MOVNTPD) V(MOVNTDQA)
  case ZYDIS_MNEMONIC_VMOVDQA32: case ZYDIS_MNEMONIC_VMOVDQA64: case ZYDIS_MNEMONIC_VMOVDQU8: case ZYDIS_MNEMONIC_VMOVDQU16:
  case ZYDIS_MNEMONIC_VMOVDQU32: case ZYDIS_MNEMONIC_VMOVDQU64: {
    unsigned m = I.op[0].type == OT_MEM ? I.op[0].size : I.op[1].type == OT_MEM ? I.op[1].size : n;
    if (m > 32) throw (int)ST_UNSUPPORTED;
    rdv(E, I, 1, m, a); wrv(E, I, 0, a, m); return ST_NONE;
  }
  V(MOVD) V(MOVQ) {
    unsigned k = I.mn == ZYDIS_MNEMONIC_MOVD || I.mn == ZYDIS_MNEMONIC_VMOVD ? 4 : 8;
    if (isVec(I.op[0])) { VBuf s; rdv(E, I, 1, k, s); vzero(a); vcopy(a, 0, s, 0, k); wrv(E, I, 0, a, 16); }
    else { rdv(E, I, 1, k, a); wrv(E, I, 0, a, k); }
    return ST_NONE;
  }
  V(MOVSS) V(MOVSD) {
    unsigned k = (I.mn == ZYDIS_MNEMONIC_MOVSS || I.mn == ZYDIS_MNEMONIC_VMOVSS) ? 4 : 8;
    if (I.op[0].type == OT_MEM) { rdv(E, I, 1, k, a); wrv(E, I, 0, a, k); return ST_NONE; }
    if (I.op[I.nops - 1].type == OT_MEM) { VBuf s; rdv(E, I, I.nops - 1, k, s); vzero(a); vcopy(a, 0, s, 0, k); wrv(E, I, 0, a, 16); return ST_NONE; }
    VBuf lo; rdv(E, I, I.nops - 1, 16, lo); rdv(E, I, I.vex ? 1 : 0, 16, a);
    vcopy(a, 0, lo, 0, k);
    wrv(E, I, 0, a, 16);
    return ST_NONE;
  }
  V(MOVHPS) V(MOVHPD) V(MOVLPS) V(MOVLPD) {
    bool high = I.mn == ZYDIS_MNEMONIC_MOVHPS || I.mn == ZYDIS_MNEMONIC_MOVHPD || I.mn == ZYDIS_MNEMONIC_VMOVHPS || I.mn == ZYDIS_MNEMONIC_VMOVHPD;
    if (I.op[0].type == OT_MEM) { VBuf s; rdv(E, I, 1, 16, s); vcopy(a, 0, s, high ? 8 : 0, 8); wrv(E, I, 0, a, 8); return ST_NONE; }
    VBuf base, m; rdv(E, I, I.vex ? 1 : 0, 16, base); rdv(E, I, I.nops - 1, 8, m);
    vcopy(base, high ? 8 : 0, m, 0, 8);
    wrv(E, I, 0, base, 16); return ST_NONE;
  }
  V(MOVHLPS) V(MOVLHPS) {
    VBuf base, s; rdv(E, I, I.vex ? 1 : 0, 16, base); rdv(E, I, I.nops - 1, 16, s);
    if (I.mn == ZYDIS_MNEMONIC_MOVHLPS || I.mn == ZYDIS_MNEMONIC_VMOVHLPS) vcopy(base, 0, s, 8, 8); else vcopy(base, 8, s, 0, 8);
    wrv(E, I, 0, base, 16); return ST_NONE;
  }
  default: return ST_UNSUPPORTED;
  }
}

static Stop vecLogic(Engine& E, const Insn& I) {
  Ctx& X = E.X; const unsigned n = vlen(I);
  u8 op; bool andn = false;
  switch (I.mn) {
  V(PXOR) V(XORPS) V(XORPD) op = O_XOR; break;
  V(PAND) V(ANDPS) V(ANDPD) op = O_AND; break;
  V(POR) V(ORPS) V(ORPD) op = O_OR; break;
  V(PANDN) V(ANDNPS) V(ANDNPD) op = O_AND; andn = true; break;
  case ZYDIS_MNEMONIC_VPXORD: case ZYDIS_MNEMONIC_VPXORQ: op = O_XOR; break;
  case ZYDIS_MNEMONIC_VPANDD: case ZYDIS_MNEMONIC_VPANDQ: op = O_AND; break;
  case ZYDIS_MNEMONIC_VPORD: case ZYDIS_MNEMONIC_VPORQ: op = O_OR; break;
  default: return ST_UNSUPPORTED;
  }
  int s1 = I.vex && I.nops >= 3 ? 1 : 0, s2 = I.vex && I.nops >= 3 ? 2 : 1;
  VBuf a, b, r;
  if (op == O_XOR && isVec(I.op[s1]) && isVec(I.op[s2]) && I.op[s1].reg == I.op[s2].reg) { vzero(r); wrv(E, I, 0, r, n); return ST_NONE; }
  rdv(E, I, s1, n, a); rdv(E, I, s2, n, b);
  for (unsigned o = 0; o < n; o += 8) {
    Val x = laneGet(X, a, o, 8), y = laneGet(X, b, o, 8);
    if (andn) x = vnot(X, x, 64);
    laneSet(X, r, o, 8, vop2(X, op, x, y, 64));
  }
  wrv(E, I, 0, r, n);
  return ST_NONE;
}

// packed integer arithmetic and comparisons, element size k bytes
static Stop vecArith(Engine& E, const Insn& I) {
  Ctx& X = E.X; const unsigned n = vlen(I);
  unsigned k = 0; int kind = 0;   // 1 add 2 sub 3 mullo 4 mulhi-s 5 mulhi-u 6 eq 7 gt 8 minu 9 maxu 10 mins 11 maxs 12 addus 13 adds 14 subus 15 subs 16 avg 17 abs
  switch (I.mn) {
  V(PADDB) k = 1; kind = 1; break;  V(PADDW) k = 2; kind = 1; break;  V(PADDD) k = 4; kind = 1; break;  V(PADDQ) k = 8; kind = 1; break;
  V(PSUBB) k = 1; kind = 2; break;  V(PSUBW) k = 2; kind = 2; break;  V(PSUBD) k = 4; kind = 2; break;  V(PSUBQ) k = 8; kind = 2; break;
  V(PMULLW) k = 2; kind = 3; break; V(PMULLD) k = 4; kind = 3; break; V(PMULHW) k = 2; kind = 4; break; V(PMULHUW) k = 2; kind = 5; break;
  V(PCMPEQB) k = 1; kind = 6; break; V(PCMPEQW) k = 2; kind = 6; break; V(PCMPEQD) k = 4; kind = 6; break; V(PCMPEQQ) k = 8; kind = 6; break;
  V(PCMPGTB) k = 1; kind = 7; break; V(PCMPGTW) k = 2; kind = 7; break; V(PCMPGTD) k = 4; kind = 7; break; V(PCMPGTQ) k = 8; kind = 7; break;
  V(PMINUB) k = 1; kind = 8; break; V(PMINUW) k = 2; kind = 8; break; V(PMINUD) k = 4; kind = 8; break;
  V(PMAXUB) k = 1; kind = 9; break; V(PMAXUW) k = 2; kind = 9; break; V(PMAXUD) k = 4; kind = 9; break;
  V(PMINSB) k = 1; kind = 10; break; V(PMINSW) k = 2; kind = 10; break; V(PMINSD) k = 4; kind = 10; break;
  V(PMAXSB) k = 1; kind = 11; break; V(PMAXSW) k = 2; kind = 11; break; V(PMAXSD) k = 4; kind = 11; break;
  V(PADDUSB) k = 1; kind = 12; break; V(PADDUSW) k = 2; kind = 12; break; V(PADDSB) k = 1; kind = 13; break; V(PADDSW) k = 2; kind = 13; break;
  V(PSUBUSB) k = 1; kind = 14; break; V(PSUBUSW) k = 2; kind = 14; break; V(PSUBSB) k = 1; kind = 15; break; V(PSUBSW) k = 2; kind = 15; break;
  V(PAVGB) k = 1; kind = 16; break; V(PAVGW) k = 2; kind = 16; break;
  V(PABSB) k = 1; kind = 17; break; V(PABSW) k = 2; kind = 17; break; V(PABSD) k = 4; kind = 17; break;
  default: return ST_UNSUPPORTED;
  }
  const unsigned w = k * 8;
  VBuf a, b, r;
  int s1 = I.vex && I.nops >= 3 ? 1 : 0, s2 = I.vex && I.nops >= 3 ? 2 : 1;
  if (kind == 17) { s1 = 1; s2 = 1; }
  rdv(E, I, s1, n, a); rdv(E, I, s2, n, b);
  for (unsigned o = 0; o < n; o += k) {
    Val x = laneGet(X, a, o, k), y = laneGet(X, b, o, k), z;
    switch (kind) {
    case 1: z = vadd(X, x, y, w); break;
    case 2: z = vsub(X, x, y, w); break;
    case 3: z = vmul(X, x, y, w); break;
    case 4: z = vop2(X, O_MULHS, x, y, w); break;
    case 5: z = vop2(X, O_MULHU, x, y, w); break;
    case 6: z = vmask(X, veq(X, x, y, w), w); break;
    case 7: z = vmask(X, vslt(X, y, x, w), w); break;
    case 8: z = vite(X, vult(X, x, y, w), x, y, w); break;
    case 9: z = vite(X, vult(X, x, y, w), y, x, w); break;
    case 10: z = vite(X, vslt(X, x, y, w), x, y, w); break;
    case 11: z = vite(X, vslt(X, x, y, w), y, x, w); break;
    case 12: { Val s = vadd(X, vzext(X, x, w, w + 1 > 64 ? 64 : 2 * w), vzext(X, y, w, 2 * w), 2 * w); z = vsat(X, s, 2 * w, w, false, false); break; }
    case 13: { Val s = vadd(X, vsext(X, x, w, 2 * w), vsext(X, y, w, 2 * w), 2 * w); z = vsat(X, s, 2 * w, w, true, true); break; }
    case 14: z = vite(X, vult(X, x, y, w), {0, 0}, vsub(X, x, y, w), w); break;
    case 15: { Val s = vsub(X, vsext(X, x, w, 2 * w), vsext(X, y, w, 2 * w), 2 * w); z = vsat(X, s, 2 * w, w, true, true); break; }
    case 16: { Val s = vadd(X, vadd(X, vzext(X, x, w, 2 * w), vzext(X, y, w, 2 * w), 2 * w), {1, 0}, 2 * w); z = vext(X, s, 1, w); break; }
    case 17: z = vite(X, vslt(X, x, {0, 0}, w), vneg(X, x, w), x, w); break;
    }
    laneSet(X, r, o, k, z);
  }
  wrv(E, I, 0, r, n);
  return ST_NONE;
}

// shifts of elements (by an immediate or by the low quadword of a register) and of whole 128-bit lanes by bytes
static Stop vecShift(Engine& E, const Insn& I) {
  Ctx& X = E.X; const unsigned n = vlen(I);
  unsigned k = 0; int kind = 0;   // 1 shl 2 shr 3 sar 4 byte-left 5 byte-right
  switch (I.mn) {
  V(PSLLW) k = 2; kind = 1; break; V(PSLLD) k = 4; kind = 1; break; V(PSLLQ) k = 8; kind = 1; break;
  V(PSRLW) k = 2; kind = 2; break; V(PSRLD) k = 4; kind = 2; break; V(PSRLQ) k = 8; kind = 2; break;
  V(PSRAW) k = 2; kind = 3; break; V(PSRAD) k = 4; kind = 3; break;
  V(PSLLDQ) kind = 4; break; V(PSRLDQ) kind = 5; break;
  default: return ST_UNSUPPORTED;
  }
  int src = (I.vex && I.nops >= 3) ? 1 : 0;
  const Opnd& last = I.op[I.nops - 1];
  u64 cnt;
  if (last.type == OT_IMM) cnt = (u64)last.disp & 0xff;
  else { VBuf c; rdv(E, I, I.nops - 1, 8, c); cnt = concretize(E, I, laneGet(X, c, 0, 8), 64); }
  VBuf a, r; rdv(E, I, src, n, a);
  if (kind >= 4) {
    unsigned s = cnt > 16 ? 16 : (unsigned)cnt; u8 sel[32];
    for (unsigned lane = 0; lane < n; lane += 16)
      for (unsigned i = 0; i < 16; i++) {
        int from = kind == 4 ? (int)i - (int)s : (int)i + (int)s;
        sel[lane + i] = (from >= 0 && from < 16) ? (u8)(lane + from) : 0xff;
      }
    permute(a, a, sel, n, r);
    wrv(E, I, 0, r, n);
    return ST_NONE;
  }
  const unsigned w = k * 8;
  for (unsigned o = 0; o < n; o += k) {
    Val x = laneGet(X, a, o, k), z;
    if (kind == 1) z = cnt >= w ? Val{0, 0} : vshlc(X, x, (unsigned)cnt, w);
    else if (kind == 2) z = cnt >= w ? Val{0, 0} : vshrc(X, x, (unsigned)cnt, w);
    else z = vsarc(X, x, cnt >= w ? w - 1 : (unsigned)cnt, w);
    laneSet(X, r, o, k, z);
  }
  wrv(E, I, 0, r, n);
  return ST_NONE;
}

// byte permutations: what each destination byte takes (index into a: 0..31, into b: 32..63, zero: 0xff)
static void permute(const VBuf& a, const VBuf& b, const u8* sel, unsigned n, VBuf& r) {
  const bool sym = a.sym || b.sym;
  for (unsigned i = 0; i < n; i++) { u8 s = sel[i]; r.b[i] = s == 0xff ? 0 : s < 32 ? a.b[s] : b.b[s - 32]; }
  r.sym = sym;
  if (!sym) return;
  for (unsigned i = 0; i < n; i++) {
    u8 s = sel[i];
    if (s == 0xff) r.c[i] = {0, 0};
    else if (s < 32) r.c[i] = a.sym ? a.c[s] : Cell{0, 0};
    else r.c[i] = b.sym ? b.c[s - 32] : Cell{0, 0};
  }
  for (unsigned i = n; i < 32; i++) r.c[i] = {0, 0};
}

static Stop vecShuffle(Engine& E, const Insn& I) {
  Ctx& X = E.X; const unsigned n = vlen(I);
  VBuf a, b, r; u8 sel[32];
  int s1 = I.vex && I.nops >= 3 ? 1 : 0, s2 = I.vex && I.nops >= 3 ? 2 : 1;
  auto imm = [&]() { return (unsigned)(I.op[I.nops - 1].disp & 0xff); };
  switch (I.mn) {
  V(PSHUFD) { rdv(E, I, 1, n, a); unsigned m = imm();
    for (unsigned l = 0; l < n; l += 16) for (unsigned d = 0; d < 4; d++) for (unsigned j = 0; j < 4; j++) sel[l + d * 4 + j] = (u8)(l + ((m >> (2 * d)) & 3) * 4 + j);
    permute(a, a, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE; }
  V(PSHUFLW) V(PSHUFHW) { rdv(E, I, 1, n, a); unsigned m = imm(); bool hi = I.mn == ZYDIS_MNEMONIC_PSHUFHW || I.mn == ZYDIS_MNEMONIC_VPSHUFHW;
    for (unsigned i = 0; i < n; i++) sel[i] = (u8)i;
    for (unsigned l = 0; l < n; l += 16) for (unsigned d = 0; d < 4; d++) for (unsigned j = 0; j < 2; j++) sel[l + (hi ? 8 : 0) + d * 2 + j] = (u8)(l + (hi ? 8 : 0) + ((m >> (2 * d)) & 3) * 2 + j);
    permute(a, a, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE; }
  V(PSHUFB) { rdv(E, I, s1, n, a); rdv(E, I, s2, n, b);
    for (unsigned i = 0; i < n; i++) {
      u8 c = (u8)concretize(E, I, laneGet(X, b, i, 1), 8);
      sel[i] = (c & 0x80) ? 0xff : (u8)((i & ~15u) + (c & 15));
    }
    permute(a, a, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE; }
  V(PUNPCKLBW) V(PUNPCKHBW) V(PUNPCKLWD) V(PUNPCKHWD) V(PUNPCKLDQ) V(PUNPCKHDQ) V(PUNPCKLQDQ) V(PUNPCKHQDQ)
  V(UNPCKLPS) V(UNPCKHPS) V(UNPCKLPD) V(UNPCKHPD) {
    unsigned k; bool hi;
    switch (I.mn) {
    V(PUNPCKLBW) k = 1; hi = false; break; V(PUNPCKHBW) k = 1; hi = true; break;
    V(PUNPCKLWD) k = 2; hi = false; break; V(PUNPCKHWD) k = 2; hi = true; break;
    V(PUNPCKLDQ) V(UNPCKLPS) k = 4; hi = false; break; V(PUNPCKHDQ) V(UNPCKHPS) k = 4; hi = true; break;
    V(PUNPCKLQDQ) V(UNPCKLPD) k = 8; hi = false; break; default: k = 8; hi = true; break;
    }
    rdv(E, I, s1, n, a); rdv(E, I, s2, n, b);
    for (unsigned l = 0; l < n; l += 16)
      for (unsigned e = 0; e < 16 / (2 * k); e++)
        for (unsigned j = 0; j < k; j++) {
          unsigned from = l + (hi ? 8 : 0) + e * k + j;
          sel[l + 2 * e * k + j] = (u8)from; sel[l + (2 * e + 1) * k + j] = (u8)(32 + from);
        }
    permute(a, b, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE;
  }
  V(SHUFPS) { rdv(E, I, s1, n, a); rdv(E, I, s2, n, b); unsigned m = imm();
    for (unsigned l = 0; l < n; l += 16) for (unsigned d = 0; d < 4; d++) for (unsigned j = 0; j < 4; j++) {
      unsigned pick = (m >> (2 * d)) & 3; sel[l + d * 4 + j] = (u8)((d < 2 ? 0 : 32) + l + pick * 4 + j); }
    permute(a, b, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE; }
  V(SHUFPD) { rdv(E, I, s1, n, a); rdv(E, I, s2, n, b); unsigned m = imm();
    for (unsigned l = 0, bit = 0; l < n; l += 16, bit += 2) for (unsigned d = 0; d < 2; d++) for (unsigned j = 0; j < 8; j++) {
      unsigned pick = (m >> (bit + d)) & 1; sel[l + d * 8 + j] = (u8)((d == 0 ? 0 : 32) + l + pick * 8 + j); }
    permute(a, b, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE; }
  V(PALIGNR) { rdv(E, I, s1, n, a); rdv(E, I, s2, n, b); unsigned m = imm();
    // concatenation a:b (a high) shifted right by m bytes, per 128-bit lane
    for (unsigned l = 0; l < n; l += 16) for (unsigned i = 0; i < 16; i++) { unsigned s = i + m; sel[l + i] = s < 16 ? (u8)(32 + l + s) : s < 32 ? (u8)(l + s - 16) : 0xff; }
    permute(a, b, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE; }
  V(PBLENDW) V(BLENDPS) V(BLENDPD) { rdv(E, I, s1, n, a); rdv(E, I, s2, n, b); unsigned m = imm();
    unsigned k = (I.mn == ZYDIS_MNEMONIC_PBLENDW || I.mn == ZYDIS_MNEMONIC_VPBLENDW) ? 2 : (I.mn == ZYDIS_MNEMONIC_BLENDPS || I.mn == ZYDIS_MNEMONIC_VBLENDPS) ? 4 : 8;
    for (unsigned i = 0; i < n; i++) { unsigned e = (i % 16) / k + (k == 2 ? 0 : (i / 16) * (16 / k)); sel[i] = ((m >> (e % 8)) & 1) ? (u8)(32 + i) : (u8)i; }
    permute(a, b, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE; }
  V(PBLENDVB) V(BLENDVPS) V(BLENDVPD) {
    VBuf msk;
    if (I.vex) { rdv(E, I, 1, n, a); rdv(E, I, 2, n, b); rdv(E, I, 3, n, msk); }
    else { rdv(E, I, 0, n, a); rdv(E, I, 1, n, b); memcpy(msk.b, E.v[0], 16); msk.sym = E.vsym & 1; if (msk.sym) memcpy(msk.c, E.vc[0], 16 * sizeof(Cell)); }
    unsigned k = (I.mn == ZYDIS_MNEMONIC_PBLENDVB || I.mn == ZYDIS_MNEMONIC_VPBLENDVB) ? 1 : (I.mn == ZYDIS_MNEMONIC_BLENDVPS || I.mn == ZYDIS_MNEMONIC_VBLENDVPS) ? 4 : 8;
    for (unsigned o = 0; o < n; o += k) {
      Val top = laneGet(X, msk, o + k - 1, 1); bool s = concretize(E, I, vbit(X, top, 7), 1) & 1;
      for (unsigned j = 0; j < k; j++) sel[o + j] = s ? (u8)(32 + o + j) : (u8)(o + j);
    }
    permute(a, b, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE;
  }
  V(MOVDDUP) V(MOVSLDUP) V(MOVSHDUP) { rdv(E, I, 1, n, a);
    for (unsigned i = 0; i < n; i++) {
      if (I.mn == ZYDIS_MNEMONIC_MOVDDUP || I.mn == ZYDIS_MNEMONIC_VMOVDDUP) sel[i] = (u8)((i & ~15u) + (i % 8));
      else { unsigned e = i / 4, j = i % 4; unsigned src = (I.mn == ZYDIS_MNEMONIC_MOVSLDUP || I.mn == ZYDIS_MNEMONIC_VMOVSLDUP) ? (e & ~1u) : (e | 1u); sel[i] = (u8)(src * 4 + j); }
    }
    permute(a, a, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE; }
  default: return ST_UNSUPPORTED;
  }
}

static Stop vecMisc(Engine& E, const Insn& I) {
  Ctx& X = E.X; const unsigned n = vlen(I);
  VBuf a, b, r;
  auto imm = [&]() { return (unsigned)(I.op[I.nops - 1].disp & 0xff); };
  auto is = [&](u16 m1, u16 m2) { return I.mn == m1 || I.mn == m2; };
  switch (I.mn) {
  V(PINSRB) V(PINSRW) V(PINSRD) V(PINSRQ) {
    unsigned k = is(ZYDIS_MNEMONIC_PINSRB, ZYDIS_MNEMONIC_VPINSRB) ? 1 : is(ZYDIS_MNEMONIC_PINSRW, ZYDIS_MNEMONIC_VPINSRW) ? 2 : is(ZYDIS_MNEMONIC_PINSRD, ZYDIS_MNEMONIC_VPINSRD) ? 4 : 8;
    rdv(E, I, I.vex ? 1 : 0, 16, a);
    Val x = rd(E, I, I.nops - 2, I.op[I.nops - 2].size * 8);
    if (I.op[I.nops - 2].size > k) x = vext(X, x, 0, k * 8);
    laneSet(X, a, (imm() % (16 / k)) * k, k, x);
    wrv(E, I, 0, a, 16); return ST_NONE;
  }
  V(PEXTRB) V(PEXTRW) V(PEXTRD) V(PEXTRQ) {
    unsigned k = is(ZYDIS_MNEMONIC_PEXTRB, ZYDIS_MNEMONIC_VPEXTRB) ? 1 : is(ZYDIS_MNEMONIC_PEXTRW, ZYDIS_MNEMONIC_VPEXTRW) ? 2 : is(ZYDIS_MNEMONIC_PEXTRD, ZYDIS_MNEMONIC_VPEXTRD) ? 4 : 8;
    rdv(E, I, 1, 16, a);
    Val x = laneGet(X, a, (imm() % (16 / k)) * k, k);
    if (I.op[0].type == OT_REG) wr(E, I, 0, vzext(X, x, k * 8, I.op[0].size * 8)); else wr(E, I, 0, x);
    return ST_NONE;
  }
  V(PMOVMSKB) V(MOVMSKPS) V(MOVMSKPD) {
    unsigned k = is(ZYDIS_MNEMONIC_PMOVMSKB, ZYDIS_MNEMONIC_VPMOVMSKB) ? 1 : is(ZYDIS_MNEMONIC_MOVMSKPS, ZYDIS_MNEMONIC_VMOVMSKPS) ? 4 : 8;
    rdv(E, I, 1, n, a);
    Val acc{0, 0}; unsigned bits = 0;
    for (unsigned o = 0; o < n; o += k) { Val t = vbit(X, laneGet(X, a, o + k - 1, 1), 7); acc = bits ? vcat(X, t, acc, 1, bits) : t; bits++; }
    wr(E, I, 0, vzext(X, acc, bits, I.op[0].size * 8));
    return ST_NONE;
  }
  V(PTEST) {
    rdv(E, I, 0, n, a); rdv(E, I, 1, n, b);
    Val z{1, 0}, c{1, 0};
    for (unsigned o = 0; o < n; o += 8) {
      Val x = laneGet(X, a, o, 8), y = laneGet(X, b, o, 8);
      z = vand1(X, z, veq(X, vand(X, x, y, 64), {0, 0}, 64));
      c = vand1(X, c, veq(X, vand(X, vnot(X, x, 64), y, 64), {0, 0}, 64));
    }
    setLazy(E, LF_LOGIC, 64, {0, 0}, {0, 0}, {1, 0});
    setFlag(E, FL_ZF, z); setFlag(E, FL_CF, c);
    return ST_NONE;
  }
  V(PMOVZXBW) V(PMOVZXBD) V(PMOVZXBQ) V(PMOVZXWD) V(PMOVZXWQ) V(PMOVZXDQ) V(PMOVSXBW) V(PMOVSXBD) V(PMOVSXBQ) V(PMOVSXWD) V(PMOVSXWQ) V(PMOVSXDQ) {
    unsigned from, to; bool sg;
    switch (I.mn) {
    V(PMOVZXBW) from = 1; to = 2; sg = false; break; V(PMOVZXBD) from = 1; to = 4; sg = false; break; V(PMOVZXBQ) from = 1; to = 8; sg = false; break;
    V(PMOVZXWD) from = 2; to = 4; sg = false; break; V(PMOVZXWQ) from = 2; to = 8; sg = false; break; V(PMOVZXDQ) from = 4; to = 8; sg = false; break;
    V(PMOVSXBW) from = 1; to = 2; sg = true; break; V(PMOVSXBD) from = 1; to = 4; sg = true; break; V(PMOVSXBQ) from = 1; to = 8; sg = true; break;
    V(PMOVSXWD) from = 2; to = 4; sg = true; break; V(PMOVSXWQ) from = 2; to = 8; sg = true; break; default: from = 4; to = 8; sg = true; break;
    }
    unsigned cnt = n / to; rdv(E, I, 1, cnt * from, a);
    for (unsigned e = 0; e < cnt; e++) { Val x = laneGet(X, a, e * from, from); laneSet(X, r, e * to, to, sg ? vsext(X, x, from * 8, to * 8) : vzext(X, x, from * 8, to * 8)); }
    wrv(E, I, 0, r, n); return ST_NONE;
  }
  V(PACKUSWB) V(PACKSSWB) V(PACKSSDW) V(PACKUSDW) {
    unsigned from = (is(ZYDIS_MNEMONIC_PACKUSWB, ZYDIS_MNEMONIC_VPACKUSWB) || is(ZYDIS_MNEMONIC_PACKSSWB, ZYDIS_MNEMONIC_VPACKSSWB)) ? 2 : 4;
    bool us = is(ZYDIS_MNEMONIC_PACKUSWB, ZYDIS_MNEMONIC_VPACKUSWB) || is(ZYDIS_MNEMONIC_PACKUSDW, ZYDIS_MNEMONIC_VPACKUSDW);
    int s1 = I.vex && I.nops >= 3 ? 1 : 0, s2 = I.vex && I.nops >= 3 ? 2 : 1;
    rdv(E, I, s1, n, a); rdv(E, I, s2, n, b);
    unsigned to = from / 2, per = 16 / from;
    for (unsigned l = 0; l < n; l += 16)
      for (unsigned e = 0; e < 2 * per; e++) {
        const VBuf& src = e < per ? a : b; Val x = laneGet(X, src, l + (e % per) * from, from);
        laneSet(X, r, l + e * to, to, vsat(X, x, from * 8, to * 8, true, !us));
      }
    wrv(E, I, 0, r, n); return ST_NONE;
  }
  default: break;
  }
  return ST_UNSUPPORTED;
}

static Stop vecAvx(Engine& E, const Insn& I) {
  Ctx& X = E.X; const unsigned n = vlen(I);
  VBuf a, b, r; u8 sel[32];
  auto imm = [&]() { return (unsigned)(I.op[I.nops - 1].disp & 0xff); };
  switch (I.mn) {
  case ZYDIS_MNEMONIC_VPBROADCASTB: case ZYDIS_MNEMONIC_VPBROADCASTW: case ZYDIS_MNEMONIC_VPBROADCASTD: case ZYDIS_MNEMONIC_VPBROADCASTQ:
  case ZYDIS_MNEMONIC_VBROADCASTSS: case ZYDIS_MNEMONIC_VBROADCASTSD: case ZYDIS_MNEMONIC_VBROADCASTI128: case ZYDIS_MNEMONIC_VBROADCASTF128: {
    unsigned k = I.mn == ZYDIS_MNEMONIC_VPBROADCASTB ? 1 : I.mn == ZYDIS_MNEMONIC_VPBROADCASTW ? 2 : (I.mn == ZYDIS_MNEMONIC_VPBROADCASTD || I.mn == ZYDIS_MNEMONIC_VBROADCASTSS) ? 4 :
                 (I.mn == ZYDIS_MNEMONIC_VPBROADCASTQ || I.mn == ZYDIS_MNEMONIC_VBROADCASTSD) ? 8 : 16;
    rdv(E, I, 1, k, a);
    for (unsigned o = 0; o < n; o += k) vcopy(r, o, a, 0, k);
    wrv(E, I, 0, r, n); return ST_NONE;
  }
  case ZYDIS_MNEMONIC_VINSERTI128: case ZYDIS_MNEMONIC_VINSERTF128: {
    rdv(E, I, 1, 32, a); rdv(E, I, 2, 16, b); unsigned h = imm() & 1;
    vcopy(a, 16 * h, b, 0, 16); wrv(E, I, 0, a, 32); return ST_NONE;
  }
  case ZYDIS_MNEMONIC_VEXTRACTI128: case ZYDIS_MNEMONIC_VEXTRACTF128: {
    rdv(E, I, 1, 32, a); unsigned h = imm() & 1;
    vcopy(r, 0, a, 16 * h, 16);
    wrv(E, I, 0, r, 16); return ST_NONE;
  }
  case ZYDIS_MNEMONIC_VPERM2I128: case ZYDIS_MNEMONIC_VPERM2F128: {
    rdv(E, I, 1, 32, a); rdv(E, I, 2, 32, b); unsigned m = imm();
    for (unsigned h = 0; h < 2; h++) { unsigned c = (m >> (4 * h)) & 0xf; for (unsigned j = 0; j < 16; j++) sel[16 * h + j] = (c & 8) ? 0xff : (u8)(((c & 2) ? 32 : 0) + (c & 1) * 16 + j); }
    permute(a, b, sel, 32, r); wrv(E, I, 0, r, 32); return ST_NONE;
  }
  case ZYDIS_MNEMONIC_VPERMQ: case ZYDIS_MNEMONIC_VPERMPD: {
    rdv(E, I, 1, 32, a); unsigned m = imm();
    for (unsigned d = 0; d < 4; d++) for (unsigned j = 0; j < 8; j++) sel[d * 8 + j] = (u8)(((m >> (2 * d)) & 3) * 8 + j);
    permute(a, a, sel, 32, r); wrv(E, I, 0, r, 32); return ST_NONE;
  }
  case ZYDIS_MNEMONIC_VPERMD: case ZYDIS_MNEMONIC_VPERMPS: {
    rdv(E, I, 1, 32, b); rdv(E, I, 2, 32, a);
    for (unsigned d = 0; d < 8; d++) { unsigned ix = (unsigned)(concretize(E, I, laneGet(X, b, d * 4, 4), 32) & 7); for (unsigned j = 0; j < 4; j++) sel[d * 4 + j] = (u8)(ix * 4 + j); }
    permute(a, a, sel, 32, r); wrv(E, I, 0, r, 32); return ST_NONE;
  }
  case ZYDIS_MNEMONIC_VPBLENDD: {
    rdv(E, I, 1, n, a); rdv(E, I, 2, n, b); unsigned m = imm();
    for (unsigned i = 0; i < n; i++) sel[i] = ((m >> (i / 4)) & 1) ? (u8)(32 + i) : (u8)i;
    permute(a, b, sel, n, r); wrv(E, I, 0, r, n); return ST_NONE;
  }
  case ZYDIS_MNEMONIC_VPSLLVD: case ZYDIS_MNEMONIC_VPSLLVQ: case ZYDIS_MNEMONIC_VPSRLVD: case ZYDIS_MNEMONIC_VPSRLVQ: case ZYDIS_MNEMONIC_VPSRAVD: {
    unsigned k = (I.mn == ZYDIS_MNEMONIC_VPSLLVQ || I.mn == ZYDIS_MNEMONIC_VPSRLVQ) ? 8 : 4, w = k * 8;
    rdv(E, I, 1, n, a); rdv(E, I, 2, n, b);
    for (unsigned o = 0; o < n; o += k) {
      Val x = laneGet(X, a, o, k); unsigned c = (unsigned)std::min<u64>(concretize(E, I, laneGet(X, b, o, k), w), 64);
      Val z = I.mn == ZYDIS_MNEMONIC_VPSRAVD ? vsarc(X, x, c >= w ? w - 1 : c, w) : c >= w ? Val{0, 0} :
              (I.mn == ZYDIS_MNEMONIC_VPSLLVD || I.mn == ZYDIS_MNEMONIC_VPSLLVQ) ? vshlc(X, x, c, w) : vshrc(X, x, c, w);
      laneSet(X, r, o, k, z);
    }
    wrv(E, I, 0, r, n); return ST_NONE;
  }
  case ZYDIS_MNEMONIC_VZEROALL: memset(E.v, 0, sizeof E.v); memset(E.vc, 0, sizeof E.vc); E.vsym = 0; return ST_NONE;
  default: return ST_UNSUPPORTED;
  }
}

Stop nativeExec(Engine& E, const Insn& I);   // native.cpp

Stop execVector(Engine& E, const Insn& I) {
  Stop s;
  if ((s = vecMove(E, I)) != ST_UNSUPPORTED) return s;
  if ((s = vecLogic(E, I)) != ST_UNSUPPORTED) return s;
  if ((s = vecArith(E, I)) != ST_UNSUPPORTED) return s;
  if ((s = vecShift(E, I)) != ST_UNSUPPORTED) return s;
  if ((s = vecShuffle(E, I)) != ST_UNSUPPORTED) return s;
  if ((s = vecMisc(E, I)) != ST_UNSUPPORTED) return s;
  if ((s = vecAvx(E, I)) != ST_UNSUPPORTED) return s;
  s = nativeExec(E, I);
  if (s == ST_UNSUPPORTED) { E.rip = I.addr; E.stopInfo = std::string("unsupported: ") + ZydisMnemonicGetString((ZydisMnemonic)I.mn); }
  else E.nativeCount++;
  return s;
}

}  // namespace unshroud
