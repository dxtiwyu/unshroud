// unshroud - exceptions in the process (see win.hpp): the records ntdll builds, the walk of the frames with the images'
// unwind data, the handlers of the program run as the code they are, RtlUnwindEx, RtlRestoreContext.
// A dispatch or an unwind in progress is a frame on the emulated stack (as ntdll's own frames are): a handler is called
// with a return address in the MAGIC page, whose hook goes on with the frame found above the stack pointer. Register
// values travel through CONTEXT records as memory cells, with their expressions.
#include "win.hpp"
#include <cstdio>

namespace unshroud {

namespace {
enum : u64 { CX_FLAGS = 0x30, CX_MXCSR = 0x34, CX_SEG = 0x38, CX_EFLAGS = 0x44, CX_DR0 = 0x48, CX_DR6 = 0x68, CX_DR7 = 0x70, CX_RAX = 0x78, CX_RSP = 0x98, CX_RIP = 0xf8, CX_FLT = 0x100, CX_XMM0 = 0x1a0, CX_SIZE = 0x4d0 };
enum : u64 { ER_CODE = 0, ER_FLAGS = 4, ER_CHAIN = 8, ER_ADDRESS = 0x10, ER_NPARAMS = 0x18, ER_INFO = 0x20, ER_SIZE = 0x98 };
enum : u64 { DC_CONTROLPC = 0, DC_IMAGEBASE = 8, DC_FUNCTIONENTRY = 0x10, DC_ESTABLISHER = 0x18, DC_TARGETIP = 0x20, DC_CONTEXT = 0x28, DC_HANDLER = 0x30,
             DC_HANDLERDATA = 0x38, DC_HISTORY = 0x40, DC_SCOPEINDEX = 0x48, DC_SIZE = 0x50 };
enum : u32 { EXC_NONCONTINUABLE = 1, EXC_UNWINDING = 2, EXC_EXIT_UNWIND = 4, EXC_NESTED_CALL = 0x10, EXC_TARGET_UNWIND = 0x20, EXC_COLLIDED_UNWIND = 0x40 };
enum : u32 { NT_ACCESS_VIOLATION = 0xC0000005, NT_BREAKPOINT = 0x80000003, NT_SINGLE_STEP = 0x80000004, NT_ILLEGAL = 0xC000001D, NT_DIVZERO = 0xC0000094,
             NT_INTOVF = 0xC0000095, NT_PRIVILEGED = 0xC0000096, NT_UNWIND = 0xC0000027, NT_CONSOLIDATE = 0x80000029, NT_LONGJUMP = 0x80000026, NT_CPP = 0xE06D7363 };
// the return addresses of calls made into the program
enum { K_VEH = 0, K_DISP, K_UNW, K_CONS, K_UEF, K_VCH };
// a dispatch in progress (frame D) and what the kernel leaves above it (block K: CONTEXT, EXCEPTION_RECORD, machine frame)
enum : u64 { K_SIZE = 0x5c0, K_REC = 0x4f0, K_MACH = 0x590 };
enum : u64 { D_TAG = 0, D_REC = 8, D_CTX = 0x10, D_PHASE = 0x18, D_INDEX = 0x1c, D_PTRS = 0x20, D_DC = 0x30, D_EST = 0x80, D_NESTED = 0x88, D_FLAGS = 0x90, D_FRAMES = 0x94,
             D_ORIGIN = 0x98, D_SOFT = 0x9c, D_SAVED = 0xa0, D_SAVEDRIP = 0x120, D_KIND = 0x128, D_C1 = 0x130, D_DECISION = 0x600, D_SIZE = 0x610 };
// an unwind in progress (frame U)
enum : u64 { U_TAG = 0, U_TARGET = 8, U_TARGETIP = 0x10, U_REC = 0x18, U_RETVAL = 0x20, U_CUR = 0x28, U_PREV = 0x30, U_HISTORY = 0x38, U_EST = 0x48, U_FLAGS = 0x50, U_FRAMES = 0x54,
             U_DC = 0x80, U_LOCALREC = 0xd0, U_CTXA = 0x170, U_CTXB = 0x640, U_SIZE = 0xb10 };
const u64 TAG_D = 0x5053445850534458ull, TAG_U = 0x574e5558574e5558ull, TAG_C = 0x4e4f43584e4f4358ull;
}  // namespace

struct Exc {
  Engine& E; WinEnv& W; Ctx& X;
  Exc(Engine& e, WinEnv& w) : E(e), W(w), X(e.X) { if (!X.tape.empty()) E.settle(); }

  // ---- memory (addresses the program controls: nothing below 0x10000 is touched)
  static bool okAddr(u64 a) { return a >= 0x10000 && a < 0x800000000000ull; }
  u64 q(u64 a) const { u64 v = 0; if (okAddr(a)) E.readMem(a, &v, 8); return v; }
  u32 d(u64 a) const { u32 v = 0; if (okAddr(a)) E.readMem(a, &v, 4); return v; }
  u8 b(u64 a) const { u8 v = 0; if (okAddr(a)) E.readMem(a, &v, 1); return v; }
  void pq(u64 a, u64 v) { if (okAddr(a)) E.writeMem(a, &v, 8); }
  void pd(u64 a, u32 v) { if (okAddr(a)) E.writeMem(a, &v, 4); }
  Val ld(u64 a) { if (!okAddr(a)) return Val{0, 0}; return E.load(a, 8); }
  void st(u64 a, Val v) { if (okAddr(a)) E.store(a, 8, v); }
  void zero(u64 a, size_t n) { std::vector<u8> z(n, 0); if (okAddr(a)) E.writeMem(a, z.data(), n); }
  void copy(u64 dst, u64 src, unsigned n) {       // expressions included
    if (!okAddr(dst) || !okAddr(src) || dst == src) return;
    std::vector<u8> bytes(n); std::vector<Cell> cells(n);
    const bool any = E.loadCells(src, n, bytes.data(), cells.data());
    E.storeCells(dst, n, bytes.data(), any ? cells.data() : nullptr);
  }
  u64 stackLow() const { return q(E.gsbase + 0x10); }
  u64 stackHigh() const { return q(E.gsbase + 0x08); }
  bool onStack(u64 a) const { return a >= stackLow() && a < stackHigh(); }

  // ---- CONTEXT records
  Val reg(u64 c, int r) { return ld(c + CX_RAX + 8 * (u64)r); }
  u64 regc(u64 c, int r) const { return q(c + CX_RAX + 8 * (u64)r); }
  void setReg(u64 c, int r, Val v) { st(c + CX_RAX + 8 * (u64)r, v); }
  // (rf: the CPU saves the flags of a fault with RF set, so the instruction can run again; traps leave it clear)
  void capture(u64 c, u32 flags, bool rf = false) {
    zero(c, CX_SIZE);
    pd(c + CX_FLAGS, flags); pd(c + CX_MXCSR, E.mxcsr);
    const u16 seg[6] = {0x33, 0x2b, 0x2b, 0x53, 0x2b, E.ssSel}; E.writeMem(c + CX_SEG, seg, sizeof seg);
    // EFLAGS: the flags which depend on the inputs keep their expressions
    const u64 f = E.rflags() | (rf ? 0x10000ull : 0); u32 fe = 0;
    static const u32 bits[6] = {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF};
    u64 conc = f & 0xffffffffull;
    for (u32 bit : bits) {
      const u32 e = E.flagExpr(bit);
      if (!e || X.isC(e)) continue;
      unsigned long pos; _BitScanForward(&pos, bit);
      conc &= ~(u64)bit;
      const u32 t = X.shl(X.zext(e, 32), X.cst(pos, 32)); fe = fe ? X.or_(fe, t) : t;
    }
    if (fe) fe = X.or_(fe, X.cst(conc, 32));
    E.store(c + CX_EFLAGS, 4, Val{f & 0xffffffffull, fe});
    for (int r = 0; r < 16; r++) E.store(c + CX_RAX + 8 * r, 8, Val{E.g[r], X.force(E.gs[r])});
    pq(c + CX_RIP, E.rip);
    // the debug registers: the kernel keeps them only while a breakpoint is enabled (else all read 0); DR6: the fixed ones
    // and what the #DB being raised found
    if ((flags & 0x10) && (E.dr7 & 0x55)) {
      for (int i = 0; i < 4; i++) pq(c + CX_DR0 + 8 * (u64)i, E.dr[i]);
      pq(c + CX_DR6, 0xffff0ff0ull | E.dbStatus); pq(c + CX_DR7, E.dr7 | 0x400);
    }
    const u16 cw = 0x27f; E.writeMem(c + CX_FLT, &cw, 2); pd(c + CX_FLT + 0x18, E.mxcsr); pd(c + CX_FLT + 0x1c, 0xffff);
    for (int r = 0; r < 16; r++) E.storeCells(c + CX_XMM0 + 16 * r, 16, E.v[r], ((E.vsym >> r) & 1) ? E.vc[r] : nullptr);
  }
  // the flags of a CONTEXT as NtContinue lets a thread go on with them: those a program may set (IF stays on; RF, VM and
  // IOPL are not its), and with TF one instruction runs, then a single step
  void restoreFlags(u64 c) {
    const Val f = E.load(c + CX_EFLAGS, 4);
    E.fl = Flags{}; E.fl.bits = (f.c & 0x244dd5ull) | 0x202;
    if (f.s) for (int pos : {0, 2, 4, 6, 7, 11}) { const u32 e = X.extract(f.s, pos, 1); if (!X.isC(e)) E.fl.sym[pos] = e; }
    E.tf = (E.fl.bits & 0x100) ? 2 : 0; E.movSS = 0;
    E.rfOnce = (u8)((f.c >> 16) & 1);                 // RF: the next instruction does not hit an execute breakpoint
    if (E.tf | E.rfOnce) E.dbgOn = 1;
  }
  // the debug registers of a CONTEXT whose flags have them, as the kernel takes them: user addresses only, the local
  // enables and the type / length fields of DR7 (a global enable is dropped; DR6 is not taken)
  void restoreDebug(u64 c) {
    if ((d(c + CX_FLAGS) & 0x100010u) != 0x100010u) return;
    for (int i = 0; i < 4; i++) { const u64 v = q(c + CX_DR0 + 8 * (u64)i); E.dr[i] = v <= 0x7ffffffeffffull ? v : 0; }
    E.dr7 = q(c + CX_DR7) & 0xffff0355ull;
    E.drUpdate();
  }
  void restore(u64 c) {
    for (int r = 0; r < 16; r++) { const Val v = ld(c + CX_RAX + 8 * r); E.g[r] = v.c; E.gs[r] = v.s; }
    E.gs[RSP] = 0;
    E.rip = q(c + CX_RIP);
    restoreFlags(c); restoreDebug(c); E.ssSel = 0x2b;
    const u32 mx = d(c + CX_MXCSR); if (mx) E.mxcsr = mx;
    for (int r = 0; r < 16; r++) {
      u8 by[16]; Cell cl[16];
      const bool any = E.loadCells(c + CX_XMM0 + 16 * r, 16, by, cl);
      memcpy(E.v[r], by, 16);
      if (any) { memcpy(E.vc[r], cl, sizeof cl); E.vsym |= 1u << r; }
      else if ((E.vsym >> r) & 1) { memset(E.vc[r], 0, 16 * sizeof(Cell)); bool up = false; for (int i = 16; i < 32; i++) up |= E.vc[r][i].e != 0; if (!up) E.vsym &= ~(1u << r); }
    }
  }

  // ---- RtlVirtualUnwind: the CONTEXT at c becomes the caller's. Returns the language handler asked for (type: 1
  // exception, 2 unwind), with its data and the establisher frame.
  struct Unw { u64 handler = 0, data = 0, est = 0; };
  Unw virtualUnwind(u32 type, u64 base, u64 pc, u64 fe, u64 c) {
    Unw r;
    u64 ui = base + (d(fe + 8) & ~3u);
    u8 h[4]; E.readMem(ui, h, 4);
    unsigned flags = h[0] >> 3, prolog = h[1], count = h[2], freg = h[3] & 15, foff = h[3] >> 4;
    const u32 begin = d(fe), endRva = d(fe + 4);
    u32 off = (u32)(pc - (base + begin));
    auto code = [&](u64 info, unsigned i) { u8 k[2]; E.readMem(info + 4 + 2 * (u64)i, k, 2); return std::pair<unsigned, unsigned>(k[0], k[1]); };   // (offset, op | info << 4)
    auto slot = [&](u64 info, unsigned i) { u16 v = 0; E.readMem(info + 4 + 2 * (u64)i, &v, 2); return (u64)v; };
    if (!freg) r.est = regc(c, RSP);
    else if (off >= prolog || (flags & 4)) r.est = regc(c, freg) - foff * 16;
    else {
      unsigned i = 0; while (i < count && (code(ui, i).second & 15) != 3) i++;
      r.est = i < count && off >= code(ui, i).first ? regc(c, freg) - foff * 16 : regc(c, RSP);
    }
    // in an epilogue: its instructions are run forward, and there is no handler
    {
      u8 nb[40] = {}; E.readMem(pc, nb, sizeof nb); unsigned n = 0; unsigned efreg = 0;
      if (nb[0] == 0x48 && nb[1] == 0x83 && nb[2] == 0xc4) n = 4;
      else if (nb[0] == 0x48 && nb[1] == 0x81 && nb[2] == 0xc4) n = 7;
      else if ((nb[0] & 0xfe) == 0x48 && nb[1] == 0x8d) {
        efreg = ((nb[0] & 1) << 3) | (nb[2] & 7);
        if (efreg != 0 && efreg == freg) { if ((nb[2] & 0xf8) == 0x60) n = 4; else if ((nb[2] & 0xf8) == 0xa0) n = 7; }
      }
      const unsigned first = n;
      while (n < 30) { if ((nb[n] & 0xf8) == 0x58) n += 1; else if ((nb[n] & 0xf0) == 0x40 && (nb[n + 1] & 0xf8) == 0x58) n += 2; else break; }
      bool in = false;
      if (nb[n] == 0xc3 || nb[n] == 0xc2 || (nb[n] == 0xf3 && nb[n + 1] == 0xc3)) in = true;
      else if (nb[n] == 0xeb || nb[n] == 0xe9) {
        i64 t = (i64)(pc + n - base); if (nb[n] == 0xeb) t += 2 + (i8)nb[n + 1]; else { i32 rel; memcpy(&rel, nb + n + 1, 4); t += 5 + rel; }
        if (t < (i64)begin || t >= (i64)endRva) in = true;
        else if (t == (i64)begin && !(flags & 4)) in = true;
      } else if (nb[n] == 0xff && nb[n + 1] == 0x25) in = true;
      else if ((nb[n] & 0xf8) == 0x48 && nb[n + 1] == 0xff && (nb[n + 2] & 0x38) == 0x20) in = true;
      if (in) {
        u64 sp = regc(c, RSP); unsigned k = 0;
        if (first == 4 && nb[1] == 0x83) { sp += (i64)(i8)nb[3]; k = 4; }
        else if (first == 7 && nb[1] == 0x81) { i32 v; memcpy(&v, nb + 3, 4); sp += (i64)v; k = 7; }
        else if (first == 4) { sp = regc(c, efreg) + (i64)(i8)nb[3]; k = 4; }
        else if (first == 7) { i32 v; memcpy(&v, nb + 3, 4); sp = regc(c, efreg) + (i64)v; k = 7; }
        while (k < n) {
          unsigned rn;
          if ((nb[k] & 0xf8) == 0x58) { rn = nb[k] & 7; k += 1; } else { rn = ((nb[k] & 1) << 3) | (nb[k + 1] & 7); k += 2; }
          setReg(c, (int)rn, ld(sp)); sp += 8;
        }
        pq(c + CX_RIP, q(sp)); pq(c + CX_RSP, sp + 8);
        return r;
      }
    }
    // the prologue backwards (chained unwind data: the parent's too)
    u64 cur = fe; bool machine = false;
    for (int depth = 0; depth < 32; depth++) {
      ui = base + (d(cur + 8) & ~3u); E.readMem(ui, h, 4);
      flags = h[0] >> 3; prolog = h[1]; count = h[2]; freg = h[3] & 15; foff = h[3] >> 4;
      off = (u32)(pc - (base + d(cur)));
      for (unsigned i = 0; i < count;) {
        const auto cd = code(ui, i); const unsigned op = cd.second & 15, info = cd.second >> 4;
        if (op == 6) { i++; continue; }                // where the epilogues are (version 2): nothing to undo
        if (off >= cd.first) {
          switch (op) {
          case 0: { const u64 sp = regc(c, RSP); setReg(c, (int)info, ld(sp)); pq(c + CX_RSP, sp + 8); break; }
          case 1: { u64 sz = slot(ui, ++i); if (info) sz += slot(ui, ++i) << 16; else sz *= 8; pq(c + CX_RSP, regc(c, RSP) + sz); break; }
          case 2: pq(c + CX_RSP, regc(c, RSP) + info * 8 + 8); break;
          case 3: pq(c + CX_RSP, regc(c, freg) - foff * 16); break;
          case 4: setReg(c, (int)info, ld(r.est + slot(ui, ++i) * 8)); break;
          case 5: { u64 o = slot(ui, i + 1) | (slot(ui, i + 2) << 16); i += 2; setReg(c, (int)info, ld(r.est + o)); break; }
          case 7: i += 2; break;
          case 8: copy(c + CX_XMM0 + 16 * info, r.est + slot(ui, ++i) * 16, 16); break;
          case 9: { u64 o = slot(ui, i + 1) | (slot(ui, i + 2) << 16); i += 2; copy(c + CX_XMM0 + 16 * info, r.est + o, 16); break; }
          case 10: { u64 sp = regc(c, RSP) + (info ? 8 : 0); pq(c + CX_RIP, q(sp)); pq(c + CX_RSP, q(sp + 24)); machine = true; break; }
          default: break;
          }
          i++;
        } else {
          static const u8 slots[16] = {1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 1, 1, 1, 1};
          i += slots[op]; if (op == 1 && info) i++;
        }
      }
      if (!(flags & 4)) break;
      cur = ui + 4 + 2 * (u64)((count + 1) & ~1u);       // the parent's entry follows the codes
    }
    if (!machine) { const u64 sp = regc(c, RSP); pq(c + CX_RIP, q(sp)); pq(c + CX_RSP, sp + 8); }
    if (off >= prolog && (flags & type)) { const u64 at = ui + 4 + 2 * (u64)((count + 1) & ~1u); r.handler = base + d(at); r.data = at + 4; }
    return r;
  }

  // ---- frames
  u64 magicAt(u64 pc) const { return pc >= WinEnv::MAGIC && pc < WinEnv::MAGIC + 0x100 && !(pc & 15) ? (pc - WinEnv::MAGIC) >> 4 : ~0ull; }
  // The walk met the return address of a call the dispatcher or the unwinder made (c: the context after the frame of
  // the function called was undone): the frames of the dispatch / unwind are not walked, the context they were working
  // on is taken up. Returns false when the stack does not hold what it should. nested: the establisher frame of the
  // handler which was running, when an exception was being dispatched there.
  bool through(u64 c, u64 k, u64* nested = nullptr) {
    const u64 f = regc(c, RSP) + 0x20;
    if (k == K_VEH || k == K_DISP || k == K_UEF || k == K_VCH) {
      if (q(f + D_TAG) != TAG_D) return false;
      if (nested && k == K_DISP) *nested = q(f + D_EST);
      callerOf(c, q(f + D_CTX));
      return true;
    }
    if (k == K_UNW) { if (q(f + U_TAG) != TAG_U) return false; copy(c, q(f + U_CUR), CX_SIZE); return true; }
    if (k == K_CONS) { if (q(f) != TAG_C) return false; callerOf(c, q(f + 8)); return true; }
    return false;
  }
  // what undoing ntdll's own frames gives (KiUserExceptionDispatcher's machine frame, RcConsolidateFrames): where the
  // saved context was and its nonvolatile registers; the others stay as the walk has them
  void callerOf(u64 c, u64 from) {
    for (int r : {RBX, RSP, RBP, RSI, RDI, R12, R13, R14, R15}) setReg(c, r, ld(from + CX_RAX + 8 * r));
    pq(c + CX_RIP, q(from + CX_RIP));
    copy(c + CX_XMM0 + 16 * 6, from + CX_XMM0 + 16 * 6, 160);
  }
  // (the first frame may be at any address: a call through a bad pointer faults there, with the return address on the stack)
  bool endOfStack(u64 pc, u64 sp, bool first = false) const { return (pc == 0 && !first) || pc == W.retAddr || !onStack(sp) || (sp & 7); }

  // a call into the program from frame f: it returns to magic(k), with f found again at rsp + 0x20
  void callOut(Api* a, u64 f, u64 fn, int k, u64 a0, u64 a1 = 0, u64 a2 = 0, u64 a3 = 0) {
    const u64 sp = f - 0x28;
    pq(sp, WinEnv::magic(k));
    E.g[RCX] = a0; E.g[RDX] = a1; E.g[R8] = a2; E.g[R9] = a3; E.gs[RCX] = E.gs[RDX] = E.gs[R8] = E.gs[R9] = 0;
    E.g[RSP] = sp; E.gs[RSP] = 0; E.rip = fn;
    if (a) a->done = true;
  }

  // is there anybody to take an exception raised here? (vectored handlers, the top-level filter, a frame with a handler)
  bool anyHandler() {
    if (q(WinEnv::STATE + 0x20) || q(WinEnv::STATE + 0x18)) return true;
    const u64 c = WinEnv::STATE + 0x1000;
    E.writeMem(c + CX_RAX, E.g, sizeof E.g); pq(c + CX_RIP, E.rip);
    for (int n = 0; n < 128; n++) {
      const u64 pc = q(c + CX_RIP), sp = regc(c, RSP);
      if (magicAt(pc) != ~0ull) return true;         // inside a handler: the dispatch in progress knows
      if (endOfStack(pc, sp, n == 0)) return false;
      u64 base = 0; const u64 fe = W.lookupFunctionEntry(E, pc, &base);
      if (!fe) { pq(c + CX_RIP, q(sp)); pq(c + CX_RSP, sp + 8); continue; }
      if (virtualUnwind(1, base, pc, fe, c).handler) return true;
    }
    return false;
  }

  // ---- the dispatch of an exception (RtlDispatchException): returns 1 when a handler was called (it comes back through
  // a magic address), 2 when the context was restored and execution continues there, 0 when nobody took the exception
  // (the registers are then as they were when it was raised)
  int dispatch(Api* a, u64 D) {
    const u64 rec = q(D + D_REC), ctx = q(D + D_CTX), c1 = D + D_C1;
    if (d(D + D_PHASE) == 0) {                        // vectored handlers, in order
      const u32 i = d(D + D_INDEX), n = (u32)std::min<u64>(q(WinEnv::STATE + 0x20), 16);
      if (i < n) { pd(D + D_INDEX, i + 1); callOut(a, D, q(WinEnv::STATE + 0x28 + 8 * (u64)i), K_VEH, D + D_PTRS); return 1; }
      pd(D + D_PHASE, 1); copy(c1, ctx, CX_SIZE);
    }
    bool fresh = d(D + D_FRAMES) == 0;
    while (d(D + D_PHASE) == 1) {                     // the frames, innermost first
      const u32 frames = d(D + D_FRAMES); pd(D + D_FRAMES, frames + 1);
      const bool first = fresh; fresh = false;
      const u64 pc = q(c1 + CX_RIP), sp = regc(c1, RSP);
      const u64 k = magicAt(pc);
      if (frames > 512) { pd(D + D_PHASE, 2); break; }
      if (k != ~0ull) {
        u64 nested = 0;
        if (!through(c1, k, &nested)) { pd(D + D_PHASE, 2); break; }
        if (nested) { pd(D + D_FLAGS, d(D + D_FLAGS) | EXC_NESTED_CALL); if (nested > q(D + D_NESTED)) pq(D + D_NESTED, nested); }
        fresh = true; continue;
      }
      if (endOfStack(pc, sp, first)) { pd(D + D_PHASE, 2); break; }
      u64 base = 0; const u64 fe = W.lookupFunctionEntry(E, pc, &base);
      if (!fe) { pq(c1 + CX_RIP, q(sp)); pq(c1 + CX_RSP, sp + 8); continue; }      // a leaf: only its return address is on the stack
      const Unw u = virtualUnwind(1, base, pc, fe, c1);
      if ((u.est & 7) || !onStack(u.est)) { pd(D + D_PHASE, 2); break; }
      if (!u.handler) { if (q(D + D_NESTED) == u.est) { pd(D + D_FLAGS, d(D + D_FLAGS) & ~EXC_NESTED_CALL); pq(D + D_NESTED, 0); } continue; }
      const u64 dc = D + D_DC;
      pq(dc + DC_CONTROLPC, pc); pq(dc + DC_IMAGEBASE, base); pq(dc + DC_FUNCTIONENTRY, fe); pq(dc + DC_ESTABLISHER, u.est); pq(dc + DC_TARGETIP, 0);
      pq(dc + DC_CONTEXT, c1); pq(dc + DC_HANDLER, u.handler); pq(dc + DC_HANDLERDATA, u.data); pq(dc + DC_HISTORY, 0); pq(dc + DC_SCOPEINDEX, 0);
      pd(rec + ER_FLAGS, (d(rec + ER_FLAGS) & EXC_NONCONTINUABLE) | (d(D + D_FLAGS) & EXC_NESTED_CALL));
      pq(D + D_EST, u.est);
      callOut(a, D, u.handler, K_DISP, rec, u.est, ctx, dc);
      return 1;
    }
    if (d(D + D_PHASE) == 2) {                        // nobody: the filter SetUnhandledExceptionFilter installed
      pd(D + D_PHASE, 3);
      const u64 f = q(WinEnv::STATE + 0x18);
      if (f) { callOut(a, D, f, K_UEF, D + D_PTRS); return 1; }
    }
    // unhandled: back to where it was raised (the flags as the CONTEXT has them: handlers' code ran meanwhile, and the
    // dispatcher cleared TF and DF)
    for (int r = 0; r < 16; r++) { const Val v = ld(D + D_SAVED + 8 * r); E.g[r] = v.c; E.gs[r] = v.s; }
    restoreFlags(ctx);
    E.rip = q(D + D_SAVEDRIP);
    return 0;
  }

  // the frames of a dispatch below sp: block K (CONTEXT of the exception, its record, the machine frame) and frame D.
  // The CONTEXT is captured from the engine as it is (the caller sets rip / rsp to what the record must say first).
  u64 open(u64 sp, u32 code, u32 flags, u64 address, u32 origin, bool soft, u32 kind, u64 recGiven = 0, bool rf = false) {
    const u64 K = (sp & ~15ull) - K_SIZE, D = K - D_SIZE, rec = recGiven ? recGiven : K + K_REC;
    zero(D, D_SIZE + K_SIZE);
    E.dbStatus |= E.dbHeld; E.dbHeld = 0;          // (a #DB mov ss held back past an instruction which raised this: its DR6)
    capture(K, 0x10001f, rf);
    // the kernel enters the dispatcher with TF and DF clear (the CONTEXT keeps them) and no single step pending; DR6 is
    // clean again for the next exception
    E.fl.bits &= ~0x500ull; E.tf = 0; E.movSS = 0; E.dbStatus = 0; E.rfOnce = 0;
    if (!recGiven) { pd(rec + ER_CODE, code); pd(rec + ER_FLAGS, flags); pq(rec + ER_ADDRESS, address); }
    pq(K + K_MACH, E.rip); pq(K + K_MACH + 8, 0x33); pq(K + K_MACH + 0x10, E.rflags()); pq(K + K_MACH + 0x18, E.g[RSP]); pq(K + K_MACH + 0x20, 0x2b);
    pq(D + D_TAG, TAG_D); pq(D + D_REC, rec); pq(D + D_CTX, K); pq(D + D_PTRS, rec); pq(D + D_PTRS + 8, K);
    pd(D + D_ORIGIN, origin); pd(D + D_SOFT, soft); pd(D + D_KIND, kind);
    return D;
  }
  void saveRegs(u64 D, u64 rip) { for (int r = 0; r < 16; r++) E.store(D + D_SAVED + 8 * r, 8, Val{E.g[r], X.force(E.gs[r])}); pq(D + D_SAVEDRIP, rip); }

  // execution continues with the context of the exception (NtContinue), after the vectored continue handlers
  int resume(Api* a, u64 D) {
    const u32 i = d(D + D_PHASE) >= 16 ? d(D + D_PHASE) - 16 : 0, n = (u32)std::min<u64>(q(WinEnv::STATE + 0xa8), 16);
    if (i < n) { pd(D + D_PHASE, 16 + i + 1); callOut(a, D, q(WinEnv::STATE + 0xb0 + 8 * (u64)i), K_VCH, D + D_PTRS); return 1; }
    restore(q(D + D_CTX));
    if (a) a->done = true;
    return 2;
  }

  // nobody took it, seen from the hook of a magic address: the path ends there, or (a guarded access) goes on without the guard
  void unhandled(Api& a, u64 D) {
    a.done = true;
    if (d(D + D_SOFT)) {
      const u64 decision = q(D + D_DECISION);         // nobody took it: there was nothing to decide
      if (decision && decision <= E.path.size() && E.path[decision - 1].pc == E.rip && E.path[decision - 1].taken <= 2) E.path.erase(E.path.begin() + (decision - 1));
      E.softRetry = E.rip; E.trapMemo.insert(E.rip ^ (E.g[RSP] * 0x9E3779B97F4A7C15ull)); return;
    }
    char buf[96]; const u64 rec = q(D + D_REC);
    snprintf(buf, sizeof buf, "unhandled exception 0x%08x at 0x%llx", d(rec + ER_CODE), (unsigned long long)q(rec + ER_ADDRESS));
    E.stopInfo = buf; a.stop = ST_EXCEPTION;
  }

  // the frame of the call which just returned to a magic address (its `ret` left rsp 0x20 below the frame)
  u64 frameAt(u64 tag) const { const u64 f = E.g[RSP] + 0x20; return q(f) == tag ? f : 0; }

  // ---- RtlUnwindEx: the frames from the caller's up to the target frame are undone, the handlers of those which have
  // one are called (termination handlers, destructors), then execution continues in the target frame at TargetIp.
  // Returns 1: a handler was called; 2: done, the context is restored; 0: no such frame (the path cannot go on).
  int unwind(Api* a, u64 U) {
    const u64 target = q(U + U_TARGET), rec = q(U + U_REC);
    bool fresh = d(U + U_FRAMES) == 0;
    for (;;) {
      u64 cur = q(U + U_CUR), prev = q(U + U_PREV);
      const u32 frames = d(U + U_FRAMES); pd(U + U_FRAMES, frames + 1);
      const bool first = fresh; fresh = false;
      const u64 pc = q(cur + CX_RIP), sp = regc(cur, RSP);
      if (frames > 1024) return 0;
      const u64 k = magicAt(pc);
      if (k != ~0ull) { if (!through(cur, k)) return 0; fresh = true; continue; }
      if (endOfStack(pc, sp, first)) return 0;
      u64 base = 0; const u64 fe = W.lookupFunctionEntry(E, pc, &base);
      if (!fe) { pq(cur + CX_RIP, q(sp)); pq(cur + CX_RSP, sp + 8); continue; }
      copy(prev, cur, CX_SIZE);
      const Unw u = virtualUnwind(2, base, pc, fe, prev);
      if ((u.est & 7) || !onStack(u.est) || (target && target < u.est)) return 0;
      pq(U + U_EST, u.est);
      if (u.handler) {
        u32 flags = d(U + U_FLAGS); if (u.est == target) flags |= EXC_TARGET_UNWIND;
        pd(rec + ER_FLAGS, flags);
        st(cur + CX_RAX, ld(U + U_RETVAL));
        const u64 dc = U + U_DC;
        pq(dc + DC_CONTROLPC, pc); pq(dc + DC_IMAGEBASE, base); pq(dc + DC_FUNCTIONENTRY, fe); pq(dc + DC_ESTABLISHER, u.est); pq(dc + DC_TARGETIP, q(U + U_TARGETIP));
        pq(dc + DC_CONTEXT, cur); pq(dc + DC_HANDLER, u.handler); pq(dc + DC_HANDLERDATA, u.data); pq(dc + DC_HISTORY, q(U + U_HISTORY)); pq(dc + DC_SCOPEINDEX, 0);
        callOut(a, U, u.handler, K_UNW, rec, u.est, cur, dc);
        return 1;
      }
      if (u.est == target) return finish(a, U);
      pq(U + U_CUR, prev); pq(U + U_PREV, cur);
    }
  }
  int afterUnwindHandler(Api* a, u64 U) {
    const u64 target = q(U + U_TARGET);
    if (q(U + U_EST) == target) return finish(a, U);
    const u64 cur = q(U + U_CUR), prev = q(U + U_PREV);
    pq(U + U_CUR, prev); pq(U + U_PREV, cur);
    return unwind(a, U);
  }
  int finish(Api* a, u64 U) {
    const u64 cur = q(U + U_CUR), rec = q(U + U_REC);
    st(cur + CX_RAX, ld(U + U_RETVAL));
    if (d(rec + ER_CODE) != NT_CONSOLIDATE) pq(cur + CX_RIP, q(U + U_TARGETIP));
    return restoreEx(a, cur, rec, U);
  }
  // RtlRestoreContext: longjmp buffers, the consolidation callback (a catch block run on top of the stack, which
  // returns where execution continues), then the registers
  int restoreEx(Api* a, u64 c, u64 rec, u64 below) {
    if (rec && d(rec + ER_CODE) == NT_LONGJUMP && d(rec + ER_NPARAMS) >= 1) {
      const u64 jb = q(rec + ER_INFO);
      static const int regs[9] = {RBX, RSP, RBP, RSI, RDI, R12, R13, R14, R15};
      for (int i = 0; i < 9; i++) setReg(c, regs[i], ld(jb + 8 + 8 * i));
      pq(c + CX_RIP, q(jb + 0x50)); pd(c + CX_MXCSR, d(jb + 0x58));
      copy(c + CX_XMM0 + 16 * 6, jb + 0x60, 160);
    } else if (rec && d(rec + ER_CODE) == NT_CONSOLIDATE && d(rec + ER_NPARAMS) >= 1) {
      const u64 f = (below & ~15ull) - 0x40;
      pq(f, TAG_C); pq(f + 8, c); pq(f + 0x10, rec);
      callOut(a, f, q(rec + ER_INFO), K_CONS, rec);
      return 1;
    }
    restore(c);
    if (a) a->done = true;
    return 2;
  }
};

// ------------------------------------------------------------------------------------------------ WinEnv
u64 WinEnv::lookupFunctionEntry(Engine& E, u64 pc, u64* imageBase) {
  auto rd32 = [&](u64 a) { u32 v = 0; E.readMem(a, &v, 4); return v; };
  auto search = [&](u64 tab, u64 n, u64 base) -> u64 {
    if (pc < base || pc - base > 0xffffffffull) return 0;
    const u32 rva = (u32)(pc - base);
    for (i64 lo = 0, hi = (i64)n - 1; lo <= hi;) {
      const i64 mid = (lo + hi) / 2; const u64 e = tab + 12 * (u64)mid;
      if (rva < rd32(e)) hi = mid - 1; else if (rva >= rd32(e + 4)) lo = mid + 1;
      else { u64 fe = e; for (int k = 0; k < 8 && (rd32(fe + 8) & 1); k++) fe = base + (rd32(fe + 8) & ~1u); return fe; }
    }
    return 0;
  };
  if (WinModule* m = moduleAt(pc)) {
    if (m->pdata && m->pdataSize >= 12) if (u64 fe = search(m->base + m->pdata, m->pdataSize / 12, m->base)) { if (imageBase) *imageBase = m->base; return fe; }
    return 0;
  }
  u64 n = 0; E.readMem(STATE + 0x130, &n, 8);      // tables the program added (RtlAddFunctionTable)
  for (u64 i = 0; i < n && i < 8; i++) {
    u64 t[3]; E.readMem(STATE + 0x138 + 24 * i, t, 24);
    if (u64 fe = search(t[0], t[1], t[2])) { if (imageBase) *imageBase = t[2]; return fe; }
  }
  return 0;
}

int WinEnv::onTrap(Engine& E, Stop s) {
  if (!exceptions) return 0;
  const u8 kind = E.trapKind; const u64 pc = E.rip;
  const bool soft = (kind == TK_READ || kind == TK_WRITE) && (E.trapArg >> 12) < E.guardSet;
  const u64 memo = pc ^ (E.g[RSP] * 0x9E3779B97F4A7C15ull);
  if (soft && E.trapMemo.count(memo)) return 2;
  if (++E.trapCount > 20000) return soft ? 2 : 0;    // an exception storm (a handler which continues at the same fault)
  // rip: where the CONTEXT says the thread is; addr: the record's ExceptionAddress when it is another place (0: rip).
  // The values are what Windows 11 on this kind of CPU reports (bench/exc/trap_tests.cpp, run natively).
  u32 code = 0, nparams = 0; u64 info[2] = {0, 0}, rip = pc, addr = 0;
  switch (kind) {
  case TK_BREAKPOINT: code = 0x80000003; nparams = 1; break;
  case TK_INVALID: code = 0xC000001D; break;
  case TK_DIVZERO: code = 0xC0000094; break;
  case TK_DIVOVF: code = 0xC0000095; break;
  case TK_PRIV: code = 0xC0000096; break;
  case TK_SINGLESTEP: code = 0x80000004; break;
  case TK_GP: code = 0xC0000005; nparams = 2; info[1] = ~0ull; break;
  case TK_INT:
    if (E.trapArg == 3) { code = 0x80000003; nparams = 1; rip = pc + 1; }                          // cd 03: one byte back from its end
    else if (E.trapArg == 0x101) { code = 0x80000004; rip = E.lastInsn.next; }                     // icebp: a trap, after the instruction
    else if (E.trapArg == 0x2d) {
      // the debug service: with rax 1, 3, 4 or 5 (print, symbols, command) nothing is raised; the byte after the
      // instruction is skipped either way. Else a breakpoint whose parameter is rax, reported one byte further.
      const u64 svc = E.g[RAX];
      if (svc == 1 || svc == 3 || svc == 4 || svc == 5) { E.rip = E.lastInsn.next + 1; return 1; }
      code = 0x80000003; nparams = 1; info[0] = svc; rip = E.lastInsn.next; addr = E.lastInsn.next + 1;
    }
    else if (E.trapArg == 0x2c) code = 0xC0000420;
    else if (E.trapArg == 4) { code = 0xC0000095; rip = E.lastInsn.next; addr = E.lastInsn.next - 1; }   // int 4: integer overflow
    else if (E.trapArg == 0x29) return 0;             // __fastfail: the process ends
    else { code = 0xC0000005; nparams = 2; info[1] = ~0ull; }
    break;
  case TK_READ: case TK_WRITE:
    code = 0xC0000005; nparams = 2; info[0] = kind == TK_WRITE; info[1] = E.trapArg;
    // a non-canonical address is a general protection fault: no address, reported as a read
    if (const u64 top = E.trapArg >> 47; top != 0 && top != 0x1ffff) { info[0] = 0; info[1] = ~0ull; }
    break;
  case TK_EXEC: code = 0xC0000005; nparams = 2; info[0] = 8; info[1] = E.trapArg; break;
  default: return 0;
  }
  if (static const bool log = getenv("UNSHROUD_EXC_LOG") != nullptr; log)      // every exception given to the handlers
    fprintf(stderr, "exception %x at %llx (address %llx%s), rsp %llx, instruction %llu%c", code, (unsigned long long)pc, (unsigned long long)info[1], soft ? ", soft" : "", (unsigned long long)E.g[RSP], (unsigned long long)E.icount, 10);
  try {
    Exc x(E, *this);
    if (!x.anyHandler()) { if (soft) E.trapMemo.insert(memo); return soft ? 2 : 0; }
    size_t decision = 0;
    if (soft && nullFaults == 2) {                    // do the handlers get it? Both answers are paths of the function
      const bool take = E.oracle(pc, true);
      if (!take) { E.trapMemo.insert(memo); return 2; }
      decision = E.path.size();
    }
    const u64 sp = E.g[RSP];
    E.rip = rip;
    // a fault's CONTEXT has RF set; breakpoints, single steps and the interrupts user code may raise (int 3, icebp, int 2c,
    // int 2d, int 4) are traps (bench/exc/trap_tests.cpp, trap2, run natively)
    const u64 v = E.trapArg;
    const bool fault = kind != TK_BREAKPOINT && kind != TK_SINGLESTEP && !(kind == TK_INT && (v == 3 || v == 0x101 || v == 0x2c || v == 0x2d || v == 4));
    const u64 D = x.open(sp, code, 0, addr ? addr : rip, 0, soft, kind, 0, fault);
    const u64 rec = x.q(D + D_REC);
    x.pd(rec + ER_NPARAMS, nparams); x.pq(rec + ER_INFO, info[0]); x.pq(rec + ER_INFO + 8, info[1]);
    x.saveRegs(D, pc);
    x.pq(D + D_DECISION, decision);
    const std::string was = E.stopInfo;
    const int r = x.dispatch(nullptr, D);
    if (r) return 1;
    if (decision && decision <= E.path.size()) E.path.erase(E.path.begin() + (decision - 1));   // nobody took it: there was nothing to decide
    E.stopInfo = was;
    if (soft) E.trapMemo.insert(memo);
    return soft ? 2 : 0;
  } catch (int) { return 0; }
}

void WinEnv::saveContext(Engine& E, u64 c) { Exc x(E, *this); x.capture(c, 0x10001f); }
void WinEnv::loadContext(Engine& E, u64 c) { Exc x(E, *this); x.restore(c); }

void WinEnv::excModels() {
  // ---- the magic addresses: a call made into the program returned
  auto lost = [](Api& a, const char* what) { a.E.stopInfo = what; a.stop = ST_FAULT; a.done = true; };
  model("@magic0", [this, lost](Api& a) {           // a vectored exception handler
    Exc x(a.E, *this); const u64 D = x.frameAt(TAG_D);
    if (!D) return lost(a, "exception frame lost");
    const int r = (u32)a.E.g[RAX] == 0xffffffffu ? x.resume(&a, D) : x.dispatch(&a, D);
    if (!r) x.unhandled(a, D);
  });
  model("@magic1", [this, lost](Api& a) {           // the handler of a frame, called for an exception
    Exc x(a.E, *this); const u64 D = x.frameAt(TAG_D);
    if (!D) return lost(a, "exception frame lost");
    const u32 disp = (u32)a.E.g[RAX]; const u64 rec = x.q(D + D_REC), est = x.q(D + D_EST);
    int r = 0;
    if (disp == 0) {                                  // ExceptionContinueExecution
      if (x.d(rec + ER_FLAGS) & EXC_NONCONTINUABLE) { x.pd(D + D_PHASE, 3); r = x.dispatch(&a, D); }
      else r = x.resume(&a, D);
    } else if (disp == 1 || disp == 2 || disp == 3) {
      if (disp == 2) { x.pd(D + D_FLAGS, x.d(D + D_FLAGS) | EXC_NESTED_CALL); const u64 n = x.q(D + D_DC + DC_ESTABLISHER); if (n > x.q(D + D_NESTED)) x.pq(D + D_NESTED, n); }
      else if (x.q(D + D_NESTED) == est) { x.pd(D + D_FLAGS, x.d(D + D_FLAGS) & ~EXC_NESTED_CALL); x.pq(D + D_NESTED, 0); }
      r = x.dispatch(&a, D);
    } else { x.pd(D + D_PHASE, 3); r = x.dispatch(&a, D); }
    if (!r) x.unhandled(a, D);
  });
  model("@magic2", [this, lost](Api& a) {           // the handler of a frame, called for an unwind
    Exc x(a.E, *this); const u64 U = x.frameAt(TAG_U);
    if (!U) return lost(a, "unwind frame lost");
    x.pd(U + U_FLAGS, x.d(U + U_FLAGS) & ~(EXC_TARGET_UNWIND | EXC_COLLIDED_UNWIND));
    if (!x.afterUnwindHandler(&a, U)) { a.E.stopInfo = "unwind: no target frame"; a.stop = ST_EXCEPTION; a.done = true; }
  });
  model("@magic3", [this, lost](Api& a) {           // the consolidation callback: where execution continues
    Exc x(a.E, *this); const u64 f = x.frameAt(TAG_C);
    if (!f) return lost(a, "unwind frame lost");
    const u64 c = x.q(f + 8);
    x.pq(c + CX_RIP, a.E.g[RAX]);
    x.restore(c); a.done = true;
  });
  model("@magic4", [this, lost](Api& a) {           // the top-level filter
    Exc x(a.E, *this); const u64 D = x.frameAt(TAG_D);
    if (!D) return lost(a, "exception frame lost");
    const int r = (u32)a.E.g[RAX] == 0xffffffffu ? x.resume(&a, D) : x.dispatch(&a, D);
    if (!r) x.unhandled(a, D);
  });
  model("@magic5", [this, lost](Api& a) {           // a vectored continue handler
    Exc x(a.E, *this); const u64 D = x.frameAt(TAG_D);
    if (!D) return lost(a, "exception frame lost");
    if ((u32)a.E.g[RAX] == 0xffffffffu) x.pd(D + D_PHASE, 16 + 64);   // no more of them
    x.resume(&a, D);
  });

  // ---- raising: the context is the caller's, as if the call had returned
  auto raise = [this](Api& a, Val code, u32 flags, const std::vector<Val>& params, u64 recGiven) {
    Exc x(a.E, *this); Engine& E = a.E;
    const u64 S = E.g[RSP], ret = x.q(S), at = E.rip;
    E.rip = ret; E.g[RSP] = S + 8;
    const u64 D = x.open(S, (u32)code.c, flags, at, 1, false, 0, recGiven), rec = x.q(D + D_REC);
    if (recGiven) x.pq(rec + ER_ADDRESS, ret);
    else {
      if (code.s) E.store(rec + ER_CODE, 4, Val{code.c & 0xffffffffull, E.X.extract(code.s, 0, 32)});   // a code which depends on the inputs: the handlers' tests of it are decisions
      x.pd(rec + ER_NPARAMS, (u32)params.size()); for (size_t i = 0; i < params.size(); i++) x.st(rec + ER_INFO + 8 * i, params[i]); }
    x.saveRegs(D, ret);
    if (!x.dispatch(&a, D)) x.unhandled(a, D);
  };
  model("RaiseException", [raise](Api& a) {
    Exc x(a.E, a.W); const u64 args = a.arg(3); std::vector<Val> p;
    if (Exc::okAddr(args)) for (u64 i = 0; i < std::min<u64>(a.arg(2) & 0xffffffff, 15); i++) p.push_back(x.ld(args + 8 * i));
    raise(a, a.argv(0), (u32)a.arg(1) & EXC_NONCONTINUABLE, p, 0);
  });
  model("RtlRaiseException", [raise](Api& a) { if (!Exc::okAddr(a.arg(0))) return a.ret(0); raise(a, Val{0, 0}, 0, {}, a.arg(0)); });
  model("RtlRaiseStatus", [raise](Api& a) { raise(a, a.argv(0), EXC_NONCONTINUABLE, {}, 0); });
  model("_CxxThrowException", [this, raise](Api& a) {
    WinModule* m = moduleAt(a.arg(1));
    raise(a, Val{NT_CPP, 0}, EXC_NONCONTINUABLE, {Val{0x19930520, 0}, a.argv(0), a.argv(1), Val{m ? m->base : 0, 0}}, 0);
  });
  // handlers an image imports instead of holding them: no model of theirs yet, the search goes on
  for (const char* n : {"__C_specific_handler", "__CxxFrameHandler", "__CxxFrameHandler2", "__CxxFrameHandler3", "__CxxFrameHandler4", "__GSHandlerCheck",
                        "__GSHandlerCheck_EH", "__GSHandlerCheck_EH4", "__GSHandlerCheck_SEH", "_except_handler4_common", "__gxx_personality_seh0"})
    model(n, [](Api& a) { a.ret(1); });

  // ---- unwinding
  auto unwindEx = [this](Api& a, bool ex) {
    Exc x(a.E, *this); Engine& E = a.E;
    const u64 S = E.g[RSP], ret = x.q(S), U = (S & ~15ull) - 0xb20;
    const u64 target = a.arg(0), targetIp = a.arg(1), orig = ex ? a.arg(4) : 0, history = ex ? a.arg(5) : 0; u64 rec = a.arg(2); const Val rv = a.argv(3);
    x.zero(U, U_SIZE);
    x.pq(U + U_TAG, TAG_U); x.pq(U + U_TARGET, target); x.pq(U + U_TARGETIP, targetIp); E.store(U + U_RETVAL, 8, rv); x.pq(U + U_HISTORY, history);
    const u64 cur = Exc::okAddr(orig) ? orig : U + U_CTXB;
    x.pq(U + U_CUR, cur); x.pq(U + U_PREV, U + U_CTXA);
    E.rip = ret; E.g[RSP] = S + 8;
    x.capture(cur, 0x10000f);
    if (!Exc::okAddr(rec)) { rec = U + U_LOCALREC; x.pd(rec + ER_CODE, NT_UNWIND); x.pq(rec + ER_ADDRESS, ret); }
    const u32 flags = EXC_UNWINDING | (target ? 0 : EXC_EXIT_UNWIND);
    x.pq(U + U_REC, rec); x.pd(U + U_FLAGS, flags); x.pd(rec + ER_FLAGS, flags);
    if (!x.unwind(&a, U)) { E.stopInfo = "unwind: no target frame"; a.stop = ST_EXCEPTION; a.done = true; }
  };
  model("RtlUnwindEx", [unwindEx](Api& a) { unwindEx(a, true); });
  model("RtlUnwind", [unwindEx](Api& a) { unwindEx(a, false); });
  model("RtlCaptureContext", [](Api& a) {
    Exc x(a.E, a.W); Engine& E = a.E; const u64 S = E.g[RSP], c = a.arg(0);
    E.rip = x.q(S); E.g[RSP] = S + 8;
    if (Exc::okAddr(c)) x.capture(c, 0x10000f);
    a.done = true;
  });
  model("RtlRestoreContext", [](Api& a) { Exc x(a.E, a.W); if (!Exc::okAddr(a.arg(0))) return a.ret(0); x.restoreEx(&a, a.arg(0), Exc::okAddr(a.arg(1)) ? a.arg(1) : 0, a.E.g[RSP]); });
  // GetThreadContext / SetThreadContext (and the Nt / Zw functions under them), of the thread itself (a handle of another
  // thread is not told apart): Get fills the CONTEXT as RtlCaptureContext sees the caller, with the debug registers if the
  // flags ask for them; Set takes the debug registers only (another part of the thread itself is not changed here)
  const auto getCtx = [](Api& a) -> bool {
    Exc x(a.E, a.W); Engine& E = a.E; const u64 c = a.arg(1);
    if (!Exc::okAddr(c)) return false;
    const u32 flags = x.d(c + CX_FLAGS); const u64 S = E.g[RSP], ip = E.rip;
    E.rip = x.q(S); E.g[RSP] = S + 8; x.capture(c, flags); E.rip = ip; E.g[RSP] = S;
    return true;
  };
  const auto setCtx = [](Api& a) -> bool {
    Exc x(a.E, a.W); const u64 c = a.arg(1);
    if (!Exc::okAddr(c)) return false;
    x.restoreDebug(c);
    return true;
  };
  model("NtGetContextThread", [getCtx](Api& a) { a.ret(getCtx(a) ? 0 : 0xC0000005); });
  model("NtSetContextThread", [setCtx](Api& a) { a.ret(setCtx(a) ? 0 : 0xC0000005); });
  alias("ZwGetContextThread", "NtGetContextThread"); alias("ZwSetContextThread", "NtSetContextThread");
  model("GetThreadContext", [getCtx](Api& a) { a.ret(getCtx(a) ? 1 : 0); });
  model("SetThreadContext", [setCtx](Api& a) { a.ret(setCtx(a) ? 1 : 0); });
  model("NtContinue", [](Api& a) { Exc x(a.E, a.W); if (!Exc::okAddr(a.arg(0))) return a.ret(0xC000000D); x.restore(a.arg(0)); a.done = true; });
  alias("ZwContinue", "NtContinue");
  model("RtlLookupFunctionEntry", [this](Api& a) {
    u64 base = 0; const u64 fe = lookupFunctionEntry(a.E, a.arg(0), &base);
    if (fe) a.putq(a.arg(1), base);
    a.ret(fe);
  });
  model("RtlVirtualUnwind", [](Api& a) {
    Exc x(a.E, a.W); const u64 fe = a.arg(3), c = a.arg(4);
    if (!Exc::okAddr(fe) || !Exc::okAddr(c)) return a.ret(0);
    const Exc::Unw u = x.virtualUnwind((u32)a.arg(0), a.arg(1), a.arg(2), fe, c);
    a.putq(a.arg(5), u.data); a.putq(a.arg(6), u.est);
    a.ret(u.handler);
  });
  model("RtlPcToFileHeader", [this](Api& a) { WinModule* m = moduleAt(a.arg(0)); const u64 b = m ? m->base : 0; a.putq(a.arg(1), b); a.ret(b); });

  // ---- handler lists (in emulated memory)
  auto addTo = [](Api& a, u64 list, bool first, u64 fn) {
    const u64 n = std::min<u64>(a.q(list), 16);
    if (n >= 16 || fn < 0x10000) return a.ret(0);
    if (first) { for (u64 i = n; i > 0; i--) a.putq(list + 8 + 8 * i, a.q(list + 8 * i)); a.putq(list + 8, fn); }
    else a.putq(list + 8 + 8 * n, fn);
    a.putq(list, n + 1); a.ret(fn);
  };
  auto removeFrom = [](Api& a, u64 list, u64 fn) {
    const u64 n = std::min<u64>(a.q(list), 16);
    for (u64 i = 0; i < n; i++) if (a.q(list + 8 + 8 * i) == fn) {
      for (u64 k = i; k + 1 < n; k++) a.putq(list + 8 + 8 * k, a.q(list + 16 + 8 * k));
      a.putq(list, n - 1); return a.ret(1);
    }
    a.ret(0);
  };
  model("AddVectoredExceptionHandler", [addTo](Api& a) { addTo(a, STATE + 0x20, (a.arg(0) & 0xffffffff) != 0, a.arg(1)); });
  model("RemoveVectoredExceptionHandler", [removeFrom](Api& a) { removeFrom(a, STATE + 0x20, a.arg(0)); });
  model("AddVectoredContinueHandler", [addTo](Api& a) { addTo(a, STATE + 0xa8, (a.arg(0) & 0xffffffff) != 0, a.arg(1)); });
  model("RemoveVectoredContinueHandler", [removeFrom](Api& a) { removeFrom(a, STATE + 0xa8, a.arg(0)); });
  alias("RtlAddVectoredExceptionHandler", "AddVectoredExceptionHandler"); alias("RtlRemoveVectoredExceptionHandler", "RemoveVectoredExceptionHandler");
  alias("RtlAddVectoredContinueHandler", "AddVectoredContinueHandler"); alias("RtlRemoveVectoredContinueHandler", "RemoveVectoredContinueHandler");
  model("SetUnhandledExceptionFilter", [](Api& a) { const u64 old = a.q(STATE + 0x18); a.putq(STATE + 0x18, a.arg(0)); a.ret(old); });
  alias("RtlSetUnhandledExceptionFilter", "SetUnhandledExceptionFilter");
  // without a filter of the program: the exception is not handled (what the system's own filter answers after its report)
  model("UnhandledExceptionFilter", [](Api& a) { const u64 f = a.q(STATE + 0x18); if (f < 0x10000) return a.ret(1); a.E.rip = f; a.done = true; });
  model("RtlAddFunctionTable", [](Api& a) {
    const u64 n = a.q(STATE + 0x130);
    if (n >= 8) return a.ret(0);
    a.putq(STATE + 0x138 + 24 * n, a.arg(0)); a.putq(STATE + 0x140 + 24 * n, a.arg(1) & 0xffffffff); a.putq(STATE + 0x148 + 24 * n, a.arg(2));
    a.putq(STATE + 0x130, n + 1); a.ret(1);
  });
  model("RtlAddGrowableFunctionTable", [](Api& a) {
    const u64 n = a.q(STATE + 0x130);
    if (n >= 8) return a.ret(0xC000009A);
    a.putq(STATE + 0x138 + 24 * n, a.arg(1)); a.putq(STATE + 0x140 + 24 * n, a.arg(2) & 0xffffffff); a.putq(STATE + 0x148 + 24 * n, a.arg(4));
    a.putq(STATE + 0x130, n + 1); a.putq(a.arg(0), a.arg(1)); a.ret(0);
  });
  model("RtlDeleteFunctionTable", [](Api& a) {
    const u64 n = std::min<u64>(a.q(STATE + 0x130), 8);
    for (u64 i = 0; i < n; i++) if (a.q(STATE + 0x138 + 24 * i) == a.arg(0)) {
      for (u64 k = i; k + 1 < n; k++) for (int j = 0; j < 3; j++) a.putq(STATE + 0x138 + 24 * k + 8 * j, a.q(STATE + 0x138 + 24 * (k + 1) + 8 * j));
      a.putq(STATE + 0x130, n - 1); return a.ret(1);
    }
    a.ret(0);
  });
}

}  // namespace unshroud
