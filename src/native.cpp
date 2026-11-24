// unshroud - instructions without symbolic semantics run on this CPU: operands are loaded from the engine, the memory operand
// is moved to a scratch buffer (re-encoded with Zydis), what the instruction writes is copied back. Inputs which hold
// expressions are made concrete first (the path keeps the constraints).
#include "engine.hpp"
#include <Zydis/Zydis.h>
#include <windows.h>
#include <cstddef>
#include <cstdio>

extern "C" void unshroud_native(void* state, void* code);

namespace unshroud {

struct NState { u64 gpr[16]; u64 rflags; u32 mxcsr; u32 pad0; u64 pad1[2]; alignas(32) u8 ymm[16][32]; };
static_assert(offsetof(NState, rflags) == 128 && offsetof(NState, mxcsr) == 136 && offsetof(NState, ymm) == 160, "layout");

static u8* codePage() {
  static u8* page = nullptr;
  if (!page) page = (u8*)VirtualAlloc(nullptr, 4096, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
  return page;
}

static int gprOf(ZydisRegister r) {
  if (r == ZYDIS_REGISTER_NONE) return -1;
  ZydisRegisterClass c = ZydisRegisterGetClass(r);
  if (c != ZYDIS_REGCLASS_GPR64 && c != ZYDIS_REGCLASS_GPR32 && c != ZYDIS_REGCLASS_GPR16 && c != ZYDIS_REGCLASS_GPR8) return -1;
  int id = ZydisRegisterGetId(ZydisRegisterGetLargestEnclosing(ZYDIS_MACHINE_MODE_LONG_64, r));
  return id < 16 ? id : 99;
}

static ZydisRegister gpr64(int i) {
  static const ZydisRegister t[16] = {ZYDIS_REGISTER_RAX, ZYDIS_REGISTER_RCX, ZYDIS_REGISTER_RDX, ZYDIS_REGISTER_RBX, ZYDIS_REGISTER_RSP, ZYDIS_REGISTER_RBP,
    ZYDIS_REGISTER_RSI, ZYDIS_REGISTER_RDI, ZYDIS_REGISTER_R8, ZYDIS_REGISTER_R9, ZYDIS_REGISTER_R10, ZYDIS_REGISTER_R11, ZYDIS_REGISTER_R12,
    ZYDIS_REGISTER_R13, ZYDIS_REGISTER_R14, ZYDIS_REGISTER_R15};
  return t[i];
}

static void concretizeVec(Engine& E, const Insn& I, int r) {
  for (int o = 0; o < 32; o += 8) {
    u32 any = 0; for (int i = 0; i < 8; i++) any |= E.vc[r][o + i].e;
    if (!any) continue;
    u32 e = cellsExpr(E.X, E.v[r] + o, E.vc[r] + o, 8);
    u64 c; memcpy(&c, E.v[r] + o, 8);
    E.addConstraint(E.X.eq(e, E.X.cst(c, 64)), I.addr, 0, 0, 3);
    memset(E.vc[r] + o, 0, 8 * sizeof(Cell));
  }
  E.vsym &= ~(1u << r);
}

// the guest address of the memory operand (symbolic parts made concrete, as the engine does)
static u64 memAddress(Engine& E, const Insn& I, const Opnd& od) {
  Ctx& X = E.X;
  u64 k = (u64)od.disp + (od.base == 16 ? I.next : 0);
  u64 seg = od.seg == RK_FS ? E.fsbase : od.seg == RK_GS ? E.gsbase : 0;
  u32 e = 0; u64 rest = k + seg;
  if (od.base != 0xff && od.base != 16) { k += E.g[od.base]; if (E.gs[od.base]) e = E.gs[od.base]; else rest += E.g[od.base]; }
  if (od.index != 0xff) {
    k += E.g[od.index] * od.scale;
    if (E.gs[od.index]) { u32 t = X.mul(E.gs[od.index], X.cst(od.scale, 64)); e = e ? X.add(e, t) : t; } else rest += E.g[od.index] * od.scale;
  }
  k += seg;
  if (I.asz == 4) k &= 0xffffffffull;
  if (e) E.concretized(X.add(e, X.cst(rest, 64)), k, 64, I.addr, 1);
  return k;
}

// 0, or the exception code of a fault in the instruction (it then did nothing which matters: its outputs are not copied back)
static unsigned long callNative(void* s, void* code) {
  // the host's MXCSR and direction flag are the host's again afterwards, whether the instruction completed or faulted
  const unsigned int csr = _mm_getcsr();
  unsigned long r = 0;
  __try { unshroud_native(s, code); }
  __except (EXCEPTION_EXECUTE_HANDLER) { r = GetExceptionCode(); __writeeflags(__readeflags() & ~0x400ull); _mm256_zeroupper(); }
  _mm_setcsr(csr);
  return r;
}

Stop nativeExec(Engine& E, const Insn& I) {
  u8 bytes[16]; E.readMem(I.addr, bytes, 15);
  ZydisDecoder dec; ZydisDecoderInit(&dec, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_STACK_WIDTH_64);
  ZydisDecodedInstruction zi; ZydisDecodedOperand zo[ZYDIS_MAX_OPERAND_COUNT];
  if (!ZYAN_SUCCESS(ZydisDecoderDecodeFull(&dec, bytes, 15, &zi, zo))) return ST_UNSUPPORTED;
  switch (zi.meta.isa_ext) {
  // A call of a hypervisor or of an enclave (vmcall, vmmcall, vmfunc, getsec, enclu ...) never reaches this machine's:
  // the program gets what a process gets where nothing answers such calls, an invalid-opcode exception.
  case ZYDIS_ISA_EXT_VTX: case ZYDIS_ISA_EXT_VMFUNC: case ZYDIS_ISA_EXT_SVM: case ZYDIS_ISA_EXT_SNP: case ZYDIS_ISA_EXT_TDX: case ZYDIS_ISA_EXT_SMX:
  case ZYDIS_ISA_EXT_SGX: case ZYDIS_ISA_EXT_SGX_ENCLV:
    // Where unknown memory is input, whether a hypervisor answers vmcall / vmmcall is a decision of the path too (an
    // explorer flips it): if one does, what it returns in rax is unknown.
    if (E.lazyMem && (zi.mnemonic == ZYDIS_MNEMONIC_VMCALL || zi.mnemonic == ZYDIS_MNEMONIC_VMMCALL) && E.oracle(I.addr * 0x9E3779B97F4A7C15ull ^ 0x766d63616c6cull, false)) {
      const Val v = E.ucValue(I.addr, "hv"); E.g[RAX] = v.c; E.gs[RAX] = v.s;
      return ST_NONE;
    }
    E.stopInfo = "invalid opcode"; E.trapKind = TK_INVALID; E.rip = I.addr; return ST_EXCEPTION;
  default: break;
  }
  switch (zi.meta.category) {
  case ZYDIS_CATEGORY_COND_BR: case ZYDIS_CATEGORY_UNCOND_BR: case ZYDIS_CATEGORY_CALL: case ZYDIS_CATEGORY_RET: case ZYDIS_CATEGORY_SYSCALL:
  case ZYDIS_CATEGORY_INTERRUPT: case ZYDIS_CATEGORY_SYSRET: case ZYDIS_CATEGORY_SYSTEM: case ZYDIS_CATEGORY_IO: case ZYDIS_CATEGORY_IOSTRINGOP:
  case ZYDIS_CATEGORY_STRINGOP: case ZYDIS_CATEGORY_PUSH: case ZYDIS_CATEGORY_POP: case ZYDIS_CATEGORY_X87_ALU: case ZYDIS_CATEGORY_SEMAPHORE:
    return ST_UNSUPPORTED;
  default: break;
  }
  if (zi.meta.isa_ext == ZYDIS_ISA_EXT_X87 || zi.meta.isa_ext == ZYDIS_ISA_EXT_XSAVE || zi.meta.isa_ext == ZYDIS_ISA_EXT_XSAVEOPT) return ST_UNSUPPORTED;
  switch (zi.meta.isa_ext) {
  // What changes or reads state of this thread or this CPU which is not the guest's (segment bases, protection keys,
  // shadow stacks, transactions, user interrupts, tiles, key handles, waits) is not run here either.
  case ZYDIS_ISA_EXT_RDWRFSGS: case ZYDIS_ISA_EXT_PKU: case ZYDIS_ISA_EXT_CET: case ZYDIS_ISA_EXT_MPX: case ZYDIS_ISA_EXT_RTM: case ZYDIS_ISA_EXT_TSX_LDTRK:
  case ZYDIS_ISA_EXT_UINTR: case ZYDIS_ISA_EXT_ENQCMD: case ZYDIS_ISA_EXT_AMX_TILE: case ZYDIS_ISA_EXT_AMX_BF16: case ZYDIS_ISA_EXT_AMX_FP16: case ZYDIS_ISA_EXT_AMX_INT8:
  case ZYDIS_ISA_EXT_KEYLOCKER: case ZYDIS_ISA_EXT_KEYLOCKER_WIDE: case ZYDIS_ISA_EXT_PCONFIG: case ZYDIS_ISA_EXT_MONITOR: case ZYDIS_ISA_EXT_MONITORX:
  case ZYDIS_ISA_EXT_WAITPKG: case ZYDIS_ISA_EXT_INVPCID: case ZYDIS_ISA_EXT_MSRLIST: case ZYDIS_ISA_EXT_WRMSRNS: case ZYDIS_ISA_EXT_LKGS: case ZYDIS_ISA_EXT_FRED:
  case ZYDIS_ISA_EXT_PT: case ZYDIS_ISA_EXT_HRESET: case ZYDIS_ISA_EXT_PADLOCK: case ZYDIS_ISA_EXT_SMAP: case ZYDIS_ISA_EXT_MCOMMIT: case ZYDIS_ISA_EXT_PBNDKB:
  case ZYDIS_ISA_EXT_RDPRU: case ZYDIS_ISA_EXT_AMD_INVLPGB: case ZYDIS_ISA_EXT_XSAVES: case ZYDIS_ISA_EXT_XSAVEC: case ZYDIS_ISA_EXT_APXEVEX: case ZYDIS_ISA_EXT_APXLEGACY:
    return ST_UNSUPPORTED;
  default: break;
  }
  // never run what this process may not run (privileged, I/O, interrupt flag, MSRs, caches, descriptor tables)
  if (zi.attributes & ZYDIS_ATTRIB_IS_PRIVILEGED) return ST_UNSUPPORTED;
  switch (zi.mnemonic) {
  case ZYDIS_MNEMONIC_CLI: case ZYDIS_MNEMONIC_STI: case ZYDIS_MNEMONIC_HLT: case ZYDIS_MNEMONIC_IN: case ZYDIS_MNEMONIC_OUT: case ZYDIS_MNEMONIC_INSB:
  case ZYDIS_MNEMONIC_INSW: case ZYDIS_MNEMONIC_INSD: case ZYDIS_MNEMONIC_OUTSB: case ZYDIS_MNEMONIC_OUTSW: case ZYDIS_MNEMONIC_OUTSD: case ZYDIS_MNEMONIC_RDMSR:
  case ZYDIS_MNEMONIC_WRMSR: case ZYDIS_MNEMONIC_RDPMC: case ZYDIS_MNEMONIC_INVD: case ZYDIS_MNEMONIC_WBINVD: case ZYDIS_MNEMONIC_INVLPG: case ZYDIS_MNEMONIC_LGDT:
  case ZYDIS_MNEMONIC_LIDT: case ZYDIS_MNEMONIC_LLDT: case ZYDIS_MNEMONIC_LTR: case ZYDIS_MNEMONIC_SWAPGS: case ZYDIS_MNEMONIC_CLTS: case ZYDIS_MNEMONIC_LMSW:
    return ST_UNSUPPORTED;
  default: break;
  }
  // bit strings: a register offset reaches beyond the operand
  if ((zi.mnemonic == ZYDIS_MNEMONIC_BT || zi.mnemonic == ZYDIS_MNEMONIC_BTS || zi.mnemonic == ZYDIS_MNEMONIC_BTR || zi.mnemonic == ZYDIS_MNEMONIC_BTC) &&
      zo[0].type == ZYDIS_OPERAND_TYPE_MEMORY && zo[1].type == ZYDIS_OPERAND_TYPE_REGISTER) return ST_UNSUPPORTED;
  bool used[16] = {}; int memop = -1;
  for (unsigned i = 0; i < zi.operand_count; i++) {
    const ZydisDecodedOperand& o = zo[i];
    if (o.type == ZYDIS_OPERAND_TYPE_REGISTER) {
      ZydisRegisterClass c = ZydisRegisterGetClass(o.reg.value);
      if (c == ZYDIS_REGCLASS_ZMM || c == ZYDIS_REGCLASS_MASK || c == ZYDIS_REGCLASS_X87 || c == ZYDIS_REGCLASS_MMX || c == ZYDIS_REGCLASS_CONTROL || c == ZYDIS_REGCLASS_DEBUG) return ST_UNSUPPORTED;
      int g = gprOf(o.reg.value); if (g == 99 || g == 4) return ST_UNSUPPORTED;
      if (g >= 0) used[g] = true;
      if ((c == ZYDIS_REGCLASS_XMM || c == ZYDIS_REGCLASS_YMM) && ZydisRegisterGetId(o.reg.value) >= 16) return ST_UNSUPPORTED;
    } else if (o.type == ZYDIS_OPERAND_TYPE_MEMORY) {
      if (o.visibility != ZYDIS_OPERAND_VISIBILITY_EXPLICIT || o.mem.type != ZYDIS_MEMOP_TYPE_MEM || memop >= 0) return ST_UNSUPPORTED;
      memop = (int)i;
      if (gprOf(o.mem.index) == 4) return ST_UNSUPPORTED;            // (rsp as a base is fine: the operand is moved to the scratch buffer)
      if (gprOf(o.mem.base) >= 0) used[gprOf(o.mem.base)] = true;
      if (gprOf(o.mem.index) >= 0) used[gprOf(o.mem.index)] = true;
    } else if (o.type == ZYDIS_OPERAND_TYPE_POINTER) return ST_UNSUPPORTED;
  }
  int scr = -1;
  for (int c : {11, 10, 9, 8, 3, 6, 7, 5, 12, 13, 14, 15}) if (!used[c]) { scr = c; break; }
  if (scr < 0) return ST_UNSUPPORTED;
  ZydisEncoderRequest req;
  if (!ZYAN_SUCCESS(ZydisEncoderDecodedInstructionToEncoderRequest(&zi, zo, zi.operand_count_visible, &req))) return ST_UNSUPPORTED;
  if (memop >= 0) {
    if ((unsigned)memop >= req.operand_count) return ST_UNSUPPORTED;
    auto& m = req.operands[memop].mem;
    m.base = gpr64(scr); m.index = ZYDIS_REGISTER_NONE; m.scale = 0; m.displacement = 0;
  }
  u8* code = codePage(); ZyanUSize len = 15;
  if (!ZYAN_SUCCESS(ZydisEncoderEncodeInstruction(&req, code, &len))) return ST_UNSUPPORTED;
  code[len] = 0xC3;
  const ZydisAccessedFlags* af = zi.cpu_flags;
  // inputs which hold expressions are made concrete
  for (unsigned i = 0; i < zi.operand_count; i++) {
    const ZydisDecodedOperand& o = zo[i];
    if (o.type != ZYDIS_OPERAND_TYPE_REGISTER || !(o.actions & ZYDIS_OPERAND_ACTION_MASK_READ)) continue;
    int g = gprOf(o.reg.value);
    if (g >= 0 && E.gs[g]) { E.addConstraint(E.X.eq(E.gs[g], E.X.cst(E.g[g], 64)), I.addr, 0, 0, 3); E.gs[g] = 0; }
    ZydisRegisterClass c = ZydisRegisterGetClass(o.reg.value);
    if (c == ZYDIS_REGCLASS_XMM || c == ZYDIS_REGCLASS_YMM) { int r = ZydisRegisterGetId(o.reg.value); if (E.vsym & (1u << r)) concretizeVec(E, I, r); }
  }
  if (af && (af->tested & 0xfff))
    for (u32 bit : {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF}) if (af->tested & bit) { Val f = E.flag(bit); if (f.s) E.addConstraint(f.c ? f.s : E.X.not_(f.s), I.addr, 0, 0, 3); }
  alignas(64) static u8 scratch[128];
  u64 maddr = 0; unsigned msize = 0;
  if (memop >= 0) {
    msize = zo[memop].size / 8;
    const Opnd* od = nullptr;
    for (unsigned i = 0; i < I.nops; i++) if (I.op[i].type == OT_MEM) od = &I.op[i];
    if (msize == 0 || msize > 64 || !od) return ST_UNSUPPORTED;
    maddr = memAddress(E, I, *od);
    Cell cl[64];
    const bool symMem = E.loadCells(maddr, msize, scratch, cl);
    for (unsigned o = 0; symMem && o < msize; o += 8) {
      unsigned n = std::min(8u, msize - o); u32 any = 0;
      for (unsigned i = 0; i < n; i++) any |= cl[o + i].e;
      if (!any) continue;
      u64 c = 0; memcpy(&c, scratch + o, n);
      E.addConstraint(E.X.eq(cellsExpr(E.X, scratch + o, cl + o, n), E.X.cst(c, n * 8)), I.addr, 0, 0, 3);
    }
  }
  NState* s = (NState*)_aligned_malloc(sizeof(NState), 64);
  for (int r = 0; r < 16; r++) s->gpr[r] = E.g[r];
  s->gpr[scr] = (u64)(uintptr_t)scratch;
  s->rflags = (E.rflags() & 0xcd5) | 0x202;
  s->mxcsr = E.mxcsr;
  memcpy(s->ymm, E.v, sizeof s->ymm);
  if (callNative(s, code)) { _aligned_free(s); return ST_UNSUPPORTED; }
  for (unsigned i = 0; i < zi.operand_count; i++) {
    const ZydisDecodedOperand& o = zo[i];
    if (o.type != ZYDIS_OPERAND_TYPE_REGISTER || !(o.actions & ZYDIS_OPERAND_ACTION_MASK_WRITE)) continue;
    int g = gprOf(o.reg.value);
    if (g >= 0) { E.g[g] = s->gpr[g]; E.gs[g] = 0; continue; }
    ZydisRegisterClass c = ZydisRegisterGetClass(o.reg.value);
    if (c == ZYDIS_REGCLASS_XMM || c == ZYDIS_REGCLASS_YMM) { int r = ZydisRegisterGetId(o.reg.value); memcpy(E.v[r], s->ymm[r], 32); memset(E.vc[r], 0, sizeof E.vc[r]); E.vsym &= ~(1u << r); }
  }
  E.mxcsr = s->mxcsr;                        // (the status flags an instruction sets are kept, whatever the operand list says)
  if (memop >= 0 && (zo[memop].actions & ZYDIS_OPERAND_ACTION_MASK_WRITE)) { if (E.dbWatch) E.dataCheck(maddr, msize, true); E.writeMem(maddr, scratch, msize); }
  if (af) {
    u32 changed = (af->modified | af->set_0 | af->set_1 | af->undefined) & (FL_CF | FL_PF | FL_AF | FL_ZF | FL_SF | FL_OF);
    for (u32 bit : {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF}) if (changed & bit) {
      unsigned long pos; _BitScanForward(&pos, bit);
      E.fl.lazy &= ~bit; E.fl.prev.lazy &= ~bit;
      E.fl.bits = (E.fl.bits & ~(1ull << pos)) | (s->rflags & (1ull << pos)); E.fl.sym[pos] = 0;
    }
  }
  _aligned_free(s);
  return ST_NONE;
}

}  // namespace unshroud
