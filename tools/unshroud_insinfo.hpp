// What an instruction is, statically (Zydis): the registers and flags it reads / writes, its explicit memory operand,
// its kind. Shared by unshroud_tseg (what is a constant along a recorded path) and unshroud_deob (the replay).
#pragma once
#include <Zydis/Zydis.h>
#include <cstdint>
#include <cstddef>

namespace insinfo {
typedef uint8_t u8; typedef uint16_t u16; typedef uint32_t u32; typedef uint64_t u64; typedef int64_t i64;
enum : u8 { K_OTHER = 0, K_JCC, K_JMP, K_JMPI, K_CALL, K_CALLI, K_RET, K_ENV, K_TRAP };
struct MemOp { bool on = false; u8 base = 0xff, index = 0xff, scale = 0, seg = 0, size = 0, opi = 0; i64 disp = 0; bool rd = false, wr = false, agen = false; };
struct InsInfo {
  bool rep = false, decoded = false;
  u8 len = 0, kind = 0, nexp = 0, dstReg = 0xff; u16 mn = 0;
  u32 rd = 0, wr = 0, wrPart = 0, envOut = 0; u8 rdF = 0, wrF = 0; MemOp m;   // registers: bit 0-15 GPR, 16-31 XMM; flags: CF PF AF ZF SF OF DF
  u8 opReg[4] = {0xff, 0xff, 0xff, 0xff}; u8 opSize[4] = {}; u8 opAct[4] = {};  // explicit operands: register (0-15 GPR, 16-31 XMM) or 0xfe memory / 0xfd immediate
  u8 tgReg = 0xff; bool tgMem = false; i64 imm = 0; bool hasImm = false;        // call / jmp: the register which holds the target, or a memory operand; the immediate
};
inline int regIdx(ZydisRegister r) {
  if (r == ZYDIS_REGISTER_NONE) return -1;
  const ZydisRegisterClass c = ZydisRegisterGetClass(r);
  if (c == ZYDIS_REGCLASS_GPR8 || c == ZYDIS_REGCLASS_GPR16 || c == ZYDIS_REGCLASS_GPR32 || c == ZYDIS_REGCLASS_GPR64) return (int)ZydisRegisterGetLargestEnclosing(ZYDIS_MACHINE_MODE_LONG_64, r) - (int)ZYDIS_REGISTER_RAX;
  if (c == ZYDIS_REGCLASS_XMM || c == ZYDIS_REGCLASS_YMM || c == ZYDIS_REGCLASS_ZMM) return 16 + (ZydisRegisterGetId(r) & 15);
  return -1;
}
inline u8 flagBits(u32 m) { return (u8)((m & 1) | ((m >> 1) & 2) | ((m >> 2) & 4) | ((m >> 3) & 8) | ((m >> 3) & 16) | ((m >> 6) & 32) | ((m >> 4) & 64)); }   // CF PF AF ZF SF OF DF
inline bool fullXmmWrite(ZydisMnemonic mn) {
  switch (mn) {
  case ZYDIS_MNEMONIC_MOVD: case ZYDIS_MNEMONIC_MOVQ: case ZYDIS_MNEMONIC_MOVDQA: case ZYDIS_MNEMONIC_MOVDQU: case ZYDIS_MNEMONIC_MOVAPS: case ZYDIS_MNEMONIC_MOVUPS:
  case ZYDIS_MNEMONIC_MOVAPD: case ZYDIS_MNEMONIC_MOVUPD: case ZYDIS_MNEMONIC_PSHUFD: case ZYDIS_MNEMONIC_PSHUFLW: case ZYDIS_MNEMONIC_PSHUFHW: case ZYDIS_MNEMONIC_LDDQU:
  case ZYDIS_MNEMONIC_PMOVZXBW: case ZYDIS_MNEMONIC_PMOVZXBD: case ZYDIS_MNEMONIC_PMOVZXWD: case ZYDIS_MNEMONIC_PMOVZXDQ: case ZYDIS_MNEMONIC_MOVDDUP: case ZYDIS_MNEMONIC_MOVSHDUP: case ZYDIS_MNEMONIC_MOVSLDUP:
    return true;
  default: return false; }
}
// false: the bytes are no instruction (len = 1)
inline bool decodeIns(const ZydisDecoder& dec, const u8* bytes, size_t avail, InsInfo& s) {
  s.decoded = true;
  ZydisDecodedInstruction zi; ZydisDecodedOperand zo[ZYDIS_MAX_OPERAND_COUNT];
  if (avail < 15 || !ZYAN_SUCCESS(ZydisDecoderDecodeFull(&dec, bytes, 15, &zi, zo))) { s.len = 1; return false; }
  s.len = zi.length; s.mn = (u16)zi.mnemonic; s.rep = (zi.attributes & (ZYDIS_ATTRIB_HAS_REP | ZYDIS_ATTRIB_HAS_REPE | ZYDIS_ATTRIB_HAS_REPNE)) != 0;
  const bool vex = zi.encoding != ZYDIS_INSTRUCTION_ENCODING_LEGACY;
  for (int i = 0; i < zi.operand_count; i++) {
    const ZydisDecodedOperand& o = zo[i];
    const bool rdA = o.actions & (ZYDIS_OPERAND_ACTION_READ | ZYDIS_OPERAND_ACTION_CONDREAD), wrA = o.actions & (ZYDIS_OPERAND_ACTION_WRITE | ZYDIS_OPERAND_ACTION_CONDWRITE);
    const bool expl = o.visibility == ZYDIS_OPERAND_VISIBILITY_EXPLICIT && i < 4;
    if (expl) { s.nexp = (u8)(i + 1); s.opSize[i] = (u8)(o.size / 8); s.opAct[i] = (u8)((rdA ? 1 : 0) | (wrA ? 2 : 0)); }
    if (o.type == ZYDIS_OPERAND_TYPE_REGISTER) {
      const int r = regIdx(o.reg.value);
      if (r < 0) continue;
      if (expl) { s.opReg[i] = (u8)r; if (i == 0 && wrA) s.dstReg = (u8)r; }
      if (rdA) s.rd |= 1u << r;
      if (wrA) {
        s.wr |= 1u << r;
        const bool part = r < 16 ? o.size < 32 : (!vex && !fullXmmWrite(zi.mnemonic) && !rdA);
        if (part || (o.actions & ZYDIS_OPERAND_ACTION_CONDWRITE)) { s.wrPart |= 1u << r; s.rd |= 1u << r; }
      }
    } else if (o.type == ZYDIS_OPERAND_TYPE_MEMORY) {
      const int b = regIdx(o.mem.base), x = regIdx(o.mem.index);
      if (b >= 0) s.rd |= 1u << b; if (x >= 0) s.rd |= 1u << x;
      if (expl) {
        s.opReg[i] = 0xfe; s.m.on = true; s.m.opi = (u8)i; s.m.base = o.mem.base == ZYDIS_REGISTER_RIP ? 16 : b >= 0 ? (u8)b : 0xff; s.m.index = x >= 0 ? (u8)x : 0xff; s.m.scale = o.mem.scale; s.m.disp = o.mem.disp.value;
        s.m.seg = o.mem.segment == ZYDIS_REGISTER_GS ? 1 : o.mem.segment == ZYDIS_REGISTER_FS ? 2 : 0; s.m.size = (u8)(o.size / 8);
        s.m.agen = o.mem.type == ZYDIS_MEMOP_TYPE_AGEN; s.m.rd = rdA && !s.m.agen; s.m.wr = wrA && !s.m.agen;
      }
    } else if (expl) { s.opReg[i] = 0xfd; if (o.type == ZYDIS_OPERAND_TYPE_IMMEDIATE) { s.hasImm = true; s.imm = o.imm.is_signed ? o.imm.value.s : (i64)o.imm.value.u; } }
  }
  if (zi.cpu_flags) { s.rdF = flagBits(zi.cpu_flags->tested); s.wrF = flagBits(zi.cpu_flags->modified | zi.cpu_flags->set_0 | zi.cpu_flags->set_1 | zi.cpu_flags->undefined); }
  // x ^ x, x - x: no read of x
  if ((zi.mnemonic == ZYDIS_MNEMONIC_XOR || zi.mnemonic == ZYDIS_MNEMONIC_SUB || zi.mnemonic == ZYDIS_MNEMONIC_PXOR || zi.mnemonic == ZYDIS_MNEMONIC_XORPS) &&
      s.nexp >= 2 && s.opReg[0] < 32 && s.opReg[0] == s.opReg[1] && (s.opReg[0] >= 16 || s.opSize[0] >= 4)) s.rd &= ~(1u << s.opReg[0]);
  switch (zi.meta.category) {
  case ZYDIS_CATEGORY_COND_BR: s.kind = K_JCC; break;
  case ZYDIS_CATEGORY_UNCOND_BR: s.kind = zo[0].type == ZYDIS_OPERAND_TYPE_IMMEDIATE ? K_JMP : K_JMPI; break;
  case ZYDIS_CATEGORY_CALL: s.kind = zo[0].type == ZYDIS_OPERAND_TYPE_IMMEDIATE ? K_CALL : K_CALLI; break;
  case ZYDIS_CATEGORY_RET: s.kind = K_RET; break;
  case ZYDIS_CATEGORY_SYSCALL: case ZYDIS_CATEGORY_INTERRUPT: s.kind = K_TRAP; break;
  default: break;
  }
  if (s.kind == K_JMPI || s.kind == K_CALLI) { if (zo[0].type == ZYDIS_OPERAND_TYPE_REGISTER) s.tgReg = (u8)regIdx(zo[0].reg.value); else s.tgMem = true; }
  switch (zi.mnemonic) {
  case ZYDIS_MNEMONIC_CPUID: case ZYDIS_MNEMONIC_RDTSC: case ZYDIS_MNEMONIC_RDTSCP: case ZYDIS_MNEMONIC_RDRAND: case ZYDIS_MNEMONIC_RDSEED: case ZYDIS_MNEMONIC_XGETBV: case ZYDIS_MNEMONIC_RDPID: case ZYDIS_MNEMONIC_RDPMC:
    s.kind = K_ENV; s.envOut = s.wr & 0xffff; break;
  case ZYDIS_MNEMONIC_UD2: case ZYDIS_MNEMONIC_INT3: case ZYDIS_MNEMONIC_HLT: s.kind = K_TRAP; break;
  default: break;
  }
  if (s.kind == K_CALL || s.kind == K_CALLI) s.rd |= (1u << 1) | (1u << 2) | (1u << 8) | (1u << 9);   // the arguments: rcx, rdx, r8, r9
  if (s.kind == K_RET) s.rd |= 1u << 0;                                                              // rax
  s.rd &= ~(1u << 4); s.wr &= ~(1u << 4); s.wrPart &= ~(1u << 4);                                    // rsp is never a value of the function
  return true;
}
}  // namespace insinfo
