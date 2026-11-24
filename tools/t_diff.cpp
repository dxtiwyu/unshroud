// Differential test of the instruction semantics: every instruction form found in a PE (or a built-in list) runs from
// random states (1) in unshroud with every register, flag, vector register and the memory operand symbolic, (2) in unshroud
// concrete, (3) on this CPU. Concrete results must agree with the CPU (flags the instruction leaves undefined aside), and
// every expression must evaluate to its concrete value.
// usage: t_diff <pe> [--trials N] [--per-shape K] [--only mnemonic] [--verbose]
#include "../src/util.hpp"
#include "../src/pe.hpp"
#include <Zydis/Zydis.h>
#include <cstdio>
#include <cstring>
#include <map>
#include <random>
#include <set>
#include <windows.h>
using namespace unshroud;

namespace unshroud { Stop nativeExec(Engine& E, const Insn& I); }

static const u64 CODE = 0x10000000ull;

struct Case { std::vector<u8> bytes; std::string text; u16 mn; u32 undefinedFlags; bool hasMem; };

static std::string shapeOf(const ZydisDecodedInstruction& zi, const ZydisDecodedOperand* zo) {
  std::string s = ZydisMnemonicGetString(zi.mnemonic);
  for (unsigned i = 0; i < zi.operand_count_visible; i++) {
    const auto& o = zo[i];
    char b[48];
    if (o.type == ZYDIS_OPERAND_TYPE_REGISTER) snprintf(b, sizeof b, " r%d:%u", (int)ZydisRegisterGetClass(o.reg.value), o.size);
    else if (o.type == ZYDIS_OPERAND_TYPE_MEMORY) snprintf(b, sizeof b, " m%u", o.size);
    else snprintf(b, sizeof b, " i%u", o.size);
    s += b;
  }
  if (zi.attributes & (ZYDIS_ATTRIB_HAS_REP | ZYDIS_ATTRIB_HAS_REPE | ZYDIS_ATTRIB_HAS_REPNE)) s += " rep";
  return s;
}

static bool usable(const ZydisDecodedInstruction& zi, const ZydisDecodedOperand* zo) {
  switch (zi.meta.category) {
  case ZYDIS_CATEGORY_COND_BR: case ZYDIS_CATEGORY_UNCOND_BR: case ZYDIS_CATEGORY_CALL: case ZYDIS_CATEGORY_RET: case ZYDIS_CATEGORY_SYSCALL:
  case ZYDIS_CATEGORY_INTERRUPT: case ZYDIS_CATEGORY_SYSRET: case ZYDIS_CATEGORY_SYSTEM: case ZYDIS_CATEGORY_IO: case ZYDIS_CATEGORY_IOSTRINGOP:
  case ZYDIS_CATEGORY_STRINGOP: case ZYDIS_CATEGORY_PUSH: case ZYDIS_CATEGORY_POP: case ZYDIS_CATEGORY_X87_ALU: case ZYDIS_CATEGORY_SEMAPHORE:
  case ZYDIS_CATEGORY_NOP: case ZYDIS_CATEGORY_WIDENOP:
    return false;
  default: break;
  }
  switch (zi.meta.isa_ext) {      // user-mode computation this CPU has (an AMD Zen: no SSE4A guess, no SHA512)
  case ZYDIS_ISA_EXT_BASE: case ZYDIS_ISA_EXT_LONGMODE: case ZYDIS_ISA_EXT_SSE: case ZYDIS_ISA_EXT_SSE2: case ZYDIS_ISA_EXT_SSE3: case ZYDIS_ISA_EXT_SSSE3:
  case ZYDIS_ISA_EXT_SSE4: case ZYDIS_ISA_EXT_AVX: case ZYDIS_ISA_EXT_AVX2: case ZYDIS_ISA_EXT_BMI1: case ZYDIS_ISA_EXT_BMI2: case ZYDIS_ISA_EXT_LZCNT:
  case ZYDIS_ISA_EXT_MOVBE: case ZYDIS_ISA_EXT_ADOX_ADCX: case ZYDIS_ISA_EXT_AES: case ZYDIS_ISA_EXT_PCLMULQDQ: case ZYDIS_ISA_EXT_F16C: case ZYDIS_ISA_EXT_FMA:
    break;
  default: return false;
  }
  if (zi.attributes & ZYDIS_ATTRIB_IS_PRIVILEGED) return false;
  switch (zi.mnemonic) {
  case ZYDIS_MNEMONIC_CPUID: case ZYDIS_MNEMONIC_RDTSC: case ZYDIS_MNEMONIC_RDTSCP: case ZYDIS_MNEMONIC_XGETBV: case ZYDIS_MNEMONIC_RDRAND:
  case ZYDIS_MNEMONIC_RDSEED: case ZYDIS_MNEMONIC_LEAVE: case ZYDIS_MNEMONIC_ENTER: case ZYDIS_MNEMONIC_PUSHFQ: case ZYDIS_MNEMONIC_POPFQ:
  case ZYDIS_MNEMONIC_LDMXCSR: case ZYDIS_MNEMONIC_STMXCSR: case ZYDIS_MNEMONIC_VZEROUPPER: case ZYDIS_MNEMONIC_VZEROALL:
    return false;
  default: break;
  }
  for (unsigned i = 0; i < zi.operand_count; i++) {
    const auto& o = zo[i];
    if (o.type == ZYDIS_OPERAND_TYPE_REGISTER) {
      ZydisRegisterClass c = ZydisRegisterGetClass(o.reg.value);
      if (c == ZYDIS_REGCLASS_SEGMENT || c == ZYDIS_REGCLASS_X87 || c == ZYDIS_REGCLASS_MMX || c == ZYDIS_REGCLASS_ZMM || c == ZYDIS_REGCLASS_MASK) return false;
      if (o.reg.value == ZYDIS_REGISTER_RSP || o.reg.value == ZYDIS_REGISTER_ESP || o.reg.value == ZYDIS_REGISTER_SP || o.reg.value == ZYDIS_REGISTER_SPL) return false;
    }
    if (o.type == ZYDIS_OPERAND_TYPE_MEMORY) {
      if (o.mem.segment == ZYDIS_REGISTER_FS || o.mem.segment == ZYDIS_REGISTER_GS) return false;
      if (o.mem.base == ZYDIS_REGISTER_RSP || o.mem.index == ZYDIS_REGISTER_RSP) return false;
      if (o.visibility != ZYDIS_OPERAND_VISIBILITY_EXPLICIT) return false;
    }
  }
  return true;
}

static std::vector<Case> corpus(const std::string& pe, int perShape, const char* only) {
  Engine E; Image img;
  if (!loadPE(E, pe, img)) { printf("cannot load %s\n", pe.c_str()); exit(1); }
  ZydisDecoder dec; ZydisDecoderInit(&dec, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_STACK_WIDTH_64);
  std::map<std::string, int> shapes; std::vector<Case> out;
  std::vector<std::pair<u64, u64>> ranges = img.funcs;
  if (ranges.empty()) ranges.push_back({0x1000, img.size - 0x1000});
  for (auto [rva, size] : ranges) {
    std::vector<u8> code(size + 16); E.readMem(img.base + rva, code.data(), size + 16);
    for (u64 off = 0; off < size;) {
      ZydisDecodedInstruction zi; ZydisDecodedOperand zo[ZYDIS_MAX_OPERAND_COUNT];
      if (!ZYAN_SUCCESS(ZydisDecoderDecodeFull(&dec, code.data() + off, size + 16 - off, &zi, zo))) { off++; continue; }
      if (usable(zi, zo) && (!only || !strcmp(ZydisMnemonicGetString(zi.mnemonic), only))) {
        std::string sh = shapeOf(zi, zo);
        if (shapes[sh]++ < perShape) {
          Case c; c.bytes.assign(code.begin() + off, code.begin() + off + zi.length); c.mn = (u16)zi.mnemonic; c.text = sh;
          c.undefinedFlags = zi.cpu_flags ? zi.cpu_flags->undefined : 0; c.hasMem = false;
          for (unsigned i = 0; i < zi.operand_count; i++) if (zo[i].type == ZYDIS_OPERAND_TYPE_MEMORY && zo[i].mem.type == ZYDIS_MEMOP_TYPE_MEM) c.hasMem = true;
          out.push_back(c);
        }
      }
      off += zi.length;
    }
  }
  return out;
}

struct World { Engine E; };

static void setState(Engine& E, std::mt19937_64& rng, const u64* g, const u8 (*v)[32], u64 flags) {
  memcpy(E.g, g, sizeof E.g); memset(E.gs, 0, sizeof E.gs);
  memcpy(E.v, v, sizeof E.v); memset(E.vc, 0, sizeof E.vc); E.vsym = 0;
  E.fl = Flags{}; E.fl.bits = flags | 0x202; E.fl.lazy = 0;
  (void)rng;
}

int main(int argc, char** argv) {
  unshroud::limitMemory();
  if (argc < 2) { printf("usage: t_diff <pe> [--trials N] [--per-shape K] [--only mnemonic] [--verbose]\n"); return 1; }
  int trials = 40, perShape = 2; const char* only = nullptr; bool verbose = false;
  for (int i = 2; i < argc; i++) {
    if (!strcmp(argv[i], "--trials")) trials = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--per-shape")) perShape = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--only")) only = argv[++i];
    else if (!strcmp(argv[i], "--verbose")) verbose = true;
  }
  std::vector<Case> cases = corpus(argv[1], perShape, only);
  printf("%zu instruction forms\n", cases.size());
  std::mt19937_64 rng(12345);
  std::map<std::string, int> failCon, failSym; int nativeSkip = 0, tested = 0, faults = 0;
  // TD_UNDEF=1: the flags an instruction leaves undefined are compared too (the model against this CPU), by mnemonic
  const bool undefMode = getenv("TD_UNDEF") != nullptr;
  struct UStat { u32 undef = 0, differ = 0; int trials = 0, bad = 0; }; std::map<std::string, UStat> ustat;
  for (const Case& c : cases) {
    bool reportedCon = false, reportedSym = false;
    if (getenv("TD_TRACE")) { printf("case %s\n", c.text.c_str()); fflush(stdout); }
    for (int t = 0; t < trials; t++) {
      u64 g[16]; alignas(32) u8 v[16][32];
      const u64 special[] = {0, 1, 2, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0xffff, 0x7fffffff, 0x80000000, 0xffffffff, 0x8000000000000000ull, ~0ull, 63, 64};
      for (int r = 0; r < 16; r++) g[r] = (rng() % 4 == 0) ? special[rng() % 16] : (rng() % 3 == 0 ? rng() & 0xff : rng());
      for (int r = 0; r < 16; r++) for (int b = 0; b < 32; b += 8) { u64 x = (rng() % 5 == 0) ? special[rng() % 16] : rng(); memcpy(v[r] + b, &x, 8); }
      g[RSP] = 0x7f0000000000ull;
      u64 flags = rng() & (FL_CF | FL_PF | FL_AF | FL_ZF | FL_SF | FL_OF);
      Engine A, B, N;          // symbolic, concrete, native
      u8 mem[64]; for (auto& b : mem) b = (u8)rng();
      u64 maddr = 0;
      for (Engine* e : {&A, &B, &N}) {
        e->map(CODE, 4096); e->writeMem(CODE, c.bytes.data(), c.bytes.size());
        u8 pad[16]; memset(pad, 0xcc, 16); e->writeMem(CODE + c.bytes.size(), pad, 16);
        setState(*e, rng, g, v, flags);
        e->rip = CODE;
      }
      const Insn* I = B.decodeAt(CODE);
      if (!I) break;
      Insn ins = *I;
      for (unsigned i = 0; i < ins.nops; i++) if (ins.op[i].type == OT_MEM) {
        const Opnd& o = ins.op[i];
        u64 a = (u64)o.disp + (o.base == 16 ? ins.next : 0);
        if (o.base != 0xff && o.base != 16) a += g[o.base];
        if (o.index != 0xff) a += g[o.index] * o.scale;
        if (ins.asz == 4) a &= 0xffffffffull;
        maddr = a;
      }
      if (maddr) for (Engine* e : {&A, &B, &N}) e->writeMem(maddr, mem, 64);
      // symbolic copy: every input is a variable
      for (int r = 0; r < 16; r++) if (r != RSP) A.symbolizeReg(r, "g" + std::to_string(r));
      for (int r = 0; r < 16; r++) A.symbolizeVec(r, "v" + std::to_string(r));
      A.symbolizeFlags("f");
      if (maddr) for (int k = 0; k < 64; k += 8) A.symbolizeMem(maddr + k, 8, "m" + std::to_string(k));
      static const bool lazyMode = getenv("UNSHROUD_LAZY") != nullptr;   // the symbolic copy records its operations, then builds them all
      A.lazy = lazyMode;
      Stop sa = A.run(1), sb = B.run(1);
      A.settle();
      if (sa == ST_COUNT) sa = ST_NONE;
      if (sb == ST_COUNT) sb = ST_NONE;
      if (sb != ST_NONE) { faults++; if (sa != sb && !reportedSym) { reportedSym = true; failSym[c.text]++; printf("STOP %s: sym %d con %d\n", c.text.c_str(), (int)sa, (int)sb); } continue; }
      Stop sn = nativeExec(N, ins);
      if (sn == ST_NONE) N.rip = ins.next;
      tested++;
      // concrete against the CPU
      const u32 arith = FL_CF | FL_PF | FL_AF | FL_ZF | FL_SF | FL_OF;
      u64 fb = B.rflags() & arith & ~c.undefinedFlags, fnat = N.rflags() & arith & ~c.undefinedFlags;
      std::string diff;
      char buf[256];
      if (sn == ST_NONE && undefMode && c.undefinedFlags) {
        const u64 ub = B.rflags() & arith & c.undefinedFlags, un = N.rflags() & arith & c.undefinedFlags;
        UStat& u = ustat[ZydisMnemonicGetString((ZydisMnemonic)c.mn)];
        u.undef |= c.undefinedFlags & arith; u.differ |= (u32)(ub ^ un); u.trials++; if (ub != un) u.bad++;
      }
      if (sn != ST_NONE) nativeSkip++;
      else {
        for (int r = 0; r < 16; r++) if (B.g[r] != N.g[r]) { snprintf(buf, sizeof buf, " g%d %llx/%llx", r, (unsigned long long)B.g[r], (unsigned long long)N.g[r]); diff += buf; }
        if (fb != fnat) { snprintf(buf, sizeof buf, " flags %llx/%llx", (unsigned long long)fb, (unsigned long long)fnat); diff += buf; }
        for (int r = 0; r < 16; r++) if (memcmp(B.v[r], N.v[r], 32)) { u64 x0, x1, y0, y1; memcpy(&x0, B.v[r], 8); memcpy(&x1, B.v[r] + 8, 8); memcpy(&y0, N.v[r], 8); memcpy(&y1, N.v[r] + 8, 8);
          snprintf(buf, sizeof buf, " v%d %llx:%llx/%llx:%llx", r, (unsigned long long)x1, (unsigned long long)x0, (unsigned long long)y1, (unsigned long long)y0); diff += buf; }
        if (maddr) { u8 mb[64], mn[64]; B.readMem(maddr, mb, 64); N.readMem(maddr, mn, 64); if (memcmp(mb, mn, 64)) diff += " memory"; }
        if (!diff.empty()) {
          failCon[c.text]++;
          if (!reportedCon || verbose) {
            reportedCon = true;
            std::string hexs; for (u8 b : c.bytes) { snprintf(buf, sizeof buf, "%02x", b); hexs += buf; }
            printf("CON %-34s %-36s %s\n", c.text.c_str(), B.disasm(CODE).c_str(), diff.c_str());
          }
        }
      }
      // symbolic against concrete: same concrete state, and every expression evaluates to its value
      std::string sd;
      for (int r = 0; r < 16; r++) {
        if (A.g[r] != B.g[r]) { snprintf(buf, sizeof buf, " g%d %llx/%llx", r, (unsigned long long)A.g[r], (unsigned long long)B.g[r]); sd += buf; }
        else if (A.gs[r] && A.X.evalSeed(A.gs[r]) != A.g[r]) { snprintf(buf, sizeof buf, " g%d-expr %llx", r, (unsigned long long)A.X.evalSeed(A.gs[r])); sd += buf; }
      }
      for (u32 bit : {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF}) {
        if (c.undefinedFlags & bit) continue;
        Val fa = A.flag(bit), fc = B.flag(bit);
        if (fa.c != fc.c) { snprintf(buf, sizeof buf, " flag%x %llu/%llu", bit, (unsigned long long)fa.c, (unsigned long long)fc.c); sd += buf; }
        else if (fa.s && (A.X.evalSeed(fa.s) & 1) != fa.c) { snprintf(buf, sizeof buf, " flag%x-expr", bit); sd += buf; }
      }
      for (int r = 0; r < 16; r++) {
        if (memcmp(A.v[r], B.v[r], 32)) { snprintf(buf, sizeof buf, " v%d", r); sd += buf; continue; }
        for (int q = 0; q < 32; q += 8) {
          u32 any = 0; for (int i = 0; i < 8; i++) any |= A.vc[r][q + i].e;
          if (!any) continue;
          u64 want; memcpy(&want, A.v[r] + q, 8);
          if (A.X.evalSeed(cellsExpr(A.X, A.v[r] + q, A.vc[r] + q, 8)) != want) { snprintf(buf, sizeof buf, " v%d.%d-expr", r, q / 8); sd += buf; }
        }
      }
      if (maddr) for (int k = 0; k < 64; k += 8) {
        Val ma = A.load(maddr + k, 8), mc = B.load(maddr + k, 8);
        if (ma.c != mc.c) { sd += " memory"; break; }
        if (ma.s && A.X.evalSeed(ma.s) != ma.c) { sd += " memory-expr"; break; }
      }
      for (const auto& pc : A.path) if (!(A.X.evalSeed(pc.cond) & 1)) { sd += " path-constraint-false"; break; }
      if (!sd.empty()) {
        failSym[c.text]++;
        if (!reportedSym || verbose) { reportedSym = true; printf("SYM %-34s %-36s %s\n", c.text.c_str(), B.disasm(CODE).c_str(), sd.c_str()); }
      }
    }
  }
  if (undefMode) {
    auto fl = [](u32 m) { std::string s; const char* n[12] = {"CF", "", "PF", "", "AF", "", "ZF", "SF", "", "", "", "OF"}; for (int i = 0; i < 12; i++) if (m & (1u << i)) { s += n[i]; s += ' '; } return s; };
    for (auto& kv : ustat) printf("UNDEF %-12s undefined: %-18s model differs from the CPU: %-18s (%d of %d trials)%c", kv.first.c_str(), fl(kv.second.undef).c_str(), fl(kv.second.differ).c_str(), kv.second.bad, kv.second.trials, 10);
  }
  printf("\n%d trials of %zu forms (%d stopped in unshroud, %d not run natively): %zu forms differ from the CPU, %zu forms with symbolic inconsistencies\n",
         tested, cases.size(), faults, nativeSkip, failCon.size(), failSym.size());
  return 0;
}
