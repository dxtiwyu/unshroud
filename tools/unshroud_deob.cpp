// unshroud_deob: replays function invocations recorded in Tenet traces (segments made by unshroud_tseg) on the engine, the
// trace correcting it at every step, and writes what each instruction of the function is once the obfuscation is
// taken away: constants, resolved targets, conditions, the statements which are left, text.
//   unshroud_deob <pe> <module base in the trace, hex> <out.jsonl> segment...      (segments of one function)
//   unshroud_deob <pe> <module base in the trace, hex> --assume <out dir> <function rva | @list>...
// Pass 1 over every unit: values with / without expressions, the static def-use graph, what is live. Then the values
// to name (those more than one statement needs). Pass 2: the same replay, named values cut into variables, the
// statements printed. Rows of the output (JSON lines): one per instruction ("as": 1 = not executed in the trace,
// walked by a free run: assumed), {"made": text the function stored}, {"asum": free-run counters}, {"summary"}.
// Environment: UNSHROUD_DEOB_PASS2=0 pass 1 only; UNSHROUD_DEOB_MAXLINES=N lines of a unit at most; UNSHROUD_DEOB_NODES=N
// expression nodes before the engine is renewed; UNSHROUD_DEOB_PROF=1 timing; UNSHROUD_DEOB_DEBUG=1 first mismatches;
// UNSHROUD_DEOB_ASSUME=1 free runs from the recorded states into code the run did not execute (UNSHROUD_DEOB_ABUDGET=steps
// per starting point, default 20000; UNSHROUD_DEOB_DEAD=file of "rva side kind" lines: sides proved dead, never walked).
// --assume: functions the run never entered, walked from their first instruction with unknown registers.
#include "../src/util.hpp"
#include "../src/engine.hpp"
#include "../src/mba.hpp"
#include "../src/solver.hpp"
#include <Zydis/Zydis.h>
#include "unshroud_insinfo.hpp"
#include <windows.h>
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <deque>
#include <map>
#include <string>
#include <unordered_map>
#include <vector>
using namespace unshroud;

struct Sec { u32 rva, size; bool w; };
static u64 TB = 0, ISIZE = 0; static std::vector<Sec> g_secs; static std::vector<u8> g_img; static std::vector<std::pair<u32, u32>> g_funcs;
static ZydisDecoder g_dec;
static bool inImg(u64 a) { return a >= TB && a < TB + ISIZE; }
static bool roAddr(u64 a) {                       // a byte of the image nobody writes (code, read-only data, headers)
  if (!inImg(a)) return false; const u32 r = (u32)(a - TB);
  for (auto& s : g_secs) if (r >= s.rva && r < s.rva + s.size) return !s.w;
  return true;
}
// the image mapped at the base it had in the recorded process, relocations applied
static bool mapImage(Engine& E, const char* path) {
  FILE* f = fopen(path, "rb"); if (!f) return false;
  fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
  std::vector<u8> d((size_t)sz); if (fread(d.data(), 1, d.size(), f) != d.size()) { fclose(f); return false; } fclose(f);
  auto* dos = (IMAGE_DOS_HEADER*)d.data(); auto* nt = (IMAGE_NT_HEADERS64*)(d.data() + dos->e_lfanew);
  ISIZE = nt->OptionalHeader.SizeOfImage; g_img.assign((size_t)ISIZE, 0);
  memcpy(g_img.data(), d.data(), std::min<size_t>(nt->OptionalHeader.SizeOfHeaders, d.size()));
  auto* sec = IMAGE_FIRST_SECTION(nt);
  for (unsigned i = 0; i < nt->FileHeader.NumberOfSections; i++) {
    size_t raw = std::min<size_t>(sec[i].SizeOfRawData, sec[i].Misc.VirtualSize ? sec[i].Misc.VirtualSize : sec[i].SizeOfRawData);
    if (sec[i].PointerToRawData + raw > d.size()) raw = d.size() > sec[i].PointerToRawData ? d.size() - sec[i].PointerToRawData : 0;
    if (raw && sec[i].VirtualAddress + raw <= ISIZE) memcpy(g_img.data() + sec[i].VirtualAddress, d.data() + sec[i].PointerToRawData, raw);
    g_secs.push_back({sec[i].VirtualAddress, std::max(sec[i].Misc.VirtualSize, sec[i].SizeOfRawData), (sec[i].Characteristics & IMAGE_SCN_MEM_WRITE) != 0});
  }
  const u64 delta = TB - nt->OptionalHeader.ImageBase;
  auto& rd = nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC];
  for (u32 o = 0; delta && rd.VirtualAddress && o + 8 <= rd.Size;) {
    auto* b = (IMAGE_BASE_RELOCATION*)(g_img.data() + rd.VirtualAddress + o); if (!b->SizeOfBlock) break;
    const u16* e = (const u16*)(b + 1);
    for (u32 k = 0; k < (b->SizeOfBlock - 8) / 2; k++) if ((e[k] >> 12) == 10) { u64 v; u8* p = g_img.data() + b->VirtualAddress + (e[k] & 0xfff); memcpy(&v, p, 8); v += delta; memcpy(p, &v, 8); }
    o += b->SizeOfBlock;
  }
  auto& ed = nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXCEPTION];
  if (ed.VirtualAddress) { auto* rf = (RUNTIME_FUNCTION*)(g_img.data() + ed.VirtualAddress); for (u32 i = 0; i < ed.Size / sizeof(RUNTIME_FUNCTION); i++) g_funcs.push_back({rf[i].BeginAddress, rf[i].EndAddress}); }
  E.map(TB, ISIZE); E.writeMem(TB, g_img.data(), g_img.size());
  ZydisDecoderInit(&g_dec, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_STACK_WIDTH_64);
  return true;
}

// ---- what an instruction is, statically (unshroud_insinfo.hpp), and what the replay found out about it
using insinfo::InsInfo; using insinfo::MemOp;
using insinfo::K_OTHER; using insinfo::K_JCC; using insinfo::K_JMP; using insinfo::K_JMPI; using insinfo::K_CALL; using insinfo::K_CALLI; using insinfo::K_RET; using insinfo::K_ENV; using insinfo::K_TRAP;
enum : u8 { ST_UNSET = 0, ST_CONST, ST_VARY, ST_SYM };            // a value over the visits: one constant, several, depends on inputs
struct Fact { u8 st = ST_UNSET; u64 lo = 0, hi = 0;
  void see(bool sym, u64 l, u64 h = 0) { if (sym) st = ST_SYM; else if (st == ST_UNSET) { st = ST_CONST; lo = l; hi = h; } else if (st == ST_CONST && (lo != l || hi != h)) st = ST_VARY; } };
struct CmpSample { u64 a = 0, b = 0; u8 sym = 0, u1 = 0, u2 = 0; u32 call = 0; std::string s1, s2; };   // a compare and the text read just before it
struct SI : InsInfo {
  bool join = false, mrVar = false, named = false, live = false, feeds = false, sawSym = false, tgBool = false, tgProved = false;
  u8 npred = 0, root = 0;
  u32 visits = 0, uvisits = 0, pred[2] = {0, 0}; u16 regVar = 0, xVar = 0; u64 regFirst[16], xFirst[16], mrFirst = 0;
  Fact in[4], out;                                    // the explicit operands read (before), the destination (after)
  u32 taken = 0, fall = 0, symCond = 0, folded = 0; std::string cond, tgExpr, tgCond; std::vector<std::pair<u64, u32>> targets;
  Fact arg[4], rv; std::vector<std::string> notes; std::vector<std::string> stmt; u32 stmtAlt = 0;
  std::vector<u32> deps; u32 qTry = 0, qHit = 0, inputs = 0, ext = 0, mism = 0, stmtN = 0;
  std::vector<std::string> rds; std::vector<u8> rdsS; u32 rdN = 0;          // text read here one character at a time (hash, compare, copy loops)
  std::vector<CmpSample> cmpS; u32 cmpEq = 0, cmpNe = 0;
  std::vector<std::pair<std::string, u64>> tgState; std::string tgStateVar; std::vector<u64> tgLeaves;   // a computed jump which depends on one stored value: value -> target, as seen
};
struct Tab { std::vector<u32> idx; std::deque<SI> si; std::vector<u32> rva; };
static Tab g_real, g_asmTab; static Tab* g_tab = &g_real;      // g_asmTab: code the run did not execute (free runs)
#define g_sidx (g_tab->idx)
#define g_si (g_tab->si)
#define g_siRva (g_tab->rva)
static SI& siAt(u32 rva) {
  u32& ix = g_sidx[rva];
  if (!ix) { g_si.emplace_back(); g_siRva.push_back(rva); ix = (u32)g_si.size(); }
  SI& s = g_si[ix - 1];
  if (!s.decoded) insinfo::decodeIns(g_dec, g_img.data() + rva, g_img.size() - rva, s);
  return s;
}
// ---- the segment reader: lines with the registers accumulated
struct Acc { u64 addr; u32 len; const char* hex; };
static inline int hx(char c) { return c <= '9' ? c - '0' : (c | 32) - 'a' + 10; }
static inline u64 hexv(const char*& p, const char* e) { u64 v = 0; while (p < e) { char c = *p; int d; if (c >= '0' && c <= '9') d = c - '0'; else if (c >= 'a' && c <= 'f') d = c - 'a' + 10; else if (c >= 'A' && c <= 'F') d = c - 'A' + 10; else break; v = v * 16 + d; p++; } return v; }
struct Reader {
  FILE* f = nullptr; std::vector<char> buf; size_t pos = 0, end = 0; u64 base = 0; bool eof = false;
  u64 G[16] = {}; u8 X[16][16] = {}; u64 rip = 0; std::vector<Acc> mr, mw;
  std::deque<std::string> syn;                       // (free runs: the bytes of made-up accesses)
  int kind = 0; std::string text; u64 gapN = 0; std::vector<std::pair<u64, u64>> gapRd; bool gapAll = false;   // kind: 0 line, 1 #seg, 2 #gap, 3 #end
  bool open(const char* p) { f = fopen(p, "rb"); buf.resize((size_t)8 << 20); pos = end = 0; base = 0; eof = false; return f != nullptr; }
  void close() { if (f) fclose(f); f = nullptr; }
  u64 tell() const { return base + pos; }
  void seek(u64 off) { _fseeki64(f, (long long)off, SEEK_SET); base = off; pos = end = 0; eof = false; }
  static void accs(const char* a, const char* ae, std::vector<Acc>& out) {
    while (a < ae) {
      const char* semi = (const char*)memchr(a, ';', (size_t)(ae - a)); if (!semi) semi = ae;
      const char* colon = (const char*)memchr(a, ':', (size_t)(semi - a));
      if (colon) { const char* q = a + 2; const u64 addr = hexv(q, colon); out.push_back({addr, (u32)((semi - colon - 1) / 2), colon + 1}); }
      a = semi + 1;
    }
  }
  bool next() {
    for (;;) {
      char* nl = pos < end ? (char*)memchr(buf.data() + pos, 10, end - pos) : nullptr;
      if (!nl) {
        if (eof) return false;
        memmove(buf.data(), buf.data() + pos, end - pos); base += pos; end -= pos; pos = 0;
        if (end == buf.size()) buf.resize(buf.size() * 2);
        const size_t n = fread(buf.data() + end, 1, buf.size() - end, f); end += n;
        if (!n) { eof = true; if (pos == end) return false; if (end == buf.size()) buf.resize(end + 1); buf[end++] = (char)10; }
        continue;
      }
      const char* s = buf.data() + pos; const char* e = nl; pos = (size_t)(nl - buf.data()) + 1;
      if (e > s && e[-1] == 13) e--;
      if (s == e) continue;
      if (*s == '#') {
        text.assign(s, e); kind = text.compare(0, 4, "#seg") == 0 ? 1 : text.compare(0, 4, "#gap") == 0 ? 2 : text.compare(0, 4, "#con") == 0 ? 4 : 3;
        if (kind == 2) {
          gapRd.clear(); gapAll = false; gapN = strtoull(text.c_str() + 7, nullptr, 10);
          size_t r = text.find("rd="); if (r != std::string::npos) { const char* p = text.c_str() + r + 3; const char* pe = text.c_str() + text.size();
            if (p < pe && *p == '*') gapAll = true;
            else while (p < pe) { const u64 a = hexv(p, pe); if (p >= pe || *p != ':') break; p++; const u64 l = hexv(p, pe); gapRd.push_back({a, l}); if (p < pe && *p == ';') p++; } }
        }
        if (kind == 4) { gapRd.clear(); const char* p = text.c_str() + 7; const char* pe = text.c_str() + text.size(); while (p < pe) { const u64 a = hexv(p, pe); if (p >= pe || *p != ':') break; p++; const u64 l = hexv(p, pe); gapRd.push_back({a, l}); if (p < pe && *p == ';') p++; } }
        return true;
      }
      kind = 0; mr.clear(); mw.clear();
      const char* p = s;
      while (p < e) {
        const char* eq = (const char*)memchr(p, '=', (size_t)(e - p)); if (!eq) break;
        const char* ce = (const char*)memchr(eq, ',', (size_t)(e - eq)); if (!ce) ce = e;
        const size_t ln = (size_t)(eq - p);
        if (p[0] == 'r') {
          const char* q = eq + 3;
          if (ln == 3 && p[1] == 'i') rip = hexv(q, ce);
          else { int gi = -1;
            if (ln == 3) { switch (p[1]) { case 'a': gi = 0; break; case 'c': gi = 1; break; case 'b': gi = p[2] == 'x' ? 3 : 5; break; case 's': gi = p[2] == 'p' ? 4 : 6; break; case 'd': gi = p[2] == 'x' ? 2 : 7; break; case '1': gi = 10 + (p[2] - '0'); break; default: break; } }
            else if (ln == 2) gi = p[1] - '0';
            if (gi >= 0 && gi < 16) G[gi] = hexv(q, ce); }
        } else if (p[0] == 'x') {
          const int xi = atoi(p + 3) & 15; u8* d = X[xi]; memset(d, 0, 16);
          const char* h = ce; int k = 0;
          while (h - 2 >= eq + 3 && k < 16) { h -= 2; d[k++] = (u8)(hx(h[0]) * 16 + hx(h[1])); }
        } else if (p[0] == 'm' && ln == 2) { if (p[1] == 'r') accs(eq + 1, ce, mr); else if (p[1] == 'w') accs(eq + 1, ce, mw); }
        p = ce + 1;
      }
      return true;
    }
  }
};
static inline void hexBytes(const Acc& a, u8* out) { for (u32 i = 0; i < a.len; i++) out[i] = (u8)(hx(a.hex[2 * i]) * 16 + hx(a.hex[2 * i + 1])); }

// ---- what the replay knows about memory, byte by byte
enum : u8 { SH_KNOWN = 1, SH_PEND = 2, SH_CIN = 4 };   // SH_CIN: a constant of the path so far (frag units: unshroud_tseg), until read or written          // seen by the replay; to be made a variable when read (after a transplant)
struct ShPage { u8 st[4096]; u32 def[4096]; u32 ep[4096]; };
struct Shadow {
  std::unordered_map<u64, ShPage*> pages; u64 lastPn = ~0ull; ShPage* last = nullptr; Shadow* base = nullptr;
  ShPage* page(u64 a, bool make) {
    const u64 pn = a >> 12; if (pn == lastPn) return last;
    auto it = pages.find(pn); ShPage* p = it == pages.end() ? nullptr : it->second;
    if (!p && base) { ShPage* b = base->page(a, false); if (b) { p = new ShPage(*b); pages[pn] = p; } }
    if (!p && make) { p = new ShPage; memset(p, 0, sizeof *p); pages[pn] = p; }
    if (p) { lastPn = pn; last = p; }
    return p;
  }
  void clear() { for (auto& kv : pages) delete kv.second; pages.clear(); lastPn = ~0ull; last = nullptr; }
};
// ---- variables: what each input of the replay stands for
enum : u8 { V_ENTRY = 1, V_LOAD, V_EXT, V_RET, V_CLOB, V_PHI, V_LCUT, V_ENV, V_NAMED, V_FIX, V_CARRY };
struct VarMeta { u8 kind = 0, size = 8, reg = 0, part = 0, depth = 1, alias = 0; u32 rva = 0, addrExpr = 0; u64 addr = 0; };
static const char* RN[32] = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
  "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15"};
struct Rp {
  Engine* E = nullptr; Solver* S = nullptr; Mba* M = nullptr; std::shared_ptr<State> pristine;
  Shadow sh; std::vector<VarMeta> vm; std::string aliasStmt;
  u8 pend[32] = {}; u32 pendRva[32] = {};           // registers to be made variables when read: kind, place
  u32 pendExpr[16] = {}, pendExprX[16][2] = {}; std::unordered_map<u32, u32> namedExpr; std::vector<u32> varNode;   // what a named value stands for (variable index -> expression); variable index -> node
  struct RdRun { u64 end = 0, last = 0; u8 unit = 0; bool z = false, sym = false; u32 site = 0; std::string bytes; } runs[4];   // loads of 1 / 2 bytes which follow each other
  std::vector<u64> dirty;                           // where text was stored since the last look (scanMade)
  bool strong = false, strongBool = false, strongProved = false;   // quick(): cases proved by the solver; a byte taken as a truth value
  u32 lastDef[32] = {}, lastDefF[7] = {};           // static producer of each register / flag (0: none; 0x80000000 | n: join n)
  u64 entryRsp = 0, frameLo = 0; u32 callEpoch = 1; bool frag = false; int pass = 1;
  u64 nIns = 0, nSym = 0, nInputs = 0, nExt = 0, nRoPatch = 0, nMism = 0, nMw = 0, nMwBad = 0, nTransplant = 0, nUnsup = 0, nFlagMism = 0, nVars = 0, nChecks = 0, nCheckBad = 0, nFolded = 0;
  std::map<std::string, u64> mismBy;
  double tSimp = 0;
  u32 newVar(unsigned w, u64 seed, const VarMeta& m) { const u32 e = E->X.var("", w, seed); const u32 ix = (u32)E->X.N(e).k; if (vm.size() <= ix) { vm.resize(ix + 1); varNode.resize(ix + 1, 0); } vm[ix] = m; varNode[ix] = e; nVars++; return e; }
  bool symE(u32 e) const { return e && !E->X.isC(e); }
  // a register about to be read: its pending variable is made now
  void need(int r) {
    if (!pend[r]) return;
    VarMeta m; m.kind = pend[r]; m.reg = (u8)r; m.rva = pendRva[r]; pend[r] = 0; if (m.kind == V_CARRY) m.size = 0;
    if (r < 16) { E->gs[r] = newVar(64, E->g[r], m); if (m.kind == V_NAMED && pendExpr[r]) namedExpr[(u32)E->X.N(E->gs[r]).k] = pendExpr[r]; pendExpr[r] = 0; }
    else { const int x = r - 16; for (int q = 0; q < 2; q++) { u64 c; memcpy(&c, E->v[x] + 8 * q, 8); m.part = (u8)q; const u32 e = newVar(64, c, m); for (int i = 0; i < 8; i++) E->vc[x][8 * q + i] = Cell{e, (u32)i}; if (m.kind == V_NAMED && pendExprX[x][q]) namedExpr[(u32)E->X.N(e).k] = pendExprX[x][q]; pendExprX[x][q] = 0; } E->vsym |= 1u << x; }
  }
  void setPend(int r, u8 kind, u32 rva) {
    pend[r] = kind; pendRva[r] = rva;
    if (r < 16) { pendExpr[r] = kind == V_NAMED ? E->gs[r] : 0; E->gs[r] = 0; }
    else if (kind == V_NAMED && (E->vsym & (1u << (r - 16)))) { const int x = r - 16; for (int q = 0; q < 2; q++) { const u32 e = cellsExpr(E->X, E->v[x] + 8 * q, E->vc[x] + 8 * q, 8); pendExprX[x][q] = e && !E->X.isC(e) ? e : 0; } for (int i = 0; i < 32; i++) E->vc[x][i] = Cell{0, 0}; E->vsym &= ~(1u << x); }
    else { const int x = r - 16; for (int i = 0; i < 32; i++) E->vc[x][i] = Cell{0, 0}; E->vsym &= ~(1u << x); }
  }
  bool regSym(int r) {
    need(r);
    if (r < 16) return symE(E->gs[r]);
    const int x = r - 16; if (!(E->vsym & (1u << x))) return false;
    for (int i = 0; i < 16; i++) if (symE(E->vc[x][i].e)) return true;
    return false;
  }
  // ---- printing
  std::string addrName(u64 a) const {
    char b[48];
    if (inImg(a)) snprintf(b, sizeof b, "g_%llx", (unsigned long long)(a - TB));
    else if (entryRsp && a >= frameLo && a < entryRsp) snprintf(b, sizeof b, "var_%llx", (unsigned long long)(entryRsp - a));
    else if (E->gsbase && a >= E->gsbase && a < E->gsbase + 0x2000) snprintf(b, sizeof b, "teb+0x%llx", (unsigned long long)(a - E->gsbase));
    else if (entryRsp && a >= entryRsp && a < entryRsp + 0x100) snprintf(b, sizeof b, "arg_%llx", (unsigned long long)(a - entryRsp));
    else snprintf(b, sizeof b, "0x%llx", (unsigned long long)a);
    return b;
  }
  std::string varName(u32 ix, int depth) {
    if (ix >= vm.size() || !vm[ix].kind) return "v" + std::to_string(ix);
    const VarMeta& m = vm[ix]; char b[64];
    const char* part = m.reg >= 16 ? (m.part ? ".hi" : ".lo") : "";
    if (m.kind == V_CARRY && !m.size) return std::string(RN[m.reg]) + part + "~";
    switch (m.kind) {
    case V_ENTRY: return std::string(RN[m.reg]) + part;
    case V_LOAD: case V_EXT: case V_LCUT: case V_CARRY: {
      static const char* sz[9] = {"?", "b", "w", "?", "d", "?", "?", "?", "q"};
      if (m.alias) { if (m.part) snprintf(b, sizeof b, "m%x_%x", m.rva, m.part); else snprintf(b, sizeof b, "m%x", m.rva); return b; }
      const std::string a = m.addrExpr && depth > 0 ? pr(m.addrExpr, depth - 1) : addrName(m.addr);
      return std::string(sz[m.size <= 8 ? m.size : 0]) + "[" + a + "]" + (m.kind == V_EXT ? "'" : ""); }
    case V_RET: snprintf(b, sizeof b, "ret_%x", m.rva); return b;
    case V_CLOB: snprintf(b, sizeof b, "%s%s_after_%x", RN[m.reg], part, m.rva); return b;
    case V_PHI: snprintf(b, sizeof b, "%s%s.%x", RN[m.reg], part, m.rva); return b;
    case V_NAMED: snprintf(b, sizeof b, "%s%s@%x", RN[m.reg], part, m.rva); return b;
    case V_ENV: snprintf(b, sizeof b, "env_%s@%x", RN[m.reg], m.rva); return b;
    default: snprintf(b, sizeof b, "%s%s?%x", RN[m.reg], part, m.rva); return b;
    }
  }
  std::string cstr(u64 k, unsigned w) const {
    char b[40];
    if (w == 1) return k ? "true" : "false";
    if (w == 64 && inImg(k)) { snprintf(b, sizeof b, "base+0x%llx", (unsigned long long)(k - TB)); return b; }
    const u64 m = maskOf(w);
    if (k > (m >> 1) && ((0 - k) & m) < 0x10000) { snprintf(b, sizeof b, "-0x%llx", (unsigned long long)((0 - k) & m)); return b; }
    snprintf(b, sizeof b, k < 10 ? "%llu" : "0x%llx", (unsigned long long)k); return b;
  }
  std::string pr(u32 id, int depth = 14) {
    if (!id) return "?";
    const Node& x = E->X.N(id);
    if (x.op == O_CONST) return cstr(x.k, x.w);
    if (x.op == O_VAR) return varName((u32)x.k, depth);
    if (depth <= 0) return "...";
    auto s = [&](u32 c) { return pr(c, depth - 1); };
    auto bin = [&](const char* o) { return "(" + s(x.a) + " " + o + " " + s(x.b) + ")"; };
    char buf[32];
    switch (x.op) {
    case O_ADD: if (E->X.N(x.b).op == O_NEG) return "(" + s(x.a) + " - " + s(E->X.N(x.b).a) + ")";
      if (E->X.N(x.b).op == O_CONST) { const u64 k = E->X.N(x.b).k, m = maskOf(x.w); if (!(x.w == 64 && inImg(k)) && k > (m >> 1)) return "(" + s(x.a) + " - " + cstr((0 - k) & m, x.w) + ")"; }
      return bin("+");
    case O_MUL: return bin("*"); case O_UDIV: return bin("/u"); case O_UREM: return bin("%u"); case O_SDIV: return bin("/s"); case O_SREM: return bin("%s");
    case O_MULHU: return "mulhu(" + s(x.a) + ", " + s(x.b) + ")"; case O_MULHS: return "mulhs(" + s(x.a) + ", " + s(x.b) + ")";
    case O_NEG: return "-" + s(x.a);
    case O_AND: return bin(x.w == 1 ? "&&" : "&"); case O_OR: return bin(x.w == 1 ? "||" : "|"); case O_XOR: return bin("^");
    case O_NOT: return (x.w == 1 ? "!" : "~") + s(x.a);
    case O_SHL: return bin("<<"); case O_LSHR: return bin(">>"); case O_ASHR: return bin(">>s");
    case O_ROL: return "rol(" + s(x.a) + ", " + s(x.b) + ")"; case O_ROR: return "ror(" + s(x.a) + ", " + s(x.b) + ")";
    case O_EXTRACT: if (x.lo == 0) { snprintf(buf, sizeof buf, "(u%u)", x.w); return buf + s(x.a); } snprintf(buf, sizeof buf, "[%u:%u]", x.lo + x.w - 1, x.lo); return s(x.a) + buf;
    case O_ZEXT: return "zx(" + s(x.a) + ")"; case O_SEXT: return "sx(" + s(x.a) + ")";
    case O_CONCAT: return "{" + s(x.a) + ", " + s(x.b) + "}";
    case O_ITE: return "(" + s(x.a) + " ? " + s(x.b) + " : " + s(x.c) + ")";
    case O_EQ: return bin("=="); case O_ULT: return bin("<u"); case O_ULE: return bin("<=u"); case O_SLT: return bin("<s"); case O_SLE: return bin("<=s");
    case O_POPCNT: return "popcnt(" + s(x.a) + ")"; case O_CLZ: return "clz(" + s(x.a) + ")"; case O_CTZ: return "ctz(" + s(x.a) + ")";
    default: return "?";
    }
  }
  // an expression as it is printed: simplified, and checked against the recorded value
  std::string show(u32 e, u64 concrete, unsigned w, double budget = 0.15);
  std::unordered_map<u32, u32> qmemo; u64 nSplit = 0;
  u32 quick(u32 e);
  bool trySplit(u32 e, const std::vector<u32>& atoms, u32 bvar, u32& r);
  bool provedConst(u32 e, u64& c);
  u32 expandNamed(u32 e, int depth = 3);
  u32 retCall(u32 e) const { if (!e) return 0; for (int k = 0; k < 4; k++) { const Node& x = E->X.N(e); if (x.op == O_VAR) { const u32 ix = (u32)x.k; return ix < vm.size() && vm[ix].kind == V_RET ? vm[ix].rva : 0; } if ((x.op == O_EXTRACT && x.lo == 0) || x.op == O_ZEXT || x.op == O_SEXT) e = x.a; else break; } return 0; }
  bool isSel(u32 e, int depth = 5) { if (!e) return false; const Node& x = E->X.N(e); if (x.op == O_CONST) return true; if (x.op != O_ITE || depth <= 0) return false; return isSel(x.b, depth - 1) && isSel(x.c, depth - 1); }
  bool selValue(u32 e) { return symE(e) && E->X.N(e).op == O_ITE && isSel(e); }
  // a value with one unknown bit, as a 1-bit variable in its place (so that what is computed from it can be split on it)
  u32 bitVar(u32 e, u64 concrete, unsigned w, const VarMeta& m) {
    Ctx& X = E->X; const Ctx::Known kn = X.known(e); const u64 unk = ~(kn.zeros | kn.ones) & maskOf(w);
    if (!unk || (unk & (unk - 1))) return 0;
    unsigned long p = 0; _BitScanForward64(&p, unk);
    const u32 v1 = newVar(1, (concrete >> p) & 1, m); u32 r = X.zext(v1, w);
    if (p) r = X.shl(r, X.cst(p, w));
    if (kn.ones & maskOf(w)) r = X.or_(r, X.cst(kn.ones & maskOf(w) & ~unk, w));
    return r;
  }
};
static double nowS() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }
std::string Rp::show(u32 e, u64 concrete, unsigned w, double budget) {
  if (!e) return cstr(concrete & maskOf(w), w);
  Ctx& X = E->X; u32 r = quick(e); if (X.isC(r)) { nChecks++; if ((X.cv(r) ^ concrete) & maskOf(X.W(r))) nCheckBad++; return cstr(X.cv(r), X.W(r)); }
  const u32 n0 = X.countNodes(r); e = r;
  if (M && n0 > 3 && n0 <= 3000 && tSimp < 600) { const double t0 = nowS(); M->o.budget = budget; r = M->simplify(e); tSimp += nowS() - t0; }
  nChecks++;
  if ((X.evalSeed(r) ^ concrete) & maskOf(X.W(r))) { if (r != e && !((X.evalSeed(e) ^ concrete) & maskOf(X.W(e)))) r = e; else nCheckBad++; }
  std::string s = pr(r, 16);
  if (s.size() > 1200) {
    const std::string cut = "...{" + std::to_string(X.countNodes(r)) + " nodes}";
    if (X.N(r).op == O_ITE && isSel(r, 8)) {             // a selection keeps its leaves: its conditions are cut, not the targets
      std::function<std::string(u32)> sel = [&](u32 e) -> std::string { const Node x = X.N(e); if (x.op != O_ITE) return cstr(x.k, x.w); std::string c = pr(x.a, 16); if (c.size() > 700) { c.resize(700); c += "...{cut}"; } return "(" + c + " ? " + sel(x.b) + " : " + sel(x.c) + ")"; };
      s = sel(r);
    } else { s.resize(1200); s += cut; }
  }
  return s;
}
enum : u8 { R_STORE = 1, R_CALL = 2, R_BR = 4, R_JMP = 8, R_RET = 16, R_ESC = 32, R_END = 64, R_PHI = 128 };
struct Phi { u32 rva; u8 reg; bool live = false; std::vector<u32> feed; };
static std::vector<Phi> g_phi; static std::unordered_map<u64, u32> g_phiIx;
static u32 phiOf(u32 rva, int reg) { const u64 k = ((u64)rva << 6) | (u64)reg; auto it = g_phiIx.find(k); if (it != g_phiIx.end()) return it->second; g_phi.push_back({rva, (u8)reg}); return g_phiIx[k] = (u32)g_phi.size() - 1; }
static inline void addDep(std::vector<u32>& d, u32 p) { if (!p) return; for (u32 x : d) if (x == p) return; d.push_back(p); }
static u64 g_maxLines = ~0ull; static size_t g_nodeLimit = 6000000;
static const u32 FLB[7] = {FL_CF, FL_PF, FL_AF, FL_ZF, FL_SF, FL_OF, FL_DF};

// what the unit's lines say before any replay: how often each place is visited, from where, and what changes between visits
static u64 prescan(Reader& R, u64 off) {
  for (SI& s : g_si) { s.uvisits = 0; s.npred = 0; s.regVar = s.xVar = 0; s.mrVar = false; s.join = false; }
  R.seek(off); u32 prev = 0xffffffffu; u64 lines = 0;
  while (R.next()) {
    if (R.kind == 1) { if (lines) break; continue; }
    if (R.kind == 3) break;
    if (R.kind != 0 || !inImg(R.rip)) continue;
    if (++lines > g_maxLines) break;
    const u32 rva = (u32)(R.rip - TB); SI& s = siAt(rva);
    if (s.rep && prev == rva) continue;
    if (s.npred < 2 && !(s.npred == 1 && s.pred[0] == prev)) s.pred[s.npred++] = prev;
    u64 mh = 1469598103934665603ull; for (const Acc& a : R.mr) for (u32 i = 0; i < a.len * 2; i++) mh = (mh ^ (u8)a.hex[i]) * 1099511628211ull;
    if (!s.uvisits++) { memcpy(s.regFirst, R.G, sizeof s.regFirst); for (int x = 0; x < 16; x++) { u64 q[2]; memcpy(q, R.X[x], 16); s.xFirst[x] = q[0] * 0x9E3779B97F4A7C15ull ^ q[1]; } s.mrFirst = mh; }
    else {
      for (int r = 0; r < 16; r++) if (s.regFirst[r] != R.G[r]) s.regVar |= (u16)(1u << r);
      for (int x = 0; x < 16; x++) { u64 q[2]; memcpy(q, R.X[x], 16); if (s.xFirst[x] != (q[0] * 0x9E3779B97F4A7C15ull ^ q[1])) s.xVar |= (u16)(1u << x); }
      if (s.mrFirst != mh) s.mrVar = true;
    }
    prev = rva;
  }
  for (SI& s : g_si) { s.join = s.npred >= 2; s.regVar &= ~(1u << RSP); }
  return lines;
}

static void configure(Engine& E) { E.jitOn = false; E.keepAddressConstraints = false; E.autoMap = true; E.X.maxNodes = 60000000; E.markLimit = 0; }
// the engine is replaced by a new one: every value which had an expression becomes a variable (the node budget)
static void transplant(Rp& P) {
  Engine* N = new Engine; N->restore(*P.pristine); configure(*N);
  Engine& E = *P.E; N->gsbase = E.gsbase; N->fsbase = E.fsbase; N->mxcsr = E.mxcsr; N->fl.bits = E.rflags(); N->rip = E.rip;
  u8 np[32];
  for (int r = 0; r < 32; r++) { np[r] = P.pend[r]; if (!np[r]) { bool sy = false; if (r < 16) sy = P.symE(E.gs[r]); else if (E.vsym & (1u << (r - 16))) for (int i = 0; i < 16; i++) sy |= P.symE(E.vc[r - 16][i].e); if (sy) { np[r] = V_CARRY; P.pendRva[r] = 0; } } }
  memcpy(N->g, E.g, sizeof E.g); memcpy(N->v, E.v, sizeof E.v);
  std::vector<u8> tmp(4096);
  for (auto& kv : P.sh.pages) {
    const u64 a0 = kv.first << 12; E.readMem(a0, tmp.data(), 4096); N->writeMem(a0, tmp.data(), 4096);
    ShPage* sp = kv.second;
    for (u32 i = 0; i < 4096; i += 8) { bool any = false; for (u32 k = 0; k < 8; k++) any |= (sp->st[i + k] & SH_KNOWN) != 0; if (!any) continue;
      const Val v = E.load(a0 + i, 8); if (!P.symE(v.s)) continue;
      for (u32 k = 0; k < 8; k++) if ((sp->st[i + k] & SH_KNOWN) && P.symE(E.load(a0 + i + k, 1).s)) sp->st[i + k] |= SH_PEND; }
  }
  delete P.M; delete P.S; delete P.E; P.E = N; P.S = new Solver(N->X); P.M = new Mba(N->X, P.S); P.vm.clear(); P.qmemo.clear(); P.namedExpr.clear(); P.varNode.clear(); memset(P.pendExpr, 0, sizeof P.pendExpr); memset(P.pendExprX, 0, sizeof P.pendExprX);
  memcpy(P.pend, np, sizeof np); P.nTransplant++;
}
// is anything of [a, a + len) an expression?
static bool accSym(Rp& P, u64 a, u32 len) {
  for (u32 i = 0; i < len;) { const u32 n = std::min<u32>(8, len - i); if (P.symE(P.E->load(a + i, n).s)) return true; i += n; }
  return false;
}
// An expression whose only unknowns are 1-bit subterms (conditions) is a selection among constants: rewritten as one,
// exactly (e == a ? e[a := 1] : e[a := 0]). This is how the protector hides a branch: an arithmetic mix of a condition bit.
static void atomsOf(Ctx& X, u32 root, std::vector<u32>& atoms, bool& other, u32 limit = 600) {
  X.newGen(); std::vector<u32> st{root}; u32 seen = 0; bool first = true;
  while (!st.empty() && !other) {
    const u32 id = st.back(); st.pop_back();
    if (!id || X.stamp[id] == X.gen) continue;
    X.stamp[id] = X.gen;
    const Node& x = X.N(id);
    if (x.op == O_CONST) continue;
    if (!first && x.w == 1) { atoms.push_back(id); if (atoms.size() > 4) other = true; continue; }
    first = false;
    if (x.op == O_VAR) continue;                 // (other inputs may cancel once the conditions are fixed: the cases are checked)
    if (++seen > limit) { other = true; break; }
    st.push_back(x.a); st.push_back(x.b); st.push_back(x.c);
  }
}
static u32 substC(Ctx& X, u32 id, const std::vector<u32>& atoms, unsigned mask, std::unordered_map<u32, u32>& memo) {
  if (!id) return 0;
  for (size_t i = 0; i < atoms.size(); i++) if (atoms[i] == id) return X.cst((mask >> i) & 1, 1);
  const Node x = X.N(id);
  if (x.op == O_CONST || x.op == O_VAR) return id;
  auto it = memo.find(id); if (it != memo.end()) return it->second;
  const u32 a = substC(X, x.a, atoms, mask, memo), b = substC(X, x.b, atoms, mask, memo), c = substC(X, x.c, atoms, mask, memo);
  const u32 r = (a == x.a && b == x.b && c == x.c) ? id : X.make(x.op, x.w, x.lo, a, b, c, x.k);
  memo[id] = r; return r;
}
u32 Rp::quick(u32 e) {
  Ctx& X = E->X; if (!e || X.isC(e)) return e;
  auto it = qmemo.find(e); if (it != qmemo.end() && !(strong && it->second == e)) return it->second;
  u32 r = e; std::vector<u32> atoms; bool other = false, assumedBool = false;
  if (X.N(e).op != O_VAR) atomsOf(X, e, atoms, other, strong ? 6000 : 600);
  if (!other && X.N(e).op != O_VAR && !(X.N(e).op == O_ITE && X.isC(X.N(e).b) && X.isC(X.N(e).c))) {
    bool ok = !atoms.empty() && trySplit(e, atoms, 0, r);
    if (!ok && strong) {
      // one more unknown: a truth value kept in a byte or a register (0 or 1 in the run) - exact only if it is one
      std::vector<u32> vs; X.collectVars(e, vs);
      if (vs.size() <= 6) for (u32 v : vs) { if (v >= varNode.size() || !varNode[v] || X.vars[v].w < 8 || X.vars[v].seed > 1) continue; if (trySplit(e, atoms, varNode[v], r)) { ok = true; assumedBool = true; break; } }
    }
  }
  if (qmemo.size() > 2000000) qmemo.clear();
  if (!assumedBool) qmemo[e] = r;
  return r;
}
static u64 g_tc[12] = {}; static u64 g_repG[3] = {}; static u32 g_repS[3] = {}; static bool g_repDone = false;   // rcx, rsi, rdi before the last rep iteration
static const bool g_prof = getenv("UNSHROUD_DEOB_PROF") != nullptr;
struct Unit { u64 off = 0; u32 func = 0, entry = 0, creg = 0; bool frag = false; u64 rsp = 0, frame = 0; std::string file, line; u64 lines = 0; std::string endWhy; };
static u32 g_curEaExpr = 0; static u64 g_curEa = 0; static bool g_pass2 = true;
static void pass2Before(Rp& P, SI& s, u32 rva, Reader& R);
static void pass2After(Rp& P, SI& s, u32 rva, Reader& R, u64 rspBefore);

// memory the instruction is about to read: the engine gets the recorded bytes; what it has not seen is an input
static void syncReads(Rp& P, SI& s, u32 rva, Reader& R, bool haveEa, u64 ea, u32 eaExpr) {
  Engine& E = *P.E; Ctx& X = E.X; u8 b[64], eb[64], mark[64];
  for (const Acc& acc : R.mr) {
    const bool expl = haveEa && acc.addr == ea && s.m.rd;
    for (u32 o = 0; o < acc.len; o += 64) {
      const u32 n = std::min<u32>(64, acc.len - o); const u64 a0 = acc.addr + o;
      for (u32 i = 0; i < n; i++) b[i] = (u8)(hx(acc.hex[2 * (o + i)]) * 16 + hx(acc.hex[2 * (o + i) + 1]));
      E.readMem(a0, eb, n);
      const bool ro = roAddr(a0) && roAddr(a0 + n - 1); bool any = false;
      for (u32 i = 0; i < n; i++) {
        ShPage* sp = P.sh.page(a0 + i, true); u8& st = sp->st[(a0 + i) & 4095];
        if (ro || (st & (SH_CIN | SH_KNOWN)) == SH_CIN) { mark[i] = 0; if (eb[i] != b[i]) { E.writeMem(a0 + i, &b[i], 1); if (ro) P.nRoPatch++; } st = (u8)((st | SH_KNOWN) & ~SH_CIN); continue; }
        mark[i] = !(st & SH_KNOWN) ? V_LOAD : (st & SH_PEND) ? V_CARRY : eb[i] != b[i] ? V_EXT : 0;
        any |= mark[i] != 0;
      }
      // a load which gives other bytes at each visit, or whose address depends on inputs: its value is a variable
      if (expl && (s.mrVar || eaExpr) && !(ro && !eaExpr)) {
        const bool cut = (s.mrVar && !(n <= 8 && P.selValue(E.load(a0, n).s))) || !accSym(P, a0, n);
        if (cut) for (u32 i = 0; i < n; i++) if (!mark[i]) { mark[i] = V_LCUT; any = true;
          if (s.mrVar) { const u32 d = P.sh.page(a0 + i, true)->def[(a0 + i) & 4095]; if (d && d < 0x80000000u) { addDep(s.deps, d); siAt(d).feeds = true; } } }
      }
      if (any) for (u32 i = 0; i < n;) {
        if (!mark[i]) { i++; continue; }
        u32 j = i; while (j < n && mark[j] == mark[i]) j++;
        while (i < j) {
          const u32 sz = j - i >= 8 ? 8 : j - i >= 4 ? 4 : j - i >= 2 ? 2 : 1; const u64 a = a0 + i;
          u64 c = 0; memcpy(&c, b + i, sz);
          VarMeta m; m.kind = mark[i]; m.size = (u8)sz; m.rva = rva; m.addr = a;
          if (expl && eaExpr) {
            m.addrExpr = o + i ? X.add(eaExpr, X.cst(o + i, 64)) : eaExpr;
            std::vector<u32> vs; X.collectVars(m.addrExpr, vs); u8 dp = 0;
            for (u32 v : vs) if (v < P.vm.size()) { const VarMeta& q = P.vm[v]; if (q.size && (q.kind == V_LOAD || q.kind == V_LCUT || q.kind == V_EXT || q.kind == V_CARRY)) dp = std::max<u8>(dp, q.alias ? 1 : q.depth); }
            m.depth = (u8)(dp + 1);
            if (m.depth >= 3) {
              static const char* sn[9] = {"?", "b", "w", "?", "d", "?", "?", "?", "q"};
              if (P.pass == 2 && s.stmtN < 2) { char nb[32]; if (o + i) snprintf(nb, sizeof nb, "m%x_%x", rva, (o + i) & 0xff); else snprintf(nb, sizeof nb, "m%x", rva); P.aliasStmt += (P.aliasStmt.empty() ? "" : "; ") + std::string(nb) + " = " + sn[sz] + "[" + P.pr(m.addrExpr) + "]"; }
              m.alias = 1; m.part = (u8)(o + i);
            }
          }
          const u32 e = P.newVar(sz * 8, c, m); E.store(a, sz, Val{c, e});
          for (u32 k = 0; k < sz; k++) { ShPage* sp = P.sh.page(a + k, true); const u32 off = (u32)((a + k) & 4095); sp->st[off] = SH_KNOWN; if (mark[i] == V_LOAD || mark[i] == V_EXT) sp->def[off] = 0; }
          if (mark[i] == V_LOAD) { s.inputs++; P.nInputs++; } else if (mark[i] == V_EXT) { s.ext++; P.nExt++; }
          i += sz;
        }
      }
      if (accSym(P, a0, n)) { u32 last = 0; for (u32 i = 0; i < n; i++) { const u32 d = P.sh.page(a0 + i, true)->def[(a0 + i) & 4095]; if (d != last) { addDep(s.deps, d); last = d; } } }
    }
  }
}
// a string the replay knows at p (the image's own data, or bytes the function wrote): ASCII or UTF-16
static u64 g_ksAddr = 0; static u32 g_ksLen = 0;
static std::string knownString(Rp& P, u64 p) {
  if (p < 0x10000) return "";
  g_ksAddr = p; g_ksLen = 0;
  u8 b[200]; u32 n = 0;
  for (; n < 200; n++) { const u64 a = p + n; bool ok = inImg(a); if (!ok) { ShPage* sp = P.sh.page(a, false); ok = sp && (sp->st[a & 4095] & SH_KNOWN); } if (!ok) break; P.E->readMem(a, b + n, 1); }
  if (n >= 16) {
    u16 len, cap; u64 ptr; memcpy(&len, b, 2); memcpy(&cap, b + 2, 2); memcpy(&ptr, b + 8, 8);
    if (len >= 2 && len <= cap && cap < 0x400 && ptr > 0x10000 && ptr != p) {
      u8 t[200]; u32 m = 0; const u32 want = std::min<u32>(len, 198);
      for (; m < want; m++) { const u64 a = ptr + m; bool ok = inImg(a); if (!ok) { ShPage* sp = P.sh.page(a, false); ok = sp && (sp->st[a & 4095] & SH_KNOWN); } if (!ok) break; P.E->readMem(a, t + m, 1); }
      if (m == want) {
        bool asc = true, wide = (want & 1) == 0; std::string s8((const char*)t, want), s16;
        for (u32 k = 0; k < want; k++) asc &= t[k] >= 0x20 && t[k] < 0x7f && t[k] != '"';
        for (u32 k = 0; k + 1 < want && wide; k += 2) { wide = t[k] >= 0x20 && t[k] < 0x7f && t[k] != '"' && t[k + 1] == 0; s16 += (char)t[k]; }
        if ((wide && want >= 4) || (asc && want >= 3)) { g_ksAddr = ptr; g_ksLen = want; }
        if (wide && want >= 4) return "{L\"" + s16 + "\"}";
        if (asc && want >= 3) return "{\"" + s8 + "\"}";
      }
    }
  }
  if (n < 5) return "";
  auto pc = [](u8 c) { return c >= 0x20 && c < 0x7f && c != '"' && c != 92; };
  u32 k = 0; while (k < n && pc(b[k])) k++;
  if (k >= 4 && k < n && b[k] == 0) { g_ksLen = k; return "\"" + std::string((const char*)b, k) + "\""; }
  g_ksLen = 8;
  k = 0; std::string w; while (2 * k + 1 < n && pc(b[2 * k]) && b[2 * k + 1] == 0) { w += (char)b[2 * k]; k++; }
  if (k >= 4 && 2 * k + 1 < n && b[2 * k] == 0 && b[2 * k + 1] == 0) return "L\"" + w + "\"";
  return "";
}
// ---- computed targets: cases the rules leave open are tested on random inputs and proved by the solver; a value
// which was given a name is looked through
static u32 substE(Ctx& X, u32 id, const std::vector<std::pair<u32, u32>>& sub, std::unordered_map<u32, u32>& memo) {
  if (!id) return 0;
  for (auto& p : sub) if (p.first == id) return p.second;
  const Node x = X.N(id);
  if (x.op == O_CONST || x.op == O_VAR) return id;
  auto it = memo.find(id); if (it != memo.end()) return it->second;
  const u32 a = substE(X, x.a, sub, memo), b = substE(X, x.b, sub, memo), c = substE(X, x.c, sub, memo);
  const u32 r = (a == x.a && b == x.b && c == x.c) ? id : X.make(x.op, x.w, x.lo, a, b, c, x.k);
  memo[id] = r; return r;
}
bool Rp::provedConst(u32 e, u64& c) {
  Ctx& X = E->X; if (X.isC(e)) { c = X.cv(e); return true; }
  std::vector<u32> vs; X.collectVars(e, vs); if (vs.empty() || vs.size() > 48) return false;
  std::vector<u64> vals(X.vars.size()); for (size_t q = 0; q < vals.size(); q++) vals[q] = X.vars[q].seed;
  c = X.eval(e, vals.data()); u64 rnd = 0x9E3779B97F4A7C15ull ^ e;
  for (int t = 0; t < 6; t++) { for (u32 v : vs) { rnd ^= rnd << 13; rnd ^= rnd >> 7; rnd ^= rnd << 17; vals[v] = rnd & maskOf(X.vars[v].w); } if (X.eval(e, vals.data()) != c) return false; }
  for (u32 v : vs) vals[v] = X.vars[v].seed;
  SolveOptions o; o.timeoutMs = 2000; std::vector<u64> model; const char* stage = "";
  return S->check({}, {X.ne(e, X.cst(c, X.W(e)))}, vals, &model, o, &stage) == SR_UNSAT;
}
// e as a selection among constants on its conditions (atoms) and, if given, on a value taken as 0 or 1 (bvar)
bool Rp::trySplit(u32 e, const std::vector<u32>& atoms, u32 bvar, u32& r) {
  Ctx& X = E->X; const unsigned na = (unsigned)atoms.size() + (bvar ? 1 : 0); if (!na || na > 5) return false;
  u32 val[32]; bool proved = false;
  for (unsigned m = 0; m < (1u << na); m++) {
    std::unordered_map<u32, u32> memo; u32 v = substC(X, e, atoms, m, memo);
    if (bvar) { std::vector<std::pair<u32, u32>> sub{{bvar, X.cst((m >> atoms.size()) & 1, X.W(bvar))}}; std::unordered_map<u32, u32> memo2; v = substE(X, v, sub, memo2); }
    if (!X.isC(v)) { u64 c = 0; if (!strong || !provedConst(v, c)) return false; v = X.cst(c, X.W(e)); proved = true; }
    val[m] = v;
  }
  for (size_t i = na; i-- > 0;) { const u32 cond = i < atoms.size() ? atoms[i] : X.ne(bvar, X.cst(0, X.W(bvar))); const unsigned half = 1u << i; for (unsigned m = 0; m < half; m++) val[m] = X.ite(cond, val[m | half], val[m]); }
  const u32 out = val[0]; nSplit++;
  // (exact by construction; checked on the recorded values for the first ones, and whenever a proof or an assumption is behind it)
  if (nSplit <= 512 || strong) { nChecks++; if (X.evalSeed(out) != X.evalSeed(e)) { if (!bvar) nCheckBad++; return false; } }
  r = out; if (proved) strongProved = true; if (bvar) strongBool = true;
  return true;
}
u32 Rp::expandNamed(u32 e, int depth) {
  Ctx& X = E->X;
  for (int d = 0; d < depth && e; d++) {
    std::vector<u32> vs; X.collectVars(e, vs); std::vector<std::pair<u32, u32>> sub;
    for (u32 v : vs) { auto it = namedExpr.find(v); if (it != namedExpr.end() && v < varNode.size() && varNode[v] && X.W(varNode[v]) == X.W(it->second)) sub.push_back({varNode[v], it->second}); }
    if (sub.empty()) break;
    std::unordered_map<u32, u32> memo; const u32 r = substE(X, e, sub, memo);
    if (X.countNodes(r) > 4000) break;
    e = r;
  }
  return e;
}
// ---- strings: text the function reads a character at a time, text it stores (stack strings, decrypted buffers)
static inline bool pch(u8 c) { return (c >= 0x20 && c < 0x7f) || c == 9 || c == 10 || c == 13; }
static std::string textOf(const std::string& bytes, unsigned unit) {     // the text of a run of characters ("": it is none)
  std::string t; const size_t n = bytes.size() / unit;
  for (size_t i = 0; i < n; i++) { const u8 c = (u8)bytes[i * unit]; if (unit == 2 && bytes[i * 2 + 1]) return ""; if (!c && i + 1 == n) break; if (!pch(c)) return ""; t += (char)c; }
  return t;
}
static std::string hexOf(const std::string& b) { static const char* d = "0123456789abcdef"; std::string o; for (unsigned char c : b) { o += d[c >> 4]; o += d[c & 15]; } return o; }
struct MadeStr { std::string text, where; bool wide = false, term = false, sym = false, assumed = false; std::vector<u32> defs; u32 n = 0; };
static std::vector<MadeStr> g_made; static std::map<std::pair<u64, bool>, u32> g_madeAt; static std::map<std::string, u32> g_madeIx;
static void closeRun(Rp& P, Rp::RdRun& r) {
  if (r.unit && r.bytes.size() >= 3u * r.unit) {
    const std::string t = textOf(r.bytes, r.unit);
    if (t.size() >= 3) { SI& s = siAt(r.site); s.rdN++; const std::string q = (r.unit == 2 ? "L\"" : "\"") + t + "\""; if (s.rds.size() < 12 && std::find(s.rds.begin(), s.rds.end(), q) == s.rds.end()) { s.rds.push_back(q); s.rdsS.push_back(r.sym ? 1 : 0); } }
  }
  r.unit = 0; r.bytes.clear(); r.end = 0;
}
static bool outsideSym(Rp& P, u64 a, u32 len) {
  Ctx& X = P.E->X; std::vector<u32> vs;
  for (u32 i = 0; i < len; i++) {
    u32 e = P.E->load(a + i, 1).s; if (!P.symE(e)) continue;
    for (int k = 0; k < 4; k++) { const Node& x = X.N(e); if (x.op == O_EXTRACT || x.op == O_ZEXT || x.op == O_SEXT) e = x.a; else break; }
    if (X.N(e).op == O_VAR && !P.namedExpr.count((u32)X.N(e).k)) return true;
    e = P.expandNamed(e); vs.clear(); X.collectVars(e, vs);
    for (u32 v : vs) {
      if (v >= P.vm.size()) return true;
      const VarMeta& m = P.vm[v]; const bool load = m.kind == V_LOAD || m.kind == V_LCUT || m.kind == V_CARRY || m.kind == V_EXT;
      if (X.vars[v].w != 1 && !(load && m.size && inImg(m.addr))) return true;
    }
  }
  return false;
}
// a load of one or two bytes: does it go on where a run of such loads stopped?
static void noteRead(Rp& P, u32 rva, u64 a, unsigned unit, const u8* b, bool sym) {
  Rp::RdRun* r = nullptr; Rp::RdRun* old = &P.runs[0];
  for (Rp::RdRun& x : P.runs) { if (x.unit == unit && x.end == a && !x.z) { r = &x; break; } if (x.last < old->last) old = &x; }
  if (!r) { closeRun(P, *old); r = old; r->unit = (u8)unit; r->z = false; r->sym = false; }
  r->sym |= sym;
  if (!b[0] && (unit == 1 || !b[1])) r->z = true;       // the terminator: what follows it is another text
  r->site = rva; r->end = a + unit; r->last = P.nIns + 1; if (r->bytes.size() < 512) r->bytes.append((const char*)b, unit);
}
static void recentRuns(Rp& P, Rp::RdRun*& a, Rp::RdRun*& b) {
  a = b = nullptr;
  for (Rp::RdRun& x : P.runs) if (x.unit && P.nIns + 1 - x.last <= 6000 && x.bytes.size() >= 2u * x.unit) { if (!a || x.last > a->last) { b = a; a = &x; } else if (!b || x.last > b->last) b = &x; }
}
// a compare of values of 4 or 8 bytes right after text was read (a hash against a constant), or of what a call returned
static void noteCmp(Rp& P, SI& s, Reader& R, u64 ea) {
  Engine& E = *P.E; u64 v[2] = {0, 0}; u8 sym = 0; u32 call = 0; const u64 m = maskOf(s.opSize[0] * 8);
  for (int i = 0; i < 2; i++) {
    const u8 r = s.opReg[i];
    if (r < 16) { v[i] = E.g[r] & m; if (P.regSym(r)) { sym |= (u8)(1 << i); const u32 c = P.retCall(E.gs[r]); if (c) call = c; } }
    else if (r == 0xfe) { if (R.mr.empty() || R.mr[0].addr != ea) return; u8 b[8] = {}; const u32 n = std::min<u32>(8, R.mr[0].len); for (u32 k = 0; k < n; k++) b[k] = (u8)(hx(R.mr[0].hex[2 * k]) * 16 + hx(R.mr[0].hex[2 * k + 1])); memcpy(&v[i], b, 8); v[i] &= m; if (accSym(P, ea, n)) sym |= (u8)(1 << i); }
    else if (r == 0xfd) v[i] = (u64)s.imm & m;
    else return;
  }
  if (!sym) return;
  Rp::RdRun *a, *b; recentRuns(P, a, b);
  if (!a && !(call && (v[0] > 0xffff || v[1] > 0xffff))) return;
  const bool eq = v[0] == v[1]; (eq ? s.cmpEq : s.cmpNe)++;
  u32 have = 0; for (auto& c : s.cmpS) have += (c.a == c.b) == eq;
  if (have >= 6) return;
  CmpSample c; c.a = v[0]; c.b = v[1]; c.sym = sym; c.call = call; if (a) { c.s1 = a->bytes; c.u1 = a->unit; } if (b) { c.s2 = b->bytes; c.u2 = b->unit; }
  s.cmpS.push_back(c);
}
static std::string knownString(Rp& P, u64 p);
static void addNote(SI& s, const std::string& nn) { if (s.notes.size() < 16 && std::find(s.notes.begin(), s.notes.end(), nn) == s.notes.end()) s.notes.push_back(nn); }
static bool knownAt(Rp& P, u64 a, u32 n) { for (u32 i = 0; i < n; i++) { const u64 x = a + i; if (inImg(x)) continue; ShPage* sp = P.sh.page(x, false); if (!sp || !(sp->st[x & 4095] & SH_KNOWN)) return false; } return true; }
// what an argument points to: text, or a structure whose first words point to text (OBJECT_ATTRIBUTES, a pair of names)
static void argNotes(Rp& P, SI& s, int n, u64 p) {
  if (p < 0x10000 || p >= (1ull << 47)) return;
  std::string t = knownString(P, p);
  auto arrow = [&]() { return !roAddr(g_ksAddr) && outsideSym(P, g_ksAddr, std::min<u32>(g_ksLen ? g_ksLen : 8, 64)) ? " => " : " -> "; };   // =>: data from outside the function
  if (!t.empty()) { addNote(s, "arg" + std::to_string(n) + arrow() + t); return; }
  for (u32 o = 0; o <= 0x18; o += 8) {
    if (!knownAt(P, p + o, 8)) break;
    u64 q = 0; P.E->readMem(p + o, &q, 8); if (q < 0x10000 || q >= (1ull << 47) || q == p) continue;
    t = knownString(P, q); if (!t.empty()) { char b[32]; snprintf(b, sizeof b, "arg%d+0x%x", n, o); addNote(s, b + std::string(arrow()) + t); }
  }
}
static void recordMade(Rp& P, const std::string& t, bool wide, bool term, u64 lo, const std::vector<u32>& defs, bool sym) {
  const std::string key = (wide ? "L" : "A") + t; auto it = g_madeIx.find(key); u32 ix;
  if (it != g_madeIx.end()) ix = it->second;
  else {
    auto at = g_madeAt.find({lo, wide}); ix = ~0u;
    if (at != g_madeAt.end()) { MadeStr& o = g_made[at->second]; if (t.size() > o.text.size() && !t.compare(0, o.text.size(), o.text) && o.n <= 2) { g_madeIx.erase((wide ? "L" : "A") + o.text); o.text = t; o.term = term; ix = at->second; } }   // the same text, longer now
    if (ix == ~0u) { if (g_made.size() >= 8192) return; ix = (u32)g_made.size(); g_made.emplace_back(); g_made[ix].text = t; g_made[ix].wide = wide; g_made[ix].term = term; g_made[ix].where = P.addrName(lo); g_made[ix].assumed = g_tab != &g_real; }
    g_madeIx[key] = ix;
  }
  MadeStr& ms = g_made[ix]; ms.n++; ms.sym |= sym; g_madeAt[{lo, wide}] = ix;
  for (u32 d : defs) if (ms.defs.size() < 24 && std::find(ms.defs.begin(), ms.defs.end(), d) == ms.defs.end()) ms.defs.push_back(d);
}
// the stores of text since the last look: the whole run of characters around each, if the function wrote it
static void scanMade(Rp& P, bool partial) {
  if (P.dirty.empty()) return;
  Engine& E = *P.E; const u64 lastAddr = P.dirty.back(); std::vector<u64> keep; u64 doneLo = 0, doneHi = 0;
  auto known = [&](u64 a, u8& c, u32& def) { ShPage* sp = P.sh.page(a, false); if (!sp || !(sp->st[a & 4095] & SH_KNOWN)) return false; E.readMem(a, &c, 1); def = sp->def[a & 4095]; return true; };
  auto chr = [&](u64 a) -> int { u8 c; u32 d; if (!known(a, c, d)) return -1; return c; };
  for (u64 a : P.dirty) {
    if (a >= doneLo && a < doneHi) continue;
    const int c0 = chr(a); if (c0 < 0) continue;
    u64 lo = a, hi = a; bool wide = false;
    if (pch((u8)c0) && chr(a + 1) == 0) wide = true; else if (c0 == 0 && a && chr(a - 1) > 0 && pch((u8)chr(a - 1))) { wide = true; lo = a - 1; }
    if (wide) {
      while (a - lo < 1024 && chr(lo - 1) == 0 && chr(lo - 2) > 0 && pch((u8)chr(lo - 2))) lo -= 2;
      hi = lo; while (hi - lo < 2048 && chr(hi) > 0 && pch((u8)chr(hi)) && chr(hi + 1) == 0) hi += 2;
      if ((hi - lo) / 2 < 4) wide = false;
    }
    if (!wide) {
      if (!pch((u8)c0)) continue;
      lo = a; while (a - lo < 1024 && chr(lo - 1) > 0 && pch((u8)chr(lo - 1))) lo--;
      hi = lo; while (hi - lo < 2048 && chr(hi) > 0 && pch((u8)chr(hi))) hi++;
      if (hi - lo < 4) continue;
    }
    const bool term = wide ? (chr(hi) == 0 && chr(hi + 1) == 0) : chr(hi) == 0;
    if (partial && lastAddr + 16 >= lo && lastAddr <= hi + 16) { keep.push_back(a); continue; }      // still being written
    doneLo = lo; doneHi = hi;
    std::string t; std::vector<u32> defs; u32 own = 0;
    for (u64 x = lo; x < hi; x += wide ? 2 : 1) { u8 c; u32 d; known(x, c, d); t += (char)c; if (d && d < 0x80000000u) { own++; if (defs.size() < 24 && std::find(defs.begin(), defs.end(), d) == defs.end()) defs.push_back(d); } }
    if (own * 2 < t.size() || (!term && t.size() < 6)) continue;
    recordMade(P, t, wide, term, lo, defs, outsideSym(P, lo, (u32)std::min<u64>(hi - lo, 128)));
  }
  P.dirty.swap(keep);
}
// a computed jump whose target depends on one stored value (a state kept in a slot): value -> target, as the run shows
static void noteState(Rp& P, SI& s, u32 expr, u64 taken) {
  Ctx& X = P.E->X; const u32 e = P.expandNamed(expr); std::vector<u32> vs; X.collectVars(e, vs);
  if (vs.empty() || vs.size() > 2) return;
  std::sort(vs.begin(), vs.end()); std::string key, names; char b[40];
  for (u32 v : vs) {
    if (v >= P.vm.size()) return; const VarMeta& m = P.vm[v];
    if (X.vars[v].w == 1 || !(m.kind == V_LCUT || m.kind == V_LOAD || m.kind == V_EXT || m.kind == V_PHI || m.kind == V_CARRY)) return;
    snprintf(b, sizeof b, "%s0x%llx", key.empty() ? "" : ", ", (unsigned long long)X.vars[v].seed); key += b; names += (names.empty() ? "" : ", ") + P.varName(v, 3);
  }
  for (auto& p : s.tgState) if (p.first == key) return;
  s.tgState.push_back({key, taken}); if (s.tgStateVar.empty()) s.tgStateVar = names;
}
static void markRoot(u32 def, u8 why) { if (!def) return; if (def & 0x80000000u) g_phi[def & 0x7fffffffu].live = true; else siAt(def).root |= why; }
// frame bytes a call may read: the stack arguments stored since the last call, and what its pointer arguments point to
static void callRoots(Rp& P, u64 rsp) {
  Engine& E = *P.E;
  for (u64 a = rsp + 0x20; a < rsp + 0x60; a++) { ShPage* sp = P.sh.page(a, false); if (sp && sp->ep[a & 4095] == P.callEpoch) { const u32 d = sp->def[a & 4095]; if (d && d < 0x80000000u && siAt(d).mn == ZYDIS_MNEMONIC_PUSH) continue; markRoot(d, R_ESC); } }
  static const int ar[4] = {RCX, RDX, R8, R9};
  for (int k = 0; k < 4; k++) { const u64 p = E.g[ar[k]]; if (p < rsp || p >= P.entryRsp + 0x28) continue;
    for (u64 a = p; a < p + 0x400 && a < P.entryRsp + 0x28; a++) { ShPage* sp = P.sh.page(a, false); if (!sp || !sp->def[a & 4095]) break; markRoot(sp->def[a & 4095], R_ESC); } }
}
// ---- one recorded line of a unit, or one step of a free run (the line is then made from the engine's own state)
struct LS { bool first = true, afterGap = false, unsup = false, free = false, freeCall = false, stop = false; SI* prev = nullptr; u32 prevRva = 0; u64 prevRip = 0, lines = 0, rspBefore = 0; std::vector<u64> alts; };   // alts: where else the instruction could have gone
static bool g_assume = false; static std::unordered_set<u64> g_deadSides;     // g_deadSides: (jump << 1 | side) proved impossible: never walked
// ---- code the run did not execute. From a recorded state (the other side of a branch the run took one way) or from
// a function's entry with unknown inputs, the engine goes on by itself, one instruction at a time, through the same
// collector (stepLine); both sides of every branch which depends on inputs are walked, calls are stepped over (their
// result is unknown). What comes out is ASSUMED: the state is not one the program was seen in.
static Tab g_tmpTab; static std::vector<u8> g_realExec;      // g_realExec: rva -> ran in the recorded run
static u32 g_fbeg = 0, g_fend = 0; static u64 g_aBudget = 20000, g_aSteps = 0, g_aRoots = 0, g_aIns = 0, g_aChecks = 0, g_aChecksBad = 0;
static void analyze();
static bool strOp(u16 mn, unsigned& sz, bool& rs, bool& rd, bool& wd) {
  rs = rd = wd = false;
  switch (mn) {
  case ZYDIS_MNEMONIC_MOVSB: sz = 1; rs = wd = true; return true; case ZYDIS_MNEMONIC_MOVSW: sz = 2; rs = wd = true; return true; case ZYDIS_MNEMONIC_MOVSD: sz = 4; rs = wd = true; return true; case ZYDIS_MNEMONIC_MOVSQ: sz = 8; rs = wd = true; return true;
  case ZYDIS_MNEMONIC_STOSB: sz = 1; wd = true; return true; case ZYDIS_MNEMONIC_STOSW: sz = 2; wd = true; return true; case ZYDIS_MNEMONIC_STOSD: sz = 4; wd = true; return true; case ZYDIS_MNEMONIC_STOSQ: sz = 8; wd = true; return true;
  case ZYDIS_MNEMONIC_LODSB: sz = 1; rs = true; return true; case ZYDIS_MNEMONIC_LODSW: sz = 2; rs = true; return true; case ZYDIS_MNEMONIC_LODSD: sz = 4; rs = true; return true; case ZYDIS_MNEMONIC_LODSQ: sz = 8; rs = true; return true;
  case ZYDIS_MNEMONIC_CMPSB: sz = 1; rs = rd = true; return true; case ZYDIS_MNEMONIC_CMPSW: sz = 2; rs = rd = true; return true; case ZYDIS_MNEMONIC_CMPSQ: sz = 8; rs = rd = true; return true;
  case ZYDIS_MNEMONIC_SCASB: sz = 1; rd = true; return true; case ZYDIS_MNEMONIC_SCASW: sz = 2; rd = true; return true; case ZYDIS_MNEMONIC_SCASD: sz = 4; rd = true; return true; case ZYDIS_MNEMONIC_SCASQ: sz = 8; rd = true; return true;
  default: return false; }
}
static void synAcc(Reader& R, std::vector<Acc>& v, Engine& E, u64 addr, u32 len) {
  if (len > 64) len = 64; if (!len) return;
  u8 b[64]; E.readMem(addr, b, len); R.syn.emplace_back(); std::string& h = R.syn.back(); static const char* d = "0123456789abcdef";
  for (u32 i = 0; i < len; i++) { h += d[b[i] >> 4]; h += d[b[i] & 15]; }
  v.push_back({addr, len, h.data()});
}
static u64 memEa(Engine& E, const SI& s, u64 rip) {
  if (s.m.base == 16) return rip + s.len + (u64)s.m.disp;
  u64 ea = (u64)s.m.disp; if (s.m.base < 16) ea += E.g[s.m.base]; if (s.m.index < 16) ea += E.g[s.m.index] * (s.m.scale ? s.m.scale : 1);
  if (s.m.seg == 1) ea += E.gsbase;
  return ea;
}
// the line a trace would have for the instruction the engine is at: registers, memory read (from the engine's own memory)
static void synthBefore(Rp& P, Reader& R, const SI& s) {
  Engine& E = *P.E; R.kind = 0; R.rip = E.rip; memcpy(R.G, E.g, sizeof R.G); for (int x = 0; x < 16; x++) memcpy(R.X[x], E.v[x], 16);
  R.mr.clear(); R.mw.clear(); R.syn.clear();
  if (s.m.on && !s.m.agen && s.m.rd) synAcc(R, R.mr, E, memEa(E, s, R.rip), s.m.size);
  if (s.mn == ZYDIS_MNEMONIC_POP || s.mn == ZYDIS_MNEMONIC_RET || s.mn == ZYDIS_MNEMONIC_POPFQ) synAcc(R, R.mr, E, E.g[RSP], 8);
  else if (s.mn == ZYDIS_MNEMONIC_LEAVE) synAcc(R, R.mr, E, E.g[RBP], 8);
  unsigned sz = 0; bool rs, rd, wd;
  if (strOp(s.mn, sz, rs, rd, wd) && !(s.rep && !E.g[RCX])) { if (rs) synAcc(R, R.mr, E, E.g[RSI], sz); if (rd) synAcc(R, R.mr, E, E.g[RDI], sz); }
}
// ... and what it wrote
static void synthAfter(Rp& P, Reader& R, const SI& s, bool haveEa, u64 ea, u64 rspBefore, u64 rdiBefore) {
  Engine& E = *P.E;
  if (haveEa && s.m.wr) synAcc(R, R.mw, E, ea, s.m.size);
  if (s.mn == ZYDIS_MNEMONIC_PUSH || s.mn == ZYDIS_MNEMONIC_PUSHFQ || s.mn == ZYDIS_MNEMONIC_CALL) synAcc(R, R.mw, E, rspBefore - 8, 8);
  unsigned sz = 0; bool rs, rd, wd;
  if (strOp(s.mn, sz, rs, rd, wd) && wd && E.g[RDI] != rdiBefore) synAcc(R, R.mw, E, rdiBefore, sz);
}
static void collectLeaves(Ctx& X, u32 e, u64 not_, std::vector<u64>& out, int depth = 6) {
  const Node x = X.N(e);
  if (x.op == O_CONST) { if (x.k != not_ && out.size() < 16 && std::find(out.begin(), out.end(), x.k) == out.end()) out.push_back(x.k); return; }
  if (x.op == O_ITE && depth > 0) { collectLeaves(X, x.b, not_, out, depth - 1); collectLeaves(X, x.c, not_, out, depth - 1); }
}
static void stepLine(Rp& P, Reader& R, Unit& U, LS& L, const bool lastP) {
  bool& first = L.first; bool& afterGap = L.afterGap; bool& unsup = L.unsup; SI*& prev = L.prev; u32& prevRva = L.prevRva; u64& prevRip = L.prevRip; u64& lines = L.lines; u64& rspBefore = L.rspBefore;
  static const u32 VOL = (1u << RAX) | (1u << RCX) | (1u << RDX) | (1u << R8) | (1u << R9) | (1u << R10) | (1u << R11);
    Engine* Ep = P.E; if (!L.free && (lines & 4095) == 0 && Ep->X.n.size() > g_nodeLimit) { transplant(P); Ep = P.E; }
    Engine& E = *Ep; const u32 rva = (u32)(R.rip - TB); SI& s = siAt(rva);
    u64 tc0 = g_prof ? __rdtsc() : 0;
    // ---- the state the previous instruction left, against the trace
    bool transfer = first;
    if (!first && g_repDone && prev->rep && R.rip == prevRip && R.G[RCX] == g_repG[0] && E.g[RCX] != R.G[RCX]) {
      E.g[RCX] = g_repG[0]; E.g[RSI] = g_repG[1]; E.g[RDI] = g_repG[2]; E.gs[RCX] = g_repS[0]; E.gs[RSI] = g_repS[1]; E.gs[RDI] = g_repS[2]; E.rip = R.rip;
    }
    g_repDone = false;
    if (!first) {
      const bool wasCall = prev->kind == K_CALL || prev->kind == K_CALLI || prev->kind == K_TRAP;
      if (prev->kind == K_JCC && !afterGap) { if (R.rip != prevRip + prev->len) prev->taken++; else prev->fall++; if (E.rip != R.rip) { P.nFlagMism++; E.rip = R.rip; } }
      if (afterGap || L.freeCall || (wasCall && (E.rip != R.rip || E.g[RSP] != R.G[RSP]))) { transfer = true; if (prev->kind == K_CALL || prev->kind == K_CALLI) prev->rv.see(false, R.G[RAX]); }
      else if (E.rip != R.rip) { transfer = true; P.nMism++; P.mismBy[std::string("control:") + Engine::mnemonicName(prev->mn)]++;
        if (getenv("UNSHROUD_DEOB_DEBUG") && P.nMism < 12) fprintf(stderr, "control mismatch after %x (%s): engine %llx, trace %llx, rsp %llx / %llx%c", prevRva, Engine::mnemonicName(prev->mn), (unsigned long long)E.rip, (unsigned long long)R.rip, (unsigned long long)E.g[RSP], (unsigned long long)R.G[RSP], 10); }
    }
    if (transfer) {
      for (int r = 0; r < 16; r++) {
        if (r == RSP) { E.g[r] = R.G[r]; continue; }
        const bool probe = s.mn == ZYDIS_MNEMONIC_SUB && s.opReg[0] == RSP && s.opReg[1] == RAX;
        if (first || E.g[r] != R.G[r] || (r == RAX && !probe) || (L.freeCall && ((VOL >> r) & 1) && r != RAX)) { E.g[r] = R.G[r]; if (first && U.frag && ((U.creg >> r) & 1)) P.setPend(r, 0, 0); else P.setPend(r, first ? (U.frag ? V_PHI : V_ENTRY) : r == RAX ? V_RET : V_CLOB, first ? rva : prevRva); P.lastDef[r] = 0; }
      }
      for (int x = 0; x < 16; x++) if (first || (L.freeCall && x < 6) || memcmp(E.v[x], R.X[x], 16)) { memcpy(E.v[x], R.X[x], 16); if (first && U.frag && ((U.creg >> (16 + x)) & 1)) P.setPend(16 + x, 0, 0); else P.setPend(16 + x, first ? (U.frag ? V_PHI : V_ENTRY) : V_CLOB, first ? rva : prevRva); P.lastDef[16 + x] = 0; }
      if (!first) { memset(P.lastDefF, 0, sizeof P.lastDefF); P.callEpoch++; }
      E.rip = R.rip;
    } else {
      if (prev->kind == K_ENV) for (int r = 0; r < 16; r++) if ((prev->envOut >> r) & 1) { E.g[r] = R.G[r]; P.setPend(r, V_ENV, prevRva); }
      for (int r = 0; r < 16; r++) if (E.g[r] != R.G[r]) {
        if (r != RSP && !unsup) { P.nMism++; prev->mism++; P.mismBy[Engine::mnemonicName(prev->mn)]++; }
        if (g_prof && r != RSP && P.nMism < 8) fprintf(stderr, "mismatch after %x (%s) line %llu: %s engine %llx, trace %llx%c", prevRva, Engine::mnemonicName(prev->mn), (unsigned long long)lines, RN[r], (unsigned long long)E.g[r], (unsigned long long)R.G[r], 10);
        E.g[r] = R.G[r]; if (r != RSP) P.setPend(r, V_FIX, prevRva); }
      for (int x = 0; x < 16; x++) if (memcmp(E.v[x], R.X[x], 16)) { if (!unsup) { P.nMism++; prev->mism++; P.mismBy[Engine::mnemonicName(prev->mn)]++; } memcpy(E.v[x], R.X[x], 16); P.setPend(16 + x, V_FIX, prevRva); }
    }
    first = false; afterGap = false; unsup = false; L.freeCall = false;
    // ---- before the instruction
    s.visits++;
    if (s.join) {
      for (int r = 0; r < 16; r++) if (((s.regVar >> r) & 1) && !(!P.pend[r] && P.selValue(E.gs[r]))) { const u32 ph = phiOf(rva, r); addDep(g_phi[ph].feed, P.lastDef[r]); P.lastDef[r] = 0x80000000u | ph; P.setPend(r, V_PHI, rva); }
      for (int x = 0; x < 16; x++) if ((s.xVar >> x) & 1) { const u32 ph = phiOf(rva, 16 + x); addDep(g_phi[ph].feed, P.lastDef[16 + x]); P.lastDef[16 + x] = 0x80000000u | ph; P.setPend(16 + x, V_PHI, rva); }
    }
    bool haveEa = false; u64 ea = 0; u32 eaExpr = 0;
    if (s.m.on && !s.m.agen) {
      haveEa = true;
      if (s.m.base == 16) ea = R.rip + s.len + (u64)s.m.disp;
      else {
        ea = (u64)s.m.disp; if (s.m.base < 16) { P.need(s.m.base); ea += E.g[s.m.base]; } if (s.m.index < 16) { P.need(s.m.index); ea += E.g[s.m.index] * (s.m.scale ? s.m.scale : 1); }
        const bool bs = s.m.base < 16 && P.symE(E.gs[s.m.base]), is = s.m.index < 16 && P.symE(E.gs[s.m.index]);
        if (bs || is) { Ctx& X = E.X; u32 e = X.cst((u64)s.m.disp, 64); if (s.m.base < 16) e = X.add(e, E.S(E.getReg(s.m.base), 64)); if (s.m.index < 16) e = X.add(e, X.mul(E.S(E.getReg(s.m.index), 64), X.cst(s.m.scale ? s.m.scale : 1, 64))); eaExpr = P.symE(e) ? e : 0; }
        if (s.m.seg == 1) { const std::vector<Acc>& v = s.m.rd ? R.mr : R.mw; if (!v.empty()) { E.gsbase = v[0].addr - ea; } ea += E.gsbase; }
      }
    }
    if (g_prof) { const u64 t = __rdtsc(); g_tc[0] += t - tc0; tc0 = t; }
    for (int r = 0; r < 32; r++) if ((s.rd >> r) & 1) if (P.regSym(r)) addDep(s.deps, P.lastDef[r]);
    for (int f = 0; f < 7; f++) if ((s.rdF >> f) & 1) if (P.symE(E.flagExpr(FLB[f]))) addDep(s.deps, P.lastDefF[f]);
    if (!R.mr.empty()) syncReads(P, s, rva, R, haveEa, ea, eaExpr);
    if (lastP && haveEa && s.m.rd && !s.rep && (s.m.size == 1 || s.m.size == 2)) for (const Acc& acc : R.mr) if (acc.addr == ea && acc.len == s.m.size) { u8 cb[2]; hexBytes(acc, cb); noteRead(P, rva, ea, s.m.size, cb, outsideSym(P, ea, s.m.size)); break; }
    for (int i = 0; i < s.nexp; i++) if (s.opAct[i] & 1) {
      const u8 r = s.opReg[i];
      if (r < 16) s.in[i].see(P.regSym(r), E.g[r] & maskOf(s.opSize[i] * 8));
      else if (r < 32) { u64 q[2]; memcpy(q, E.v[r - 16], 16); s.in[i].see(P.regSym(r), q[0], q[1]); }
      else if (r == 0xfe && s.m.rd && !R.mr.empty() && R.mr[0].addr == ea) { u8 b[16] = {}; const u32 n = std::min<u32>(16, R.mr[0].len); for (u32 k = 0; k < n; k++) b[k] = (u8)(hx(R.mr[0].hex[2 * k]) * 16 + hx(R.mr[0].hex[2 * k + 1])); u64 q[2]; memcpy(q, b, 16); s.in[i].see(accSym(P, ea, n), q[0], q[1]); }
    }
    if (lastP && s.mn == ZYDIS_MNEMONIC_CMP && s.nexp >= 2 && s.opSize[0] >= 4) noteCmp(P, s, R, ea);
    if (lastP && (s.kind == K_CALL || s.kind == K_CALLI || s.kind == K_RET)) scanMade(P, false);
    if (lastP && s.kind == K_RET && P.regSym(RAX)) { Rp::RdRun *ra, *rb; recentRuns(P, ra, rb); u32 have = (u32)s.cmpS.size(); if (ra && have < 8) { CmpSample c; c.a = E.g[RAX]; c.sym = 4; c.s1 = ra->bytes; c.u1 = ra->unit; if (rb) { c.s2 = rb->bytes; c.u2 = rb->unit; } s.cmpS.push_back(c); } }
    if (s.kind == K_CALL || s.kind == K_CALLI) {
      static const int ar[4] = {RCX, RDX, R8, R9};
      if (lastP && s.visits <= 64) { for (int k = 0; k < 4; k++) argNotes(P, s, k + 1, E.g[ar[k]]);
        for (int k = 4; k < 8; k++) { const u64 a = E.g[RSP] + 0x20 + 8 * (u64)(k - 4); ShPage* sp = P.sh.page(a, false); if (sp && sp->ep[a & 4095] == P.callEpoch && (sp->st[a & 4095] & SH_KNOWN)) { u64 v = 0; E.readMem(a, &v, 8); argNotes(P, s, k + 1, v); } } }
      for (int k = 0; k < 4; k++) s.arg[k].see(P.symE(E.gs[ar[k]]), E.g[ar[k]]);
      callRoots(P, E.g[RSP]);
    }
    g_curEaExpr = eaExpr; g_curEa = ea;
    if (g_prof) { const u64 t = __rdtsc(); g_tc[1] += t - tc0; tc0 = t; }
    if (P.pass == 2) pass2Before(P, s, rva, R);
    rspBefore = E.g[RSP]; const u64 rdi0 = E.g[RDI];
    // ---- the instruction
    const size_t fm = E.foldedTaken.size();
    E.rip = R.rip; E.stops.clear(); E.stops.insert(R.rip + s.len);
    Stop st = ST_COUNT; unsigned rsz = 0; bool movs = false;
    if (s.rep) switch (s.mn) {
      case ZYDIS_MNEMONIC_MOVSB: rsz = 1; movs = true; break; case ZYDIS_MNEMONIC_MOVSW: rsz = 2; movs = true; break; case ZYDIS_MNEMONIC_MOVSD: rsz = 4; movs = true; break; case ZYDIS_MNEMONIC_MOVSQ: rsz = 8; movs = true; break;
      case ZYDIS_MNEMONIC_STOSB: rsz = 1; break; case ZYDIS_MNEMONIC_STOSW: rsz = 2; break; case ZYDIS_MNEMONIC_STOSD: rsz = 4; break; case ZYDIS_MNEMONIC_STOSQ: rsz = 8; break;
      default: break; }
    if (rsz) {
      // one iteration, as the trace has it (a line per iteration)
      Ctx& X = E.X; const bool had = E.g[RCX] != 0;      // (the trace has one more line, with a count of zero, which ends the instruction)
      if (E.g[RCX]) {
        g_repG[0] = E.g[RCX]; g_repG[1] = E.g[RSI]; g_repG[2] = E.g[RDI]; g_repS[0] = E.gs[RCX]; g_repS[1] = E.gs[RSI]; g_repS[2] = E.gs[RDI]; g_repDone = true;
        const u64 step = (E.rflags() & FL_DF) ? (u64)0 - rsz : rsz;
        Val v = movs ? E.load(E.g[RSI], rsz) : Val{E.g[RAX] & maskOf(rsz * 8), E.gs[RAX] ? (rsz == 8 ? E.gs[RAX] : X.extract(E.gs[RAX], 0, rsz * 8)) : 0};
        E.store(E.g[RDI], rsz, v);
        if (movs) { E.g[RSI] += step; if (E.gs[RSI]) E.gs[RSI] = X.add(E.gs[RSI], X.cst(step, 64)); }
        E.g[RDI] += step; if (E.gs[RDI]) E.gs[RDI] = X.add(E.gs[RDI], X.cst(step, 64));
        E.g[RCX] -= 1; if (E.gs[RCX]) E.gs[RCX] = X.add(E.gs[RCX], X.cst(~0ull, 64));
      }
      E.rip = R.rip + (had ? 0 : s.len);
    } else { try { st = E.run(1); } catch (...) { st = ST_FAULT; } }
    P.nIns++; E.gs[RSP] = 0;
    if (L.free) { if (st == ST_FAULT || st == ST_UNSUPPORTED || st == ST_EXCEPTION || st == ST_HALT || st == ST_SYSCALL || st == ST_HOOK) L.stop = true; synthAfter(P, R, s, haveEa, ea, rspBefore, rdi0); }
    if (g_prof) { const u64 t = __rdtsc(); g_tc[2] += t - tc0; tc0 = t; }
    if (st == ST_UNSUPPORTED || (st == ST_FAULT && s.kind != K_TRAP)) { unsup = true; P.nUnsup++; P.mismBy[std::string("unsupported:") + Engine::mnemonicName(s.mn)]++; E.rip = R.rip + s.len; E.X.overBudget = false; }
    const bool last = P.pass == (g_pass2 ? 2 : 1);
    for (const PathConstraint& c : E.path) {
      Ctx& X = E.X;
      if (c.kind == 0 && s.kind == K_JCC) {
        s.symCond++; s.root |= R_BR;
        if (g_assume && (L.free || lastP)) { const u64 fallA = R.rip + s.len, other = c.taken != fallA ? fallA : fallA + (u64)s.imm; if (!g_deadSides.count(((u64)rva << 1) | (other == fallA ? 0 : 1))) L.alts.push_back(other); }
        if (last && s.cond.empty()) { const bool tk = c.taken != R.rip + s.len; s.cond = P.show(tk ? c.cond : X.not_(c.cond), tk ? 1 : 0, 1); }
      } else if (c.kind == 2 && (s.kind == K_JMPI || s.kind == K_CALLI)) {
        s.sawSym = true; if (s.kind == K_JMPI) s.root |= R_JMP;
        if (last && s.kind == K_JMPI && s.tgState.size() < 16 && s.visits <= 4096) noteState(P, s, c.expr, c.taken);
        if (last && s.tgExpr.empty()) { const u32 ex = P.expandNamed(c.expr); P.strong = true; P.strongBool = P.strongProved = false; s.tgExpr = P.show(ex, c.taken, 64); s.tgBool = P.strongBool; s.tgProved = P.strongProved; const u32 sel = P.quick(ex); P.strong = false; if (P.isSel(sel, 8)) collectLeaves(X, sel, ~0ull, s.tgLeaves, 8); }
        if (g_assume && s.kind == K_JMPI && (L.free || (lastP && s.visits <= 2))) { P.strong = true; const u32 q = P.quick(P.expandNamed(c.expr)); P.strong = false; if (P.isSel(q)) collectLeaves(X, q, c.taken, L.alts); }
        if (last && s.tgCond.empty() && s.kind == K_JMPI && !s.targets.empty() && s.targets[0].first != c.taken && s.targets.size() <= 2) {
          // the hidden condition: when does the jump go to its first recorded target? and can it go anywhere else?
          const u64 A = s.targets[0].first, B = c.taken;
          s.tgCond = P.show(X.eq(c.expr, X.cst(A, 64)), 0, 1);
          std::vector<u64> seed(X.vars.size()), model; for (size_t q = 0; q < seed.size(); q++) seed[q] = X.vars[q].seed;
          SolveOptions o; o.timeoutMs = 1500; const char* stage = "";
          const SatResult sr = seed.size() < 3000000 ? P.S->check({}, {X.ne(c.expr, X.cst(A, 64)), X.ne(c.expr, X.cst(B, 64))}, seed, &model, o, &stage) : SR_UNKNOWN;
          s.tgCond += sr == SR_UNSAT ? " [only these two: proved]" : sr == SR_SAT ? " [a third value is not excluded by the expression alone]" : " [third value: undecided]";
        }
      }
    }
    if (!E.path.empty()) E.path.clear();
    if (E.foldedTaken.size() > fm) s.folded++;
    if (E.folded.size() > 20000) { E.folded.clear(); E.foldedTaken.clear(); }
    if (s.kind == K_JMPI || s.kind == K_CALLI) { bool f = false; for (auto& t : s.targets) if (t.first == E.rip) { t.second++; f = true; break; } if (!f && s.targets.size() < 256) s.targets.push_back({E.rip, 1}); }
    u8 b[64], eb[64];
    for (const Acc& acc : R.mw) for (u32 o = 0; o < acc.len; o += 64) {
      const u32 n = std::min<u32>(64, acc.len - o); const u64 a0 = acc.addr + o;
      for (u32 i = 0; i < n; i++) b[i] = (u8)(hx(acc.hex[2 * (o + i)]) * 16 + hx(acc.hex[2 * (o + i) + 1]));
      E.readMem(a0, eb, n); P.nMw++;
      if (memcmp(b, eb, n)) { if (s.mn == ZYDIS_MNEMONIC_STMXCSR && n == 4) memcpy(&E.mxcsr, b, 4); else if (!unsup) { P.nMwBad++; s.mism++; P.mismBy[std::string("store:") + Engine::mnemonicName(s.mn)]++; } E.writeMem(a0, b, n); }
      if (!(a0 + 0x100 >= E.g[RSP] && a0 < P.entryRsp + 0x28)) s.root |= R_STORE;
      for (u32 i = 0; i < n; i++) { ShPage* sp = P.sh.page(a0 + i, true); const u32 off = (u32)((a0 + i) & 4095); sp->st[off] = SH_KNOWN; sp->def[off] = rva; sp->ep[off] = P.callEpoch; }
      if (lastP) {
        int pos = -1;
        if (n <= 2) { if (pch(b[0]) && (n == 1 || b[1] == 0 || pch(b[1]))) pos = 0; }
        else { u32 run = 0; for (u32 i = 0; i < n && pos < 0; i++) { if (pch(b[i])) { if (++run >= 3) pos = (int)(i + 1 - run); } else { if (b[i] == 0 && run == 1 && i + 2 < n && pch(b[i + 1]) && b[i + 2] == 0) pos = (int)i - 1; run = 0; } } }
        if (pos >= 0) { P.dirty.push_back(a0 + (u32)pos); if (P.dirty.size() >= 4096) scanMade(P, true); }
      }
    }
    for (int r = 0; r < 32; r++) if ((s.wr >> r) & 1) { P.lastDef[r] = rva; if (!((s.wrPart >> r) & 1)) P.pend[r] = 0; }
    for (int f = 0; f < 7; f++) if ((s.wrF >> f) & 1) P.lastDefF[f] = rva;
    if (s.dstReg < 16) { const u32 e = E.gs[s.dstReg]; s.out.see(P.symE(e), E.g[s.dstReg] & maskOf(s.opSize[0] * 8)); if (e && E.X.isC(e)) P.nFolded++; }
    else if (s.dstReg < 32) { u64 q[2]; memcpy(q, E.v[s.dstReg - 16], 16); s.out.see(P.regSym(s.dstReg), q[0], q[1]); }
    else if (s.m.wr && !R.mw.empty()) { u8 v[16] = {}; const u32 n = std::min<u32>(16, R.mw[0].len); for (u32 k = 0; k < n; k++) v[k] = (u8)(hx(R.mw[0].hex[2 * k]) * 16 + hx(R.mw[0].hex[2 * k + 1])); u64 q[2]; memcpy(q, v, 16); s.out.see(accSym(P, R.mw[0].addr, n), q[0], q[1]); }
    if (s.kind == K_RET) s.root |= R_RET;
    if (s.kind == K_CALL || s.kind == K_CALLI) s.root |= R_CALL;
    if (g_prof) { const u64 t = __rdtsc(); g_tc[3] += t - tc0; tc0 = t; }
    if (P.pass == 2) pass2After(P, s, rva, R, rspBefore);
    if (g_prof) { const u64 t = __rdtsc(); g_tc[4] += t - tc0; tc0 = t; }
    prev = &s; prevRva = rva; prevRip = R.rip;
}
struct RpSave { u8 pend[32]; u32 pendRva[32], pendExpr[16], pendExprX[16][2], lastDef[32], lastDefF[7], callEpoch; };
static void saveRp(const Rp& P, RpSave& s) { memcpy(s.pend, P.pend, sizeof s.pend); memcpy(s.pendRva, P.pendRva, sizeof s.pendRva); memcpy(s.pendExpr, P.pendExpr, sizeof s.pendExpr); memcpy(s.pendExprX, P.pendExprX, sizeof s.pendExprX); memcpy(s.lastDef, P.lastDef, sizeof s.lastDef); memcpy(s.lastDefF, P.lastDefF, sizeof s.lastDefF); s.callEpoch = P.callEpoch; }
static void loadRp(Rp& P, const RpSave& s) { memcpy(P.pend, s.pend, sizeof s.pend); memcpy(P.pendRva, s.pendRva, sizeof s.pendRva); memcpy(P.pendExpr, s.pendExpr, sizeof s.pendExpr); memcpy(P.pendExprX, s.pendExprX, sizeof s.pendExprX); memcpy(P.lastDef, s.lastDef, sizeof s.lastDef); memcpy(P.lastDefF, s.lastDefF, sizeof s.lastDefF); P.callEpoch = s.callEpoch; }
struct Work { u64 rip = 0; bool fresh = false; std::shared_ptr<State> st; RpSave rs; std::shared_ptr<std::vector<std::pair<u64, ShPage>>> sh; };
static bool walkable(u64 rip) {
  if (!inImg(rip)) return false; const u32 rva = (u32)(rip - TB);
  return rva >= g_fbeg && rva < g_fend && !g_realExec[rva] && !g_asmTab.idx[rva];
}
static bool walkedNow(u64 rip) { const u32 ix = g_tmpTab.idx[(u32)(rip - TB)]; return ix && g_tmpTab.si[ix - 1].visits; }
static u64 freeWalk(Rp& P, Unit& U, std::vector<Work>& work, bool lastP, u64 budget) {
  Engine& E = *P.E; Reader R; static SI dummy; u64 steps = 0; Shadow* base = P.sh.base;
  while (!work.empty() && steps < budget) {
    Work w = std::move(work.back()); work.pop_back();
    if (!walkable(w.rip) || walkedNow(w.rip)) continue;
    E.restore(*w.st); E.rip = w.rip; loadRp(P, w.rs);
    if (w.sh) { P.sh.clear(); P.sh.base = base; for (auto& kv : *w.sh) P.sh.pages[kv.first] = new ShPage(kv.second); }
    else if (w.fresh) { P.sh.clear(); P.sh.base = base; }
    LS L; L.free = true; L.first = false; L.prev = &dummy; u64 idle = 0;
    while (steps < budget) {
      if (!walkable(E.rip)) break;
      const u32 rva = (u32)(E.rip - TB); SI& s = siAt(rva);
      if (!s.mn || s.visits >= 48) break;
      idle = s.visits ? idle + 1 : 0; if (idle > 3000) break;
      if (s.rep && E.g[RCX] > 4096) break;
      const u64 rip0 = E.rip; synthBefore(P, R, s); stepLine(P, R, U, L, lastP); steps++;
      if (L.stop || s.kind == K_RET || s.kind == K_TRAP) break;
      for (u64 alt : L.alts) if (walkable(alt) && !walkedNow(alt) && work.size() < 200) {
        Work n; n.rip = alt; n.st = E.snapshot(); saveRp(P, n.rs);
        if (P.sh.pages.size() <= 96) { n.sh = std::make_shared<std::vector<std::pair<u64, ShPage>>>(); n.sh->reserve(P.sh.pages.size()); for (auto& kv : P.sh.pages) n.sh->push_back({kv.first, *kv.second}); }
        work.push_back(std::move(n));
      }
      L.alts.clear();
      if (s.kind == K_CALL || s.kind == K_CALLI) {             // not followed: it returns, with a result nobody knows
        E.rip = rip0 + s.len; E.g[RSP] = L.rspBefore;
        bool probe = false; if (inImg(E.rip)) { const SI& nx = siAt((u32)(E.rip - TB)); probe = nx.mn == ZYDIS_MNEMONIC_SUB && nx.opReg[0] == RSP && nx.opReg[1] == RAX; }
        if (!probe) E.g[RAX] = 0;
        L.freeCall = true;
      }
    }
  }
  work.clear();
  return steps;
}
static void resetFacts(SI& s) {
  s.visits = 0; for (Fact& x : s.in) x = Fact(); s.out = Fact(); for (Fact& x : s.arg) x = Fact(); s.rv = Fact(); s.taken = s.fall = s.symCond = s.folded = 0; s.targets.clear(); s.inputs = s.ext = s.mism = 0; s.notes.clear(); s.sawSym = false;
}
// alts: places the recorded run (or nothing at all) never went to, reachable from the engine's present state
static void forkRoots(Rp& P, Unit& U, const std::vector<u64>& alts) {
  std::vector<u64> roots; for (u64 a : alts) if (walkable(a) && std::find(roots.begin(), roots.end(), a) == roots.end()) roots.push_back(a);
  if (roots.empty()) return;
  Engine& E = *P.E; std::shared_ptr<State> st0 = E.snapshot(); RpSave rs0; saveRp(P, rs0); const u64 symIns0 = E.symIns;
  Shadow realSh; realSh.pages.swap(P.sh.pages); P.sh.lastPn = ~0ull; P.sh.last = nullptr;
  const u64 c0[12] = {P.nIns, P.nInputs, P.nExt, P.nRoPatch, P.nMism, P.nMw, P.nMwBad, P.nUnsup, P.nFlagMism, P.nVars, P.nFolded, P.nSym}; const u64 ck0 = P.nChecks, ckb0 = P.nCheckBad;
  const std::map<std::string, u64> by0 = P.mismBy; Rp::RdRun runs0[4]; for (int i = 0; i < 4; i++) runs0[i] = P.runs[i]; const std::vector<u64> dirty0 = P.dirty; const std::string alias0 = P.aliasStmt; const int pass0 = P.pass;
  Tab* tab0 = g_tab; g_tab = &g_tmpTab;
  for (int mp = 1; mp <= 2; mp++) {
    P.pass = mp; P.sh.clear(); P.sh.base = &realSh; P.dirty.clear(); P.aliasStmt.clear(); for (auto& x : P.runs) { x.unit = 0; x.bytes.clear(); x.end = 0; }
    std::vector<Work> work; RpSave rs = rs0; memset(rs.lastDef, 0, sizeof rs.lastDef); memset(rs.lastDefF, 0, sizeof rs.lastDefF);
    for (size_t i = roots.size(); i-- > 0;) { Work w; w.rip = roots[i]; w.fresh = true; w.st = st0; w.rs = rs; work.push_back(std::move(w)); }
    g_aSteps += freeWalk(P, U, work, mp == 2, g_aBudget);
    if (mp == 2) { scanMade(P, false); for (auto& x : P.runs) closeRun(P, x); }
    else { analyze(); for (SI& s : g_tmpTab.si) resetFacts(s); }
  }
  for (size_t i = 0; i < g_tmpTab.si.size(); i++) if (g_tmpTab.si[i].visits) {
    const u32 rva = g_tmpTab.rva[i]; if (g_asmTab.idx[rva]) continue;
    g_asmTab.si.push_back(std::move(g_tmpTab.si[i])); g_asmTab.rva.push_back(rva); g_asmTab.idx[rva] = (u32)g_asmTab.si.size(); g_aIns++;
  }
  for (u32 rva : g_tmpTab.rva) g_tmpTab.idx[rva] = 0;
  g_tmpTab.si.clear(); g_tmpTab.rva.clear();
  // back to the state the recorded run was in
  g_tab = tab0; P.pass = pass0; P.sh.clear(); P.sh.base = nullptr; P.sh.pages.swap(realSh.pages); E.restore(*st0); loadRp(P, rs0); E.symIns = symIns0;
  g_aChecks += P.nChecks - ck0; g_aChecksBad += P.nCheckBad - ckb0; P.nChecks = ck0; P.nCheckBad = ckb0;
  P.nIns = c0[0]; P.nInputs = c0[1]; P.nExt = c0[2]; P.nRoPatch = c0[3]; P.nMism = c0[4]; P.nMw = c0[5]; P.nMwBad = c0[6]; P.nUnsup = c0[7]; P.nFlagMism = c0[8]; P.nVars = c0[9]; P.nFolded = c0[10]; P.nSym = c0[11];
  P.mismBy = by0; for (int i = 0; i < 4; i++) P.runs[i] = runs0[i]; P.dirty = dirty0; P.aliasStmt = alias0;
  g_aRoots++;
}
static void replay(Rp& P, Reader& R, Unit& U) {
  P.E = new Engine; P.E->restore(*P.pristine); configure(*P.E); P.S = new Solver(P.E->X); P.M = new Mba(P.E->X, P.S);
  P.sh.clear(); P.vm.clear(); P.qmemo.clear(); memset(P.pend, 0, sizeof P.pend); memset(P.lastDef, 0, sizeof P.lastDef); memset(P.lastDefF, 0, sizeof P.lastDefF);
  P.callEpoch = 1; P.frag = U.frag; P.entryRsp = U.frag ? (U.frame ? U.frame : U.rsp + 0x8000) : U.rsp; P.frameLo = U.rsp - 0x100000;
  P.namedExpr.clear(); P.varNode.clear(); memset(P.pendExpr, 0, sizeof P.pendExpr); memset(P.pendExprX, 0, sizeof P.pendExprX); P.dirty.clear(); for (auto& x : P.runs) { x.unit = 0; x.bytes.clear(); x.end = 0; x.last = 0; }
  const bool lastP = P.pass == (g_pass2 ? 2 : 1);
  R.seek(U.off); LS L; bool& afterGap = L.afterGap; u64& lines = L.lines;
  while (R.next()) {
    if (R.kind == 1) { if (lines) break; continue; }
    if (R.kind == 3) { U.endWhy = R.text; break; }
    if (R.kind == 4) { for (auto& rg : R.gapRd) for (u64 a = rg.first; a < rg.first + rg.second; a++) P.sh.page(a, true)->st[a & 4095] |= SH_CIN; continue; }
    if (R.kind == 2) {
      afterGap = true;                               // the callees' reads of this frame keep their producers
      if (R.gapAll) { for (auto& kv : P.sh.pages) for (u32 i = 0; i < 4096; i++) { const u64 a = (kv.first << 12) + i; if (a >= P.E->g[RSP] && a < P.entryRsp + 0x28) markRoot(kv.second->def[i], R_ESC); } }
      else for (auto& rg : R.gapRd) for (u64 a = rg.first; a < rg.first + rg.second; a++) { ShPage* sp = P.sh.page(a, false); if (sp) markRoot(sp->def[a & 4095], R_ESC); }
      continue;
    }
    if (!inImg(R.rip)) continue;
    if (++lines > g_maxLines) { U.endWhy = "#end reason=maxlines"; break; }
    stepLine(P, R, U, L, lastP);
    if (!L.alts.empty()) { if (g_assume && lastP) forkRoots(P, U, L.alts); L.alts.clear(); }
  }
  if (U.endWhy.find("reason=ret") == std::string::npos) for (int r = 0; r < 16; r++) markRoot(P.lastDef[r], R_END);
  if (lastP) { scanMade(P, false); for (auto& x : P.runs) closeRun(P, x); }
  U.lines = lines; P.nSym += P.E->symIns;
  if (g_prof) { fprintf(stderr, "prof pass %d: sync %.1f uses+reads %.1f step %.1f post %.1f pass2after %.1f [quick %.1f (%llu calls) bitvar %.1f stores %.1f] (Gcycles), nodes %zu vars %zu%c", P.pass, g_tc[0] / 1e9, g_tc[1] / 1e9, g_tc[2] / 1e9, g_tc[3] / 1e9, g_tc[4] / 1e9, g_tc[6] / 1e9, (unsigned long long)g_tc[9], g_tc[7] / 1e9, g_tc[8] / 1e9, P.E->X.n.size(), P.E->X.vars.size(), 10); memset(g_tc, 0, sizeof g_tc); }
  delete P.M; delete P.S; delete P.E; P.M = nullptr; P.S = nullptr; P.E = nullptr;
}
// ---- after pass 1: what is live, and which values get a name (those which more than one statement needs)
static void analyze() {
  const u32 n = (u32)g_si.size(); std::vector<u32> work;
  for (u32 i = 0; i < n; i++) { SI& s = g_si[i]; s.live = s.root != 0; if (s.live) work.push_back(i); }
  std::vector<u32> pw; for (u32 i = 0; i < g_phi.size(); i++) if (g_phi[i].live) pw.push_back(i);
  auto visit = [&](u32 d, bool feed) {
    if (d & 0x80000000u) { Phi& p = g_phi[d & 0x7fffffffu]; if (!p.live) { p.live = true; pw.push_back(d & 0x7fffffffu); } return; }
    const u32 ix = g_sidx[d]; if (!ix) return; SI& t = g_si[ix - 1]; if (feed) t.feeds = true; if (!t.live) { t.live = true; work.push_back(ix - 1); } };
  while (!work.empty() || !pw.empty()) {
    if (!work.empty()) { const u32 i = work.back(); work.pop_back(); const std::vector<u32> d = g_si[i].deps; for (u32 x : d) visit(x, false); }
    else { const u32 i = pw.back(); pw.pop_back(); const std::vector<u32> d = g_phi[i].feed; for (u32 x : d) visit(x, true); }
  }
  // dominators of the graph "statement -> what it uses", from a root above every statement which stands by itself
  std::vector<u32> id(n, 0), order; std::vector<std::vector<u32>> cons(n + 1);          // node numbers: 0 = the root, i + 1 = instruction i
  auto top = [&](const SI& s) { return s.live && (s.root || s.feeds); };
  for (u32 i = 0; i < n; i++) { const SI& s = g_si[i]; if (!s.live) continue; if (top(s)) cons[i + 1].push_back(0);
    for (u32 x : s.deps) if (!(x & 0x80000000u)) { const u32 ix = g_sidx[x]; if (ix && g_si[ix - 1].live) cons[ix].push_back(i + 1); } }
  std::vector<int> rpo(n + 1, -1); std::vector<u32> post; std::vector<std::pair<u32, u32>> stk; std::vector<u8> seen(n + 1, 0);
  auto succ = [&](u32 v, u32 k) -> u32 {                 // the k-th node v uses (0: none left)
    if (v == 0) { for (u32 i = k; i < n; i++) if (top(g_si[i])) return i + 1; return 0; }
    return 0; };
  // iterative depth-first walk (the root's successors are the top statements; an instruction's are what it uses)
  seen[0] = 1; stk.push_back({0, 0});
  while (!stk.empty()) {
    u32 v = stk.back().first; u32& k = stk.back().second; u32 nx = 0;
    if (v == 0) { while (k < n && !(top(g_si[k]) && !seen[k + 1])) k++; if (k < n) { nx = k + 1; k++; } }
    else { const std::vector<u32>& d = g_si[v - 1].deps; while (k < d.size()) { const u32 x = d[k++]; if (x & 0x80000000u) continue; const u32 ix = g_sidx[x]; if (ix && g_si[ix - 1].live && !seen[ix]) { nx = ix; break; } } }
    if (nx) { seen[nx] = 1; stk.push_back({nx, 0}); } else { post.push_back(v); stk.pop_back(); }
  }
  for (size_t i = 0; i < post.size(); i++) rpo[post[i]] = (int)(post.size() - 1 - i);
  std::vector<int> idom(n + 1, -1); idom[0] = 0; bool changed = true;
  auto inter = [&](int a, int b) { while (a != b) { while (rpo[a] > rpo[b]) a = idom[a]; while (rpo[b] > rpo[a]) b = idom[b]; } return a; };
  while (changed) { changed = false;
    for (size_t i = post.size(); i-- > 0;) { const u32 v = post[i]; if (v == 0) continue; int ni = -1;
      for (u32 c : cons[v]) { if (rpo[c] < 0 || idom[c] < 0) continue; ni = ni < 0 ? (int)c : inter((int)c, ni); }
      if (ni >= 0 && idom[v] != ni) { idom[v] = ni; changed = true; } } }
  for (u32 i = 0; i < n; i++) { SI& s = g_si[i]; s.named = s.live && (s.wr || (s.root & R_STORE) || s.feeds || (s.root & R_ESC)) && (top(s) || idom[i + 1] == 0) && s.kind != K_JCC; }
}
static std::string regText(Rp& P, int r) {
  Engine& E = *P.E; P.need(r);
  if (r < 16) return P.show(E.gs[r], E.g[r], 64, 0.05);
  const int x = r - 16; u64 q[2]; memcpy(q, E.v[x], 16);
  const u32 lo = cellsExpr(E.X, E.v[x], E.vc[x], 8), hi = cellsExpr(E.X, E.v[x] + 8, E.vc[x] + 8, 8);
  return "{" + P.show(P.symE(hi) ? hi : 0, q[1], 64, 0.05) + ", " + P.show(P.symE(lo) ? lo : 0, q[0], 64, 0.05) + "}";
}
static void addStmt(SI& s, const std::string& t) { if (s.stmtN == 0) s.stmt.push_back(t); else if (std::find(s.stmt.begin(), s.stmt.end(), t) == s.stmt.end()) { s.stmtAlt++; if (s.stmt.size() < 6) s.stmt.push_back("| " + t); } }
static void pass2Before(Rp& P, SI& s, u32 rva, Reader& R) {
  Engine& E = *P.E;
  if (!P.aliasStmt.empty()) { if (s.stmtN < 2) addStmt(s, P.aliasStmt); P.aliasStmt.clear(); }
  if (s.stmtN >= 2) return;
  if (s.kind == K_CALL || s.kind == K_CALLI) {
    static const int ar[4] = {RCX, RDX, R8, R9}; std::string t = "args:";
    for (int k = 0; k < 4; k++) t += std::string(k ? ", " : " ") + RN[ar[k]] + "=" + regText(P, ar[k]);
    addStmt(s, t);
  } else if (s.kind == K_RET) addStmt(s, "return " + regText(P, RAX));
}
static const u32 SMALL = 12;                      // an expression of at most that many nodes is written out where it is used: no name
static void pass2After(Rp& P, SI& s, u32 rva, Reader& R, u64 rspBefore) {
  Engine& E = *P.E; Ctx& X = E.X;
  const bool isCall = s.kind == K_CALL || s.kind == K_CALLI;
  struct Inc { SI& s; ~Inc() { s.stmtN++; } } inc{s};
  if (!s.named) return;
  const bool cap = s.stmtN < 2, must = s.feeds || (s.root & R_END); std::string t;
  auto add = [&](const std::string& x) { t += (t.empty() ? "" : "; ") + x; };
  auto qk = [&](u32 e) -> u32 { if ((s.qTry >= 48 && !s.qHit) || (s.qTry >= 512 && s.qHit * 4 < s.qTry)) return e; s.qTry++; const u64 t0 = __rdtsc(); const u32 r = P.quick(e); g_tc[6] += __rdtsc() - t0; g_tc[9]++; if (r != e) s.qHit++; return r; };
  if (!isCall) for (int r = 0; r < 32; r++) if ((s.wr >> r) & 1) {
    if (!P.regSym(r)) { if (cap && must) add(std::string(RN[r]) + " = " + regText(P, r)); continue; }
    bool big;
    if (r < 16) { const u32 e = qk(E.gs[r]); E.gs[r] = e; big = X.N(e).size > SMALL && !P.isSel(e); }
    else {
      const int x = r - 16; big = false;
      for (int q = 0; q < 2; q++) { const u32 e0 = cellsExpr(X, E.v[x] + 8 * q, E.vc[x] + 8 * q, 8); if (!P.symE(e0)) continue; const u32 e = qk(e0);
        if (e != e0) for (int i = 0; i < 8; i++) E.vc[x][8 * q + i] = X.isC(e) ? Cell{0, 0} : Cell{e, (u32)i};
        big |= X.N(e).size > SMALL; }
    }
    if (cap && (must || big)) add(std::string(RN[r]) + " = " + regText(P, r));
    if (big && r < 16) { VarMeta m; m.kind = V_NAMED; m.reg = (u8)r; m.rva = rva; const u64 t0 = __rdtsc(); const u32 bv = P.bitVar(E.gs[r], E.g[r], 64, m); g_tc[7] += __rdtsc() - t0; if (bv) { E.gs[r] = bv; continue; } }
    if (big) P.setPend(r, V_NAMED, rva);
  }
  const bool rootStore = (s.root & (R_STORE | R_ESC)) != 0; const u64 tm0 = __rdtsc();
  for (const Acc& acc : R.mw) {
    if (isCall && acc.addr + 8 == rspBefore) continue;       // (the return address)
    for (u32 o = 0; o < acc.len && o < 64;) {
      const u32 left = acc.len - o; const u32 w = left >= 8 ? 8 : left >= 4 ? 4 : left >= 2 ? 2 : 1; const u64 a = acc.addr + o;
      Val v = E.load(a, w); const bool expl = g_curEaExpr && acc.addr == g_curEa; bool big = false;
      if (P.symE(v.s)) { const u32 e = qk(v.s); if (e != v.s) { v.s = X.isC(e) ? 0 : e; E.store(a, w, v); } big = v.s && X.N(v.s).size > SMALL && !P.isSel(v.s); }
      static const char* sn[9] = {"?", "b", "w", "?", "d", "?", "?", "?", "q"};
      const u32 ae = expl ? (o ? X.add(g_curEaExpr, X.cst(o, 64)) : g_curEaExpr) : 0;
      if (cap && (rootStore || big)) add(std::string(sn[w]) + "[" + (ae ? P.pr(ae) : P.addrName(a)) + "] = " + P.show(v.s, v.c, w * 8, 0.05));
      if (big) { VarMeta m; m.kind = V_LOAD; m.size = (u8)w; m.rva = rva; m.addr = a; m.addrExpr = ae; const u32 bv = P.bitVar(v.s, v.c, w * 8, m); E.store(a, w, Val{v.c, bv ? bv : P.newVar(w * 8, v.c, m)}); }
      o += w;
    }
  }
  g_tc[8] += __rdtsc() - tm0;
  if (cap && !t.empty()) addStmt(s, t);
}
static std::string esc(const std::string& s) {
  std::string o; for (char c : s) { if (c == '"' || c == 92) { o += (char)92; o += c; } else if ((unsigned char)c < 0x20) o += ' '; else o += c; } return o;
}
static void factJson(FILE* f, const Fact& x) { fprintf(f, "[%d, \"%llx\", \"%llx\"]", x.st, (unsigned long long)x.lo, (unsigned long long)x.hi); }
static void writeRow(FILE* f, const SI& s, u32 rva, bool as) {
    fprintf(f, "{\"rva\": \"%x\", \"n\": %u, \"mn\": \"%s\", \"len\": %u, \"k\": %u, \"live\": %d, \"named\": %d, \"root\": %u, \"join\": %d", rva, s.visits, Engine::mnemonicName(s.mn), s.len, s.kind, s.live ? 1 : 0, s.named ? 1 : 0, s.root, s.join ? 1 : 0);
    fprintf(f, ", \"in\": ["); bool c = false;
    for (int k = 0; k < s.nexp; k++) if (s.in[k].st) { fprintf(f, "%s[%d, ", c ? ", " : "", k); factJson(f, s.in[k]); fprintf(f, "]"); c = true; }
    fprintf(f, "], \"out\": "); factJson(f, s.out);
    if (s.kind == K_JCC) fprintf(f, ", \"jcc\": [%u, %u, %u, %u]", s.taken, s.fall, s.symCond, s.folded);
    if (!s.cond.empty()) fprintf(f, ", \"cond\": \"%s\"", esc(s.cond).c_str());
    if (!s.targets.empty()) { fprintf(f, ", \"tg\": ["); for (size_t k = 0; k < s.targets.size(); k++) fprintf(f, "%s[\"%s%llx\", %u]", k ? ", " : "", inImg(s.targets[k].first) ? "" : "x", (unsigned long long)(inImg(s.targets[k].first) ? s.targets[k].first - TB : s.targets[k].first), s.targets[k].second); fprintf(f, "], \"tsym\": %d", s.sawSym ? 1 : 0); }
    if (!s.tgExpr.empty()) fprintf(f, ", \"tgx\": \"%s\"", esc(s.tgExpr).c_str());
    if (!s.tgCond.empty()) fprintf(f, ", \"tgc\": \"%s\"", esc(s.tgCond).c_str());
    if (s.kind == K_CALL || s.kind == K_CALLI) { fprintf(f, ", \"arg\": ["); for (int k = 0; k < 4; k++) { fprintf(f, k ? ", " : ""); factJson(f, s.arg[k]); } fprintf(f, "], \"rv\": "); factJson(f, s.rv); }
    if (!s.notes.empty()) { fprintf(f, ", \"notes\": ["); for (size_t k = 0; k < s.notes.size(); k++) fprintf(f, "%s\"%s\"", k ? ", " : "", esc(s.notes[k]).c_str()); fprintf(f, "]"); }
    if (!s.stmt.empty()) { fprintf(f, ", \"stmt\": ["); for (size_t k = 0; k < s.stmt.size(); k++) fprintf(f, "%s\"%s\"", k ? ", " : "", esc(s.stmt[k]).c_str()); fprintf(f, "], \"alt\": %u", s.stmtAlt); }
    if (!s.rds.empty()) { fprintf(f, ", \"rds\": ["); for (size_t k = 0; k < s.rds.size(); k++) fprintf(f, "%s\"%s\"", k ? ", " : "", esc(s.rds[k]).c_str()); fprintf(f, "], \"rdss\": ["); for (size_t k = 0; k < s.rdsS.size(); k++) fprintf(f, "%s%u", k ? ", " : "", s.rdsS[k]); fprintf(f, "], \"rdn\": %u", s.rdN); }
    if (!s.cmpS.empty()) {
      fprintf(f, ", \"cmp\": {\"eq\": %u, \"ne\": %u, \"s\": [", s.cmpEq, s.cmpNe);
      for (size_t k = 0; k < s.cmpS.size(); k++) { const CmpSample& c = s.cmpS[k]; fprintf(f, "%s[\"%llx\", \"%llx\", %u, \"%x\", %u, \"%s\", %u, \"%s\"]", k ? ", " : "", (unsigned long long)c.a, (unsigned long long)c.b, c.sym, c.call, c.u1, hexOf(c.s1).c_str(), c.u2, hexOf(c.s2).c_str()); }
      fprintf(f, "]}");
    }
    if (!s.tgState.empty()) {
      fprintf(f, ", \"tgs\": [");
      for (size_t k = 0; k < s.tgState.size(); k++) { const u64 t = s.tgState[k].second; fprintf(f, "%s[\"%s\", \"%s%llx\"]", k ? ", " : "", s.tgState[k].first.c_str(), inImg(t) ? "" : "x", (unsigned long long)(inImg(t) ? t - TB : t)); }
      fprintf(f, "], \"tgsv\": \"%s\"", esc(s.tgStateVar).c_str());
    }
    if (!s.tgLeaves.empty()) { fprintf(f, ", \"tgl\": ["); for (size_t k = 0; k < s.tgLeaves.size(); k++) { const u64 t = s.tgLeaves[k]; fprintf(f, "%s\"%s%llx\"", k ? ", " : "", inImg(t) ? "" : "x", (unsigned long long)(inImg(t) ? t - TB : t)); } fprintf(f, "]"); }
    if (s.tgBool) fprintf(f, ", \"tgb\": 1");
    if (s.tgProved) fprintf(f, ", \"tgp\": 1");
    if (s.inputs || s.ext || s.mism) fprintf(f, ", \"inp\": %u, \"ext\": %u, \"mism\": %u", s.inputs, s.ext, s.mism);
    fprintf(f, "%s}%c", as ? ", \"as\": 1" : "", 10);
}
static void writeMade(FILE* f) {
  for (const MadeStr& m : g_made) {
    fprintf(f, "{\"made\": {\"t\": \"%s\", \"w\": %d, \"z\": %d, \"s\": %d, \"as\": %d, \"at\": \"%s\", \"n\": %u, \"defs\": [", esc(m.text).c_str(), m.wide ? 1 : 0, m.term ? 1 : 0, m.sym ? 1 : 0, m.assumed ? 1 : 0, esc(m.where).c_str(), m.n);
    for (size_t k = 0; k < m.defs.size(); k++) fprintf(f, "%s\"%x\"", k ? ", " : "", m.defs[k]);
    fprintf(f, "]}}%c", 10);
  }
}
// the function (or the code between two functions) an rva lies in: free runs stay inside
static void setRange(u32 rva) {
  g_fbeg = rva; g_fend = (u32)std::min<u64>(ISIZE, (u64)rva + 0x40000); u32 next = (u32)ISIZE;
  for (auto& fn : g_funcs) { if (rva >= fn.first && rva < fn.second) { g_fbeg = fn.first; g_fend = fn.second; return; } if (fn.first > rva && fn.first < next) next = fn.first; }
  g_fend = std::min(g_fend, next);
}
// ---- functions the run never entered: walked from their first instruction, every register an unknown input
//   unshroud_deob <pe> <trace base> --assume <out dir> <function rva | @file with one rva per line>...
static int assumeMain(Rp& P, int argc, char** argv) {
  g_assume = true; g_pass2 = true; std::vector<u32> fn;
  for (int i = 5; i < argc; i++) {
    if (argv[i][0] == '@') { FILE* l = fopen(argv[i] + 1, "rb"); char b[64]; while (l && fgets(b, sizeof b, l)) { const u32 r = (u32)strtoull(b, nullptr, 16); if (r) fn.push_back(r); } if (l) fclose(l); }
    else fn.push_back((u32)strtoull(argv[i], nullptr, 16));
  }
  const double t0 = nowS(); u64 done = 0, total = 0;
  for (u32 f0 : fn) {
    if (f0 >= ISIZE) continue;
    setRange(f0); Unit U; U.func = f0; U.entry = f0; U.rsp = 0x30000ff000ull;
    P.E = new Engine; P.E->restore(*P.pristine); configure(*P.E); P.S = new Solver(P.E->X); P.M = new Mba(P.E->X, P.S);
    P.sh.clear(); P.vm.clear(); P.qmemo.clear(); memset(P.pend, 0, sizeof P.pend); memset(P.lastDef, 0, sizeof P.lastDef); memset(P.lastDefF, 0, sizeof P.lastDefF);
    P.callEpoch = 1; P.frag = false; P.entryRsp = U.rsp; P.frameLo = U.rsp - 0x100000; P.pass = 2;
    P.namedExpr.clear(); P.varNode.clear(); memset(P.pendExpr, 0, sizeof P.pendExpr); memset(P.pendExprX, 0, sizeof P.pendExprX); P.dirty.clear(); for (auto& x : P.runs) { x.unit = 0; x.bytes.clear(); x.end = 0; x.last = 0; }
    P.nChecks = P.nCheckBad = 0;
    Engine& E = *P.E; E.gsbase = 0x7ff7fff00000ull; E.rip = TB + f0;
    for (int r = 0; r < 16; r++) { if (r == RSP) { E.g[r] = U.rsp; continue; } E.g[r] = 0x5000000000ull + (u64)r * 0x100000000ull; P.setPend(r, V_ENTRY, f0); }
    for (int x = 0; x < 16; x++) P.setPend(16 + x, V_ENTRY, f0);
    const std::vector<u64> roots{TB + f0}; forkRoots(P, U, roots);
    char path[700]; snprintf(path, sizeof path, "%s/%x.jsonl", argv[4], f0);
    if (g_aIns) if (FILE* f = fopen(path, "wb")) {
      g_tab = &g_asmTab; for (size_t i = 0; i < g_si.size(); i++) if (g_si[i].visits) writeRow(f, g_si[i], g_siRva[i], true); g_tab = &g_real;
      writeMade(f);
      fprintf(f, "{\"summary\": {\"func\": \"%x\", \"units\": 0, \"lines\": 0, \"assumed\": %llu, \"steps\": %llu, \"mismatch\": 0, \"stores\": 0, \"stores_bad\": 0, \"achecks\": %llu, \"achecks_bad\": %llu}}%c", f0, (unsigned long long)g_aIns, (unsigned long long)g_aSteps, (unsigned long long)g_aChecks, (unsigned long long)g_aChecksBad, 10);
      fclose(f);
    }
    total += g_aIns;
    for (u32 rva : g_asmTab.rva) g_asmTab.idx[rva] = 0;
    g_asmTab.si.clear(); g_asmTab.rva.clear(); g_made.clear(); g_madeAt.clear(); g_madeIx.clear(); g_aIns = g_aSteps = g_aChecks = g_aChecksBad = 0;
    for (u32 rva : g_real.rva) g_real.idx[rva] = 0;
    g_real.si.clear(); g_real.rva.clear(); g_phi.clear(); g_phiIx.clear();
    delete P.M; delete P.S; delete P.E; P.M = nullptr; P.S = nullptr; P.E = nullptr;
    if (++done % 50 == 0) { fprintf(stderr, "assume: %llu functions, %llu instructions, %.1f s%c", (unsigned long long)done, (unsigned long long)total, nowS() - t0, 10); fflush(stderr); }
  }
  fprintf(stderr, "assume: %llu functions, %llu instructions, %.1f s%c", (unsigned long long)done, (unsigned long long)total, nowS() - t0, 10);
  return 0;
}
int main(int argc, char** argv) {
  unshroud::limitMemory();
  if (argc < 5) { printf("usage: unshroud_deob <pe> <trace base> <out.jsonl> segment...%c", 10); return 1; }
  TB = strtoull(argv[2], nullptr, 16);
  if (const char* e = getenv("UNSHROUD_DEOB_PASS2")) g_pass2 = atoi(e) != 0;
  if (const char* e = getenv("UNSHROUD_DEOB_MAXLINES")) g_maxLines = strtoull(e, nullptr, 0);
  if (const char* e = getenv("UNSHROUD_DEOB_NODES")) g_nodeLimit = strtoull(e, nullptr, 0);
  Rp P;
  { Engine base; if (!mapImage(base, argv[1])) { printf("cannot load%c", 10); return 1; } P.pristine = base.snapshot(); }
  g_real.idx.assign((size_t)ISIZE, 0); g_asmTab.idx.assign((size_t)ISIZE, 0); g_tmpTab.idx.assign((size_t)ISIZE, 0); g_realExec.assign((size_t)ISIZE, 0);
  if (const char* e = getenv("UNSHROUD_DEOB_ASSUME")) g_assume = atoi(e) != 0;
  if (const char* e = getenv("UNSHROUD_DEOB_ABUDGET")) g_aBudget = strtoull(e, nullptr, 0);
  if (const char* e = getenv("UNSHROUD_DEOB_DEAD")) if (FILE* df = fopen(e, "rb")) { char b[128]; while (fgets(b, sizeof b, df)) { char* q = b; const u64 r = strtoull(q, &q, 16); const u64 sd = strtoull(q, &q, 10); if (r) g_deadSides.insert((r << 1) | (sd & 1)); } fclose(df); }
  if (argc >= 5 && !strcmp(argv[3], "--assume")) return assumeMain(P, argc, argv);
  // the units of the segment files
  std::vector<Unit> units;
  for (int i = 4; i < argc; i++) {
    Reader R; if (!R.open(argv[i])) continue;
    for (;;) { const u64 o = R.tell(); if (!R.next()) break;
      if (R.kind == 1) { Unit u; u.off = o; u.file = argv[i]; u.line = R.text;
        auto fld = [&](const char* k) -> std::string { size_t p = R.text.find(k); if (p == std::string::npos) return ""; p += strlen(k); size_t q = R.text.find(' ', p); return R.text.substr(p, q == std::string::npos ? q : q - p); };
        u.func = (u32)strtoull(fld("func=").c_str(), nullptr, 16); u.entry = (u32)strtoull(fld("entry=").c_str(), nullptr, 16); u.frag = fld("frag=") == "1"; u.rsp = strtoull(fld(" rsp=").c_str(), nullptr, 16); u.frame = strtoull(fld("frame=").c_str(), nullptr, 16); u.creg = (u32)strtoull(fld("creg=").c_str(), nullptr, 16);
        units.push_back(u); } }
    R.close();
  }
  const double t0 = nowS(); u64 lines1 = 0, mism1 = 0, mwBad1 = 0, flag1 = 0; double tPass1 = 0;
  for (int pass = 1; pass <= (g_pass2 ? 2 : 1); pass++) {
    P.pass = pass;
    if (pass == 2) {
      analyze(); tPass1 = nowS() - t0; mism1 = P.nMism; mwBad1 = P.nMwBad; flag1 = P.nFlagMism;
      for (size_t i = 0; i < g_si.size(); i++) if (g_si[i].visits) g_realExec[g_siRva[i]] = 1;
      if (!units.empty()) setRange(units[0].func);
      for (SI& s : g_si) resetFacts(s);
      P.nIns = P.nSym = P.nInputs = P.nExt = P.nRoPatch = P.nMism = P.nMw = P.nMwBad = P.nUnsup = P.nFlagMism = P.nVars = P.nFolded = P.nTransplant = 0; P.mismBy.clear();
    }
    for (Unit& u : units) {
      Reader R; if (!R.open(u.file.c_str())) continue;
      prescan(R, u.off); replay(P, R, u); R.close();
      if (pass == 1) lines1 += u.lines;
      fprintf(stderr, "pass %d unit %x%s: %llu lines, %.1f s, mismatches %llu, stores bad %llu%c", pass, u.entry, u.frag ? " (frag)" : "", (unsigned long long)u.lines, nowS() - t0, (unsigned long long)P.nMism, (unsigned long long)P.nMwBad, 10);
    }
  }
  if (!g_pass2) analyze();
  FILE* f = fopen(argv[3], "wb"); if (!f) return 1;
  u64 nStatic = 0, nLive = 0, nStmt = 0, nConstOut = 0;
  for (int as = 0; as <= 1; as++) {
    g_tab = as ? &g_asmTab : &g_real;
    for (size_t i = 0; i < g_si.size(); i++) {
      const SI& s = g_si[i]; if (!s.visits) continue;
      if (!as) { nStatic++; nLive += s.live; nStmt += !s.stmt.empty() || (s.live && (s.kind == K_JCC || s.kind == K_JMPI)); nConstOut += s.out.st == ST_CONST; }
      writeRow(f, s, g_siRva[i], as != 0);
    }
  }
  g_tab = &g_real;
  writeMade(f);
  fprintf(f, "{\"asum\": {\"ins\": %llu, \"roots\": %llu, \"steps\": %llu, \"checks\": %llu, \"checks_bad\": %llu}}%c", (unsigned long long)g_aIns, (unsigned long long)g_aRoots, (unsigned long long)g_aSteps, (unsigned long long)g_aChecks, (unsigned long long)g_aChecksBad, 10);
  fprintf(f, "{\"summary\": {\"func\": \"%x\", \"units\": %zu, \"lines\": %llu, \"static\": %llu, \"live\": %llu, \"statements\": %llu, \"const_out\": %llu, \"ins\": %llu, \"sym_ins\": %llu, \"inputs\": %llu, \"ext\": %llu, \"ro_patched\": %llu, \"mismatch\": %llu, \"stores\": %llu, \"stores_bad\": %llu, \"flag_mismatch\": %llu, \"unsupported\": %llu, \"folded_const\": %llu, \"vars\": %llu, \"transplants\": %llu, \"checks\": %llu, \"checks_bad\": %llu, \"mismatch_pass1\": %llu, \"stores_bad_pass1\": %llu, \"t_pass1\": %.2f, \"t_all\": %.2f, \"t_simplify\": %.2f, \"by\": {",
    units.empty() ? 0 : units[0].func, units.size(), (unsigned long long)lines1, (unsigned long long)nStatic, (unsigned long long)nLive, (unsigned long long)nStmt, (unsigned long long)nConstOut, (unsigned long long)P.nIns, (unsigned long long)P.nSym, (unsigned long long)P.nInputs, (unsigned long long)P.nExt, (unsigned long long)P.nRoPatch, (unsigned long long)P.nMism, (unsigned long long)P.nMw, (unsigned long long)P.nMwBad, (unsigned long long)P.nFlagMism, (unsigned long long)P.nUnsup, (unsigned long long)P.nFolded, (unsigned long long)P.nVars, (unsigned long long)P.nTransplant, (unsigned long long)P.nChecks, (unsigned long long)P.nCheckBad, (unsigned long long)mism1, (unsigned long long)mwBad1, tPass1, nowS() - t0, P.tSimp);
  { bool c = false; for (auto& kv : P.mismBy) { fprintf(f, "%s\"%s\": %llu", c ? ", " : "", kv.first.c_str(), (unsigned long long)kv.second); c = true; } }
  fprintf(f, "}, \"unit_list\": [");
  for (size_t i = 0; i < units.size(); i++) fprintf(f, "%s{\"entry\": \"%x\", \"frag\": %d, \"lines\": %llu, \"end\": \"%s\", \"hdr\": \"%s\"}", i ? ", " : "", units[i].entry, units[i].frag ? 1 : 0, (unsigned long long)units[i].lines, esc(units[i].endWhy).c_str(), esc(units[i].line).c_str());
  fprintf(f, "]}}%c", 10); fclose(f);
  return 0;
}
