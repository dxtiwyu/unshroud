// unshroud_tseg: cuts Tenet text traces (each file the consecutive lines of one thread) into segments, one per
// function invocation: the lines whose rip is in the function itself (the lines of its callees are left out).
//   unshroud_tseg <pe> <module base in the trace, hex> <out dir> [--funcs rva,rva] [--per N] [--max-seg N] [--cap N]
//             [--lines N] [--state file] [--no-const] [--no-events] trace...
// The call stack of a thread is followed with the image's .pdata (which function a line is in) and the stack pointer
// (a frame ends when rsp climbs above its value at the entry). For each function: the first --per invocations are
// written whole (up to --cap own lines), later ones only when they execute an instruction no segment holds yet (up
// to --max-seg segments). Past those limits only stretches around new instructions are written ("frag" units).
// Files: <out>/<function rva>_<k>.seg, <out>/<function rva>_frag.seg. Format:
//   #seg func=<rva> entry=<rva> frag=<0|1> file=<trace> line=<n> rsp=<hex> [frame=<entry rsp> creg=<mask> cfl=<mask>]
//   #const addr:len;...   (frag units) memory bytes which are constants of the path so far; creg / cfl: the registers
//        (bit 0-15 GPR, 16-31 XMM) and flags which are. A constant depends on no input of the invocation (entry
//        registers, memory it did not write, results of calls, cpuid / rdtsc): followed for every frame, cheaply
//        (which registers and bytes an instruction reads and writes; no values computed). --no-const: left out.
//   trace lines; the first one and every one after a gap list every register
//   #gap n=<lines left out> rd=<addr>:<len>;...   (rd: what the callees read of this function's frame, "*" = too much)
//   #end reason=<ret|tail|cap|sparse|eof> own=<lines of the unit>
// <out>/events.txt (appended; --no-events: not written), counted per distinct line:
//   F site=<rva> target=<hex> handler=<rva> code=<exception code> ctxrip=<hex> next=<rva> n=<count> first=<file:line>
//        the module's code was entered where no instruction sent it: a fault at site (a call to target, or the
//        instruction itself) and its handler (rcx -> EXCEPTION_POINTERS); ctxrip: what the handler stored into
//        CONTEXT.Rip (0: nothing); next: the first module code after the handler returned.
//   B site=<rva> target=<hex> entry=<rva> n= first=      a call out of the module which called back into it
//   C <file> <line> dst=<hex> src=<hex> len=<hex> rip=<rva>   256 bytes or more copied by the module's code
#include <Zydis/Zydis.h>
#include <windows.h>
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <unordered_map>
#include <vector>
#include <deque>
#include <map>
#include "unshroud_insinfo.hpp"
using insinfo::InsInfo;
typedef uint8_t u8; typedef uint16_t u16; typedef uint32_t u32; typedef uint64_t u64;

static inline u64 hexv(const char*& p, const char* e) {
  u64 v = 0;
  while (p < e) { char c = *p; int d; if (c >= '0' && c <= '9') d = c - '0'; else if (c >= 'a' && c <= 'f') d = c - 'a' + 10; else if (c >= 'A' && c <= 'F') d = c - 'A' + 10; else break; v = v * 16 + d; p++; }
  return v;
}
static std::vector<u8> g_img;                      // the image as mapped (rva -> byte)
static std::vector<u32> g_fid;                     // rva -> function index + 1 (0: no .pdata entry; then the gap's own id)
static std::vector<u32> g_fstart;                  // function index -> start rva
static std::vector<u8> g_ilen;                     // rva -> 0 unknown, else length | 0x80 if it is a call
static ZydisDecoder g_dec; static std::vector<u32> g_iix;
struct Sec { u32 rva, size; bool w; }; static std::vector<Sec> g_secs;
static bool loadImage(const char* path, u64& size) {
  FILE* f = fopen(path, "rb"); if (!f) return false;
  fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
  std::vector<u8> d((size_t)sz); if (fread(d.data(), 1, d.size(), f) != d.size()) { fclose(f); return false; } fclose(f);
  auto* dos = (IMAGE_DOS_HEADER*)d.data(); auto* nt = (IMAGE_NT_HEADERS64*)(d.data() + dos->e_lfanew);
  size = nt->OptionalHeader.SizeOfImage; g_img.assign((size_t)size, 0);
  memcpy(g_img.data(), d.data(), std::min<size_t>(nt->OptionalHeader.SizeOfHeaders, d.size()));
  auto* sec = IMAGE_FIRST_SECTION(nt);
  for (unsigned i = 0; i < nt->FileHeader.NumberOfSections; i++) {
    size_t raw = std::min<size_t>(sec[i].SizeOfRawData, sec[i].Misc.VirtualSize ? sec[i].Misc.VirtualSize : sec[i].SizeOfRawData);
    if (sec[i].PointerToRawData + raw > d.size()) raw = d.size() > sec[i].PointerToRawData ? d.size() - sec[i].PointerToRawData : 0;
    if (raw && sec[i].VirtualAddress + raw <= size) memcpy(g_img.data() + sec[i].VirtualAddress, d.data() + sec[i].PointerToRawData, raw);
    g_secs.push_back({sec[i].VirtualAddress, std::max<u32>(sec[i].Misc.VirtualSize, sec[i].SizeOfRawData), (sec[i].Characteristics & IMAGE_SCN_MEM_WRITE) != 0});
  }
  g_fid.assign((size_t)size, 0);
  auto& ed = nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXCEPTION];
  std::vector<std::pair<u32, u32>> fn;
  if (ed.VirtualAddress) { auto* rf = (RUNTIME_FUNCTION*)(g_img.data() + ed.VirtualAddress); for (u32 i = 0; i < ed.Size / sizeof(RUNTIME_FUNCTION); i++) if (rf[i].BeginAddress < rf[i].EndAddress && rf[i].EndAddress <= size) fn.push_back({rf[i].BeginAddress, rf[i].EndAddress}); }
  std::sort(fn.begin(), fn.end()); fn.erase(std::unique(fn.begin(), fn.end()), fn.end());
  for (auto& x : fn) { g_fstart.push_back(x.first); for (u32 a = x.first; a < x.second; a++) g_fid[a] = (u32)g_fstart.size(); }
  // what lies between the functions: one pseudo function per gap (leaf code without unwind data)
  for (u32 a = 0; a < size;) { if (g_fid[a]) { a++; continue; } u32 b = a; while (b < size && !g_fid[b]) b++; g_fstart.push_back(a); for (u32 k = a; k < b; k++) g_fid[k] = (u32)g_fstart.size(); a = b; }
  g_ilen.assign((size_t)size, 0); g_iix.assign((size_t)size, 0);
  ZydisDecoderInit(&g_dec, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_STACK_WIDTH_64);
  return true;
}
static inline u8 insInfo(u32 rva) {
  u8 v = g_ilen[rva]; if (v) return v;
  ZydisDecodedInstruction ins;
  if (rva + 15 <= g_img.size() && ZYAN_SUCCESS(ZydisDecoderDecodeInstruction(&g_dec, nullptr, g_img.data() + rva, 15, &ins))) v = (u8)(ins.length | (ins.mnemonic == ZYDIS_MNEMONIC_CALL ? 0x80 : 0) | (ins.mnemonic == ZYDIS_MNEMONIC_RET ? 0x40 : 0));
  else v = 1;
  return g_ilen[rva] = v;
}
enum { M_SURE = 1, M_TENT, M_SPARSE };
struct Taint;
struct Rec {
  int mode = 0; u32 fn = 0, entry = 0; FILE* f = nullptr; std::string buf, path; std::vector<u32> rvas;
  u64 own = 0, unitOwn = 0, lastLine = 0, lastNovel = 0, entryRsp = 0, startLine = 0; bool unit = false, fresh = false, counted = false;
  std::vector<std::pair<u64, u32>> rd; bool rdAll = false; Taint* t = nullptr;
};
struct Taint;
struct Frame { u32 fn; u64 entryRsp; Rec* rec; Taint* t = nullptr; u64 lastOwn = 0; bool lastCall = false; };
static u64 g_tb = 0, g_cap = 3000000, g_window = 200, g_tentCap = 24u << 20; static u32 g_per = 2, g_maxSeg = 10;
static std::string g_out; static const char* g_file = ""; static bool g_taint = true;
static std::vector<u8> g_cov, g_want; static std::vector<u16> g_segs; static std::vector<u64> g_inv, g_ownLines, g_recLines; static std::vector<u32> g_units, g_fragUnits;
static u64 G[16]; static char X[16][40]; static u8 XL[16]; static u64 g_rip = 0, g_line = 0;
static const char* GN[16] = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"};
// ---- static facts of an instruction (shared with unshroud_deob)
static std::deque<InsInfo> g_ii;
static inline const InsInfo& iiAt(u32 rva) {
  u32& ix = g_iix[rva];
  if (!ix) { g_ii.emplace_back(); ix = (u32)g_ii.size(); insinfo::decodeIns(g_dec, g_img.data() + rva, g_img.size() - rva, g_ii.back()); }
  return g_ii[ix - 1];
}
static inline int hx1(char c) { return c <= '9' ? c - '0' : (c | 32) - 'a' + 10; }
static inline u64 le(const char* h, u32 n) { u64 v = 0; for (u32 k = n; k-- > 0;) v = v * 256 + (u64)(hx1(h[2 * k]) * 16 + hx1(h[2 * k + 1])); return v; }
template <class F> static inline void eachAcc(const char* a, const char* ae, F f) {     // f(address, length, hex text)
  while (a && a < ae) {
    const char* semi = (const char*)memchr(a, ';', (size_t)(ae - a)); if (!semi) semi = ae;
    const char* colon = (const char*)memchr(a, ':', (size_t)(semi - a));
    if (colon) { const char* q = a + 2; const u64 addr = hexv(q, colon); f(addr, (u32)((semi - colon - 1) / 2), colon + 1); }
    a = semi + 1;
  }
}
// ---- what is a constant of the recorded path: per frame, the registers / flags / memory bytes which depend on no input
// of the invocation (entry registers, memory it did not write, results of calls, cpuid / rdtsc). A frag unit starts
// with that knowledge: unshroud_deob then knows the keys the function set up long before.
struct TPage { u8 st[4096]; u8 val[4096]; };       // st: 0 not seen, 1 constant, 2 depends on inputs
static std::vector<TPage*> g_tpool; static u32 g_taintFar = 8192;
struct Taint {
  u32 rsym = 0xffffffffu & ~(1u << 4); u8 fsym = 0x7f; std::unordered_map<u64, TPage*> pages; u64 lastPn = ~0ull; TPage* last = nullptr; u32 nFar = 0;
  u64 callG[16] = {}; u64 lo = 0, hi = 0;           // [lo, hi): the frame's own stack (always followed; other pages up to g_taintFar)
};
static Taint* newTaint(u64 rsp) { Taint* t = new Taint; t->lo = rsp - 0x400000; t->hi = rsp + 0x10000; return t; }
static void freeTaint(Taint* t) { if (!t) return; for (auto& kv : t->pages) g_tpool.push_back(kv.second); delete t; }
static inline TPage* tpage(Taint& t, u64 a, bool make) {
  const u64 pn = a >> 12; if (pn == t.lastPn) return t.last;
  auto it = t.pages.find(pn); TPage* p = it == t.pages.end() ? nullptr : it->second;
  if (!p && make) {
    if (!(a >= t.lo && a < t.hi)) { if (t.nFar >= g_taintFar) return nullptr; t.nFar++; }
    if (!g_tpool.empty()) { p = g_tpool.back(); g_tpool.pop_back(); } else p = new TPage;
    memset(p->st, 0, 4096); t.pages[pn] = p;
  }
  if (p) { t.lastPn = pn; t.last = p; }
  return p;
}
static inline bool roAddrT(u64 a) {
  if (a < g_tb || a >= g_tb + g_img.size()) return false; const u32 r = (u32)(a - g_tb);
  for (auto& s : g_secs) if (r >= s.rva && r < s.rva + s.size) return !s.w;
  return true;
}
// back in the frame after lines of other frames or a call out of the module
static void taintResume(Taint& t, bool wasCall) {
  if (wasCall) { for (int r = 0; r < 16; r++) if (r != 4 && (r == 0 || G[r] != t.callG[r])) t.rsym |= 1u << r; t.rsym |= 0x3fu << 16; }
  else t.rsym = 0xffffffffu & ~(1u << 4);
  t.fsym = 0x7f;
}
static void taintApply(Taint& t, const InsInfo& s, const char* mr, const char* mre, const char* mw, const char* mwe) {
  bool sym = (s.rd & t.rsym) != 0 || (s.rdF & t.fsym) != 0;
  eachAcc(mr, mre, [&](u64 addr, u32 len, const char* h) {
    if (roAddrT(addr) && roAddrT(addr + len - 1)) return;
    for (u32 i = 0; i < len; i++) {
      const u8 b = (u8)(hx1(h[2 * i]) * 16 + hx1(h[2 * i + 1])); TPage* p = tpage(t, addr + i, true); if (!p) { sym = true; continue; }
      const u32 o = (u32)((addr + i) & 4095); if (p->st[o] == 1 && p->val[o] == b) continue;
      sym = true; p->st[o] = 2; p->val[o] = b;
    } });
  const bool call = s.kind == insinfo::K_CALL || s.kind == insinfo::K_CALLI || s.kind == insinfo::K_TRAP;
  if (s.kind == insinfo::K_ENV) sym = true;
  eachAcc(mw, mwe, [&](u64 addr, u32 len, const char* h) {
    for (u32 i = 0; i < len; i++) { TPage* p = tpage(t, addr + i, true); if (!p) continue; const u32 o = (u32)((addr + i) & 4095); p->st[o] = (sym && !call) ? 2 : 1; p->val[o] = (u8)(hx1(h[2 * i]) * 16 + hx1(h[2 * i + 1])); } });
  if (sym) { t.rsym |= s.wr; t.fsym |= s.wrF; } else { t.rsym &= ~s.wr; t.fsym &= (u8)~s.wrF; }
  if (call) memcpy(t.callG, G, sizeof t.callG);
}
// the constant bytes, as "#const addr:len;..." lines
static void dumpConst(std::string& o, Taint& t) {
  std::vector<u64> pns; pns.reserve(t.pages.size()); for (auto& kv : t.pages) pns.push_back(kv.first); std::sort(pns.begin(), pns.end());
  u64 ra = 0, rl = 0; u32 inLine = 0, total = 0; char b[48];
  auto flush = [&]() { if (!rl) return; if (!inLine) o += "#const "; snprintf(b, sizeof b, "%llx:%llx;", (unsigned long long)ra, (unsigned long long)rl); o += b; rl = 0; total++; if (++inLine >= 256) { o += "\n"; inLine = 0; } };
  for (u64 pn : pns) { TPage* p = t.pages[pn]; if (total > 400000) break;
    for (u32 i = 0; i < 4096; i++) { if (p->st[i] != 1) continue; const u64 a = (pn << 12) + i; if (rl && a == ra + rl) rl++; else { flush(); ra = a; rl = 1; } } }
  flush(); if (inLine) o += "\n";
}
// ---- events: transfers into the module's code which no instruction asked for (a fault and its handler, a callback),
// and blocks of memory copied by the module's code (private copies of images)
static FILE* g_evf = nullptr; static std::map<std::string, std::pair<u64, std::string>> g_ev;
static void evCount(const char* key) { auto& e = g_ev[key]; if (!e.first++) { char b[96]; snprintf(b, sizeof b, "%s:%llu", g_file, (unsigned long long)g_line); e.second = b; } }
struct Hnd { bool on = false, fromCb = false; u64 entryRsp = 0, rcx0 = 0, rec = 0, ctx = 0, newRip = 0, target = 0; u32 site = 0, handler = 0, code = 0; bool haveCode = false; };
struct CopyRun { u64 dst = 0, src = 0, len = 0, line = 0; u32 rip = 0; };
static Hnd g_hnd; static CopyRun g_cr; static u64 g_lrAddr = 0; static u32 g_lrLen = 0; static char g_lrHex[160]; static u64 g_prevTarget = 0;
static void flushCopy() { if (g_cr.len >= 256 && g_evf) fprintf(g_evf, "C %s %llu dst=%llx src=%llx len=%llx rip=%x\n", g_file, (unsigned long long)g_cr.line, (unsigned long long)g_cr.dst, (unsigned long long)g_cr.src, (unsigned long long)g_cr.len, g_cr.rip); g_cr.len = 0; }
static void events(u32 rva, u64 rip, u64 rsp, u32 prevRva, u64 prevRip, u64 prevRsp, const char* mr, const char* mre, const char* mw, const char* mwe) {
  const InsInfo& ii = iiAt(rva);
  if (g_hnd.on) {
    Hnd& h = g_hnd;
    if (rsp > h.entryRsp) { h.on = false; }
    if (!h.on && !(h.fromCb && !h.haveCode)) { char k[256]; snprintf(k, sizeof k, "F site=%x target=%llx handler=%x code=%x ctxrip=%llx next=%x", h.site, (unsigned long long)h.target, h.handler, h.code, (unsigned long long)h.newRip, rva); evCount(k); }
    else if (h.on) {
      eachAcc(mr, mre, [&](u64 a, u32 len, const char* hex) {
        if (a == h.rcx0 && len == 8 && !h.rec) h.rec = le(hex, 8); else if (a == h.rcx0 + 8 && len == 8 && !h.ctx) h.ctx = le(hex, 8);
        else if (h.rec && a == h.rec && len >= 4 && !h.haveCode) { h.code = (u32)le(hex, 4); h.haveCode = true; } });
      eachAcc(mw, mwe, [&](u64 a, u32 len, const char* hex) { if (h.ctx && a == h.ctx + 0xf8 && len == 8) h.newRip = le(hex, 8); });
    }
  }
  if (prevRva != ~0u) {
    const InsInfo& ps = iiAt(prevRva); const u64 fall = prevRip + ps.len; char kind = 0;
    if (ps.kind == insinfo::K_CALLI || ps.kind == insinfo::K_JMPI) { if (rip != g_prevTarget && rip != fall) kind = g_prevTarget >= (1ull << 47) ? 'F' : 'B'; }
    else if (ps.kind == insinfo::K_OTHER || ps.kind == insinfo::K_ENV || ps.kind == insinfo::K_TRAP) { if (rip != fall && !(ps.rep && rip == prevRip)) kind = 'F'; }
    if (kind == 'B' && rsp >= prevRsp) kind = 0;
    if ((kind == 'F' || kind == 'B') && (!g_hnd.on || (g_hnd.fromCb && !g_hnd.haveCode))) { g_hnd = Hnd(); g_hnd.fromCb = kind == 'B'; g_hnd.on = true; g_hnd.entryRsp = rsp; g_hnd.rcx0 = G[1]; g_hnd.site = prevRva; g_hnd.target = (ps.kind == insinfo::K_CALLI || ps.kind == insinfo::K_JMPI) ? g_prevTarget : 0; g_hnd.handler = rva; }
    if (kind == 'B') { char k[160]; snprintf(k, sizeof k, "B site=%x target=%llx entry=%x", prevRva, (unsigned long long)g_prevTarget, rva); evCount(k); }
  }
  if (ii.kind == insinfo::K_CALLI || ii.kind == insinfo::K_JMPI) {
    g_prevTarget = 0;
    if (ii.tgReg < 16) g_prevTarget = G[ii.tgReg];
    else { bool got = false; eachAcc(mr, mre, [&](u64, u32 len, const char* hex) { if (!got && len == 8) { g_prevTarget = le(hex, 8); got = true; } }); }
  }
  // copies: a store of the bytes just loaded, run after run
  if (mw) {
    const char* colon = (const char*)memchr(mw, ':', (size_t)(mwe - mw)); const char* semi = (const char*)memchr(mw, ';', (size_t)(mwe - mw)); if (!semi) semi = mwe;
    if (colon && colon < semi) {
      const char* q = mw + 2; const u64 wa = hexv(q, colon); const u32 wl = (u32)((semi - colon - 1) / 2); u64 src = 0; bool found = false;
      eachAcc(mr, mre, [&](u64 a, u32 len, const char* hex) { if (!found && len == wl && a != wa && !memcmp(hex, colon + 1, 2 * wl)) { src = a; found = true; } });
      if (!found && g_lrLen == wl && wl <= 64 && g_lrAddr != wa && !memcmp(g_lrHex, colon + 1, 2 * wl)) { src = g_lrAddr; found = true; }
      if (found) { if (g_cr.len && wa == g_cr.dst + g_cr.len && src == g_cr.src + g_cr.len) g_cr.len += wl; else { flushCopy(); g_cr.dst = wa; g_cr.src = src; g_cr.len = wl; g_cr.line = g_line; g_cr.rip = rva; } }
    }
  }
  if (mr) {
    const char* colon = (const char*)memchr(mr, ':', (size_t)(mre - mr)); const char* semi = (const char*)memchr(mr, ';', (size_t)(mre - mr));
    if (colon && !semi && mre - colon - 1 <= 128) { const char* q = mr + 2; g_lrAddr = hexv(q, colon); g_lrLen = (u32)((mre - colon - 1) / 2); memcpy(g_lrHex, colon + 1, (size_t)(mre - colon - 1)); } else g_lrLen = 0;
  }
}
static inline bool cov(u32 rva) { return (g_cov[rva >> 3] >> (rva & 7)) & 1; }
static inline void setCov(u32 rva) { g_cov[rva >> 3] |= (u8)(1u << (rva & 7)); }
static void put(Rec* r, const char* p, size_t n) { if (r->f) fwrite(p, 1, n, r->f); else r->buf.append(p, n); }
static void beginUnit(Rec* r, bool frag, u32 rva) {
  char b[256]; const std::string base = g_file;
  int n = snprintf(b, sizeof b, "#seg func=%x entry=%x frag=%d file=%s line=%llu rsp=%llx", g_fstart[r->fn], rva, frag ? 1 : 0, g_file, (unsigned long long)g_line, (unsigned long long)(frag ? G[4] : r->entryRsp));
  if (frag && r->t) n += snprintf(b + n, sizeof b - n, " frame=%llx creg=%x cfl=%x", (unsigned long long)r->entryRsp, ~r->t->rsym, (unsigned)(~r->t->fsym & 0x7f));
  b[n++] = 10;
  if (frag && !r->f) { char pth[512]; snprintf(pth, sizeof pth, "%s/%x_frag.seg", g_out.c_str(), g_fstart[r->fn]); r->f = fopen(pth, "ab"); if (r->f) setvbuf(r->f, nullptr, _IOFBF, 1 << 16); g_fragUnits[r->fn]++; }
  else if (frag) g_fragUnits[r->fn]++;
  put(r, b, (size_t)n); r->unit = true; r->fresh = true; r->unitOwn = 0; r->rd.clear(); r->rdAll = false;
  if (frag && r->t) { std::string o; dumpConst(o, *r->t); put(r, o.data(), o.size()); }
}
static void endUnit(Rec* r, const char* why) {
  if (!r->unit) return;
  char b[96]; int n = snprintf(b, sizeof b, "#end reason=%s own=%llu\n", why, (unsigned long long)r->unitOwn);
  put(r, b, (size_t)n); r->unit = false;
}
// the line, as it is or with every register (the first of a unit, and after lines were left out)
static void writeLine(Rec* r, const char* s, const char* e, const char* mr, const char* mre, const char* mw, const char* mwe) {
  const u64 skipped = r->fresh ? 0 : g_line - r->lastLine - 1;
  if (r->fresh || skipped) {
    std::string o; char b[64];
    if (skipped) {
      o += "#gap n=" + std::to_string(skipped) + " rd=";
      if (r->rdAll) o += "*";
      else { std::sort(r->rd.begin(), r->rd.end()); u64 ca = 0, cl = 0; bool have = false;
        for (auto& x : r->rd) { if (have && x.first <= ca + cl) { cl = std::max(cl, x.first + x.second - ca); continue; } if (have) { snprintf(b, sizeof b, "%llx:%llx;", (unsigned long long)ca, (unsigned long long)cl); o += b; } ca = x.first; cl = x.second; have = true; }
        if (have) { snprintf(b, sizeof b, "%llx:%llx;", (unsigned long long)ca, (unsigned long long)cl); o += b; } }
      o += "\n"; r->rd.clear(); r->rdAll = false;
    }
    for (int i = 0; i < 16; i++) { snprintf(b, sizeof b, "%s=0x%llx,", GN[i], (unsigned long long)G[i]); o += b; }
    for (int i = 0; i < 16; i++) { snprintf(b, sizeof b, "xmm%d=", i); o += b; o.append(X[i], XL[i]); o += ","; }
    snprintf(b, sizeof b, "rip=0x%llx", (unsigned long long)g_rip); o += b;
    if (mr) { o += ",mr="; o.append(mr, (size_t)(mre - mr)); }
    if (mw) { o += ",mw="; o.append(mw, (size_t)(mwe - mw)); }
    o += "\n"; put(r, o.data(), o.size());
  } else { put(r, s, (size_t)(e - s)); put(r, "\n", 1); }
  r->fresh = false; r->lastLine = g_line; r->unitOwn++; g_recLines[r->fn]++;
}
static void finish(Rec* r, const char* why) {
  if (!r) return;
  if (r->mode == M_TENT) { g_recLines[r->fn] -= r->unitOwn; delete r; return; }                 // nothing new in it: dropped
  endUnit(r, why); if (r->f) fclose(r->f); delete r;
}
static void popFrame(std::vector<Frame>& st, const char* why) { finish(st.back().rec, why); freeTaint(st.back().t); st.pop_back(); }
static void ownLine(Rec* r, u32 rva, const char* s, const char* e, const char* mr, const char* mre, const char* mw, const char* mwe) {
  r->own++; const bool novel = !cov(rva);
  if (r->mode == M_SURE) {
    if (r->own > g_cap) { endUnit(r, "cap"); r->mode = M_SPARSE; }
    else { writeLine(r, s, e, mr, mre, mw, mwe); setCov(rva); return; }
  }
  if (r->mode == M_TENT) {
    writeLine(r, s, e, mr, mre, mw, mwe); r->rvas.push_back(rva);
    if (novel) {
      char pth[512]; snprintf(pth, sizeof pth, "%s/%x_%u.seg", g_out.c_str(), g_fstart[r->fn], (unsigned)g_segs[r->fn]++);
      r->f = fopen(pth, "wb"); if (r->f) { setvbuf(r->f, nullptr, _IOFBF, 1 << 20); fwrite(r->buf.data(), 1, r->buf.size(), r->f); }
      r->buf.clear(); r->buf.shrink_to_fit(); for (u32 a : r->rvas) setCov(a); r->rvas.clear(); r->rvas.shrink_to_fit(); r->mode = M_SURE; g_units[r->fn]++;
    } else if (r->buf.size() > g_tentCap) { g_recLines[r->fn] -= r->unitOwn; r->buf.clear(); r->buf.shrink_to_fit(); r->rvas.clear(); r->rvas.shrink_to_fit(); r->unit = false; r->mode = M_SPARSE; }
    return;
  }
  // M_SPARSE: only stretches around instructions no segment holds
  if (novel) { if (!r->unit) beginUnit(r, true, rva); writeLine(r, s, e, mr, mre, mw, mwe); setCov(rva); r->lastNovel = r->own; }
  else if (r->unit) { if (r->own - r->lastNovel <= g_window) writeLine(r, s, e, mr, mre, mw, mwe); else endUnit(r, "sparse"); }
}
static Rec* newRec(u32 fn, u32 rva, u64 rsp, Taint* t) {
  if (!g_want[fn]) return nullptr;
  Rec* r = new Rec; r->t = t; r->fn = fn; r->entry = rva; r->entryRsp = rsp; r->startLine = g_line;
  if (g_segs[fn] < g_per) {
    r->mode = M_SURE; char pth[512]; snprintf(pth, sizeof pth, "%s/%x_%u.seg", g_out.c_str(), g_fstart[fn], (unsigned)g_segs[fn]++);
    r->f = fopen(pth, "wb"); if (r->f) setvbuf(r->f, nullptr, _IOFBF, 1 << 20); g_units[fn]++; beginUnit(r, false, rva);
  } else if (g_segs[fn] < g_maxSeg) { r->mode = M_TENT; beginUnit(r, false, rva); }
  else r->mode = M_SPARSE;
  return r;
}
static inline int gprIndex(const char* p, size_t n) {
  if (n == 3) { switch (p[1]) {
    case 'a': return 0; case 'c': return 1; case 'b': return p[2] == 'x' ? 3 : 5; case 's': return p[2] == 'p' ? 4 : 6;
    case 'd': return p[2] == 'x' ? 2 : 7; case '1': return 10 + (p[2] - '0'); default: return -1; } }
  if (n == 2 && (p[1] == '8' || p[1] == '9')) return p[1] - '0';
  return -1;
}
int main(int argc, char** argv) {
  if (argc < 5) { fprintf(stderr, "usage: unshroud_tseg pe tracebase outdir [--funcs a,b] [--per N] [--max-seg N] [--cap N] [--lines N] [--state file] trace...\n"); return 1; }
  u64 isize = 0; if (!loadImage(argv[1], isize)) { fprintf(stderr, "cannot load %s\n", argv[1]); return 1; }
  g_tb = strtoull(argv[2], nullptr, 16); g_out = argv[3];
  const size_t nf = g_fstart.size();
  g_cov.assign((size_t)isize / 8 + 1, 0); g_want.assign(nf, 1); g_segs.assign(nf, 0); g_inv.assign(nf, 0); g_ownLines.assign(nf, 0); g_recLines.assign(nf, 0); g_units.assign(nf, 0); g_fragUnits.assign(nf, 0);
  u64 maxLines = ~0ull; std::string statePath; std::vector<const char*> files; bool events_on = true;
  for (int i = 4; i < argc; i++) {
    if (!strcmp(argv[i], "--funcs")) { std::fill(g_want.begin(), g_want.end(), 0); std::string s = argv[++i]; size_t k = 0; while (k < s.size()) { size_t j = s.find(',', k); if (j == std::string::npos) j = s.size(); const u64 a = strtoull(s.substr(k, j - k).c_str(), nullptr, 16); if (a < isize) g_want[g_fid[a] - 1] = 1; k = j + 1; } }
    else if (!strcmp(argv[i], "--per")) g_per = (u32)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--max-seg")) g_maxSeg = (u32)atoi(argv[++i]);
    else if (!strcmp(argv[i], "--cap")) g_cap = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--lines")) maxLines = strtoull(argv[++i], nullptr, 0);
    else if (!strcmp(argv[i], "--state")) statePath = argv[++i];
    else if (!strcmp(argv[i], "--no-const")) g_taint = false;
    else if (!strcmp(argv[i], "--no-events")) events_on = false;
    else files.push_back(argv[i]);
  }
  if (!statePath.empty()) if (FILE* f = fopen(statePath.c_str(), "rb")) {
    u64 n1 = 0, n2 = 0; fread(&n1, 8, 1, f); fread(&n2, 8, 1, f);
    if (n1 == g_cov.size() && n2 == nf) { fread(g_cov.data(), 1, g_cov.size(), f); fread(g_segs.data(), 2, nf, f); }
    fclose(f);
  }
  if (events_on) g_evf = fopen((g_out + "/events.txt").c_str(), "ab");
  std::vector<char> buf((size_t)64 << 20);
  for (const char* path : files) {
    FILE* f = fopen(path, "rb"); if (!f) { fprintf(stderr, "cannot open %s\n", path); continue; }
    { const char* b1 = strrchr(path, '/'); const char* b2 = strrchr(path, 92); g_file = b1 > b2 ? b1 + 1 : b2 ? b2 + 1 : path; }
    memset(G, 0, sizeof G); for (int i = 0; i < 16; i++) { strcpy(X[i], "0x0"); XL[i] = 3; }
    std::vector<Frame> st; g_line = 0; u32 prevRva = ~0u; u64 prevRip = 0, prevRsp = 0, retTo = 0; bool retPop = false;
    size_t keep = 0; bool eof = false; u64 bytes = 0;
    while (!eof && g_line < maxLines) {
      size_t n = fread(buf.data() + keep, 1, buf.size() - keep, f); size_t total = keep + n; bytes += n;
      if (!n) { eof = true; if (!total) break; buf[total++] = '\n'; }
      size_t start = 0;
      for (;;) {
        char* nl = (char*)memchr(buf.data() + start, '\n', total - start); if (!nl) break;
        const char* s = buf.data() + start; const char* e = nl; start = (size_t)(nl - buf.data()) + 1;
        if (e > s && e[-1] == '\r') e--;
        if (++g_line > maxLines) break;
        const char* p = s; const char *mr = nullptr, *mre = nullptr, *mw = nullptr, *mwe = nullptr; bool haveRip = false;
        while (p < e) {
          const char* eq = (const char*)memchr(p, '=', (size_t)(e - p)); if (!eq) break;
          const char* ce = (const char*)memchr(eq, ',', (size_t)(e - eq)); if (!ce) ce = e;
          const size_t ln = (size_t)(eq - p);
          if (p[0] == 'r') {
            if (ln == 3 && p[1] == 'i') { const char* q = eq + 3; g_rip = hexv(q, ce); haveRip = true; }
            else { const int gi = gprIndex(p, ln); if (gi >= 0) { const char* q = eq + 3; G[gi] = hexv(q, ce); } }
          } else if (p[0] == 'x') { const int xi = atoi(p + 3) & 15; const size_t vl = std::min<size_t>((size_t)(ce - eq - 1), 39); memcpy(X[xi], eq + 1, vl); XL[xi] = (u8)vl; }
          else if (p[0] == 'm' && ln == 2) { if (p[1] == 'r') { mr = eq + 1; mre = ce; } else if (p[1] == 'w') { mw = eq + 1; mwe = ce; } }
          p = ce + 1;
        }
        if (!haveRip) continue;
        const u64 rip = g_rip, rsp = G[4];
        if (rip < g_tb || rip >= g_tb + isize) { prevRva = ~0u; prevRip = rip; continue; }
        const u32 rva = (u32)(rip - g_tb); const u32 fn = g_fid[rva] - 1;
        if (g_evf) events(rva, rip, rsp, prevRva, prevRip, prevRsp, mr, mre, mw, mwe);
        bool prevCall = false; u64 prevFall = 0;
        if (prevRva != ~0u) { const u8 ii = insInfo(prevRva); prevCall = ii & 0x80; prevFall = prevRip + (ii & 0x3f); }
        bool reenter = false;
        if (retPop && !st.empty()) { const u64 pe = st.back().entryRsp; popFrame(st, "ret"); reenter = retTo != 0 && rip != retTo && rsp <= pe; }   // (above it: back in a frame below, through code that is not traced)
        retPop = false;
        while (!st.empty() && rsp > st.back().entryRsp) { popFrame(st, "ret"); }
        bool push = reenter;
        if (st.empty()) push = true;
        else if (prevCall && rip != prevFall) push = true;
        else if (fn != st.back().fn) {
          int k = -1;
          for (int j = (int)st.size() - 2, d = 0; j >= 0 && d < 8; j--, d++) if (st[j].fn == fn && rsp <= st[j].entryRsp) { k = j; break; }
          if (k >= 0) { while ((int)st.size() - 1 > k) { popFrame(st, "tail"); } }
          else { if (rsp >= st.back().entryRsp) { popFrame(st, "tail"); } push = true; }
        }
        if (push) { g_inv[fn]++; st.push_back({fn, rsp, nullptr}); Frame& nf = st.back(); nf.t = g_taint ? newTaint(rsp) : nullptr; nf.rec = newRec(fn, rva, rsp, nf.t); if (!nf.rec) { freeTaint(nf.t); nf.t = nullptr; } }
        Frame& fr = st.back(); g_ownLines[fn]++;
        const InsInfo& ii = iiAt(rva);
        if (fr.t && fr.lastOwn && (fr.lastCall || g_line != fr.lastOwn + 1)) taintResume(*fr.t, fr.lastCall);
        if (fr.rec) ownLine(fr.rec, rva, s, e, mr, mre, mw, mwe);
        if (fr.t) taintApply(*fr.t, ii, mr, mre, mw, mwe);
        fr.lastOwn = g_line; fr.lastCall = ii.kind == insinfo::K_CALL || ii.kind == insinfo::K_CALLI || ii.kind == insinfo::K_TRAP;
        // what this line reads of the frames below it: noted for their open units
        if (mr && st.size() > 1) {
          const char* a = mr;
          while (a < mre) {
            const char* semi = (const char*)memchr(a, ';', (size_t)(mre - a)); if (!semi) semi = mre;
            const char* colon = (const char*)memchr(a, ':', (size_t)(semi - a));
            if (colon) { const char* q = a + 2; const u64 addr = hexv(q, colon); const u32 len = (u32)((semi - colon - 1) / 2);
              if (addr > fr.entryRsp && addr < st.front().entryRsp + 0x28)
                for (int j = (int)st.size() - 2; j >= 0; j--) if (addr < st[j].entryRsp + 0x28) { Rec* r = st[j].rec; if (r && r->unit) { if (!r->rd.empty() && r->rd.back().first + r->rd.back().second == addr) r->rd.back().second += len; else if (!r->rd.empty() && r->rd.back().first == addr && r->rd.back().second >= len) {} else if (r->rd.size() < 65536) r->rd.push_back({addr, len}); else r->rdAll = true; } break; } }
            a = semi + 1;
          }
        }
        if ((insInfo(rva) & 0x40) && !st.empty() && rsp == st.back().entryRsp) {
          retPop = true; retTo = 0;
          if (mr) { const char* c = (const char*)memchr(mr, ':', (size_t)(mre - mr)); if (c && mre - c >= 17) for (int k = 7; k >= 0; k--) { const char* h = c + 1 + 2 * k; retTo = retTo * 256 + (u64)((h[0] <= '9' ? h[0] - '0' : (h[0] | 32) - 'a' + 10) * 16 + (h[1] <= '9' ? h[1] - '0' : (h[1] | 32) - 'a' + 10)); } }
        }
        prevRva = rva; prevRip = rip; prevRsp = rsp;
      }
      keep = total - start; if (keep == buf.size()) buf.resize(buf.size() * 2);
      memmove(buf.data(), buf.data() + start, keep);
    }
    while (!st.empty()) popFrame(st, "eof");
    flushCopy(); g_hnd.on = false; g_lrLen = 0;
    fclose(f);
    fprintf(stderr, "%s: %llu lines, %.1f MB\n", g_file, (unsigned long long)g_line, bytes / 1048576.0); fflush(stderr);
  }
  if (!statePath.empty()) if (FILE* f = fopen(statePath.c_str(), "wb")) { u64 n1 = g_cov.size(), n2 = nf; fwrite(&n1, 8, 1, f); fwrite(&n2, 8, 1, f); fwrite(g_cov.data(), 1, g_cov.size(), f); fwrite(g_segs.data(), 2, nf, f); fclose(f); }
  if (g_evf) { for (auto& kv : g_ev) fprintf(g_evf, "%s n=%llu first=%s\n", kv.first.c_str(), (unsigned long long)kv.second.first, kv.second.second.c_str()); fclose(g_evf); }
  for (size_t i = 0; i < nf; i++) if (g_inv[i]) printf("%x inv %llu own %llu rec %llu units %u frags %u\n", g_fstart[i], (unsigned long long)g_inv[i], (unsigned long long)g_ownLines[i], (unsigned long long)g_recLines[i], g_units[i], g_fragUnits[i]);
  return 0;
}
