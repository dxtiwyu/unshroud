// unshroud - engine: memory, decoding, blocks, run loop
#include "engine.hpp"
#include "jit.hpp"
#include <Zydis/Zydis.h>
#include <cstdio>
#include <intrin.h>
#include <cstdlib>
#include <atomic>

namespace unshroud {

struct RegDesc { u8 rk, idx, off, size; };
static RegDesc regmap[ZYDIS_REGISTER_MAX_VALUE + 1];
static bool regmapReady = false;

static void initRegmap() {
  if (regmapReady) return;
  for (int r = 0; r <= ZYDIS_REGISTER_MAX_VALUE; r++) {
    ZydisRegister zr = (ZydisRegister)r;
    RegDesc d{RK_OTHER, 0, 0, 0};
    ZydisRegisterClass cls = ZydisRegisterGetClass(zr);
    auto gprId = [&](ZydisRegister x) { ZydisRegister big = ZydisRegisterGetLargestEnclosing(ZYDIS_MACHINE_MODE_LONG_64, x); return (int)ZydisRegisterGetId(big); };
    switch (cls) {
    case ZYDIS_REGCLASS_GPR64: d = {RK_GPR, (u8)ZydisRegisterGetId(zr), 0, 8}; break;
    case ZYDIS_REGCLASS_GPR32: d = {RK_GPR, (u8)gprId(zr), 0, 4}; break;
    case ZYDIS_REGCLASS_GPR16: d = {RK_GPR, (u8)gprId(zr), 0, 2}; break;
    case ZYDIS_REGCLASS_GPR8:
      if (zr == ZYDIS_REGISTER_AH) d = {RK_GPR, 0, 1, 1};
      else if (zr == ZYDIS_REGISTER_CH) d = {RK_GPR, 1, 1, 1};
      else if (zr == ZYDIS_REGISTER_DH) d = {RK_GPR, 2, 1, 1};
      else if (zr == ZYDIS_REGISTER_BH) d = {RK_GPR, 3, 1, 1};
      else d = {RK_GPR, (u8)gprId(zr), 0, 1};
      break;
    case ZYDIS_REGCLASS_XMM: d = {RK_VEC, (u8)ZydisRegisterGetId(zr), 0, 16}; break;
    case ZYDIS_REGCLASS_YMM: d = {RK_VEC, (u8)ZydisRegisterGetId(zr), 0, 32}; break;
    case ZYDIS_REGCLASS_IP: d = {RK_RIP, 16, 0, 8}; break;
    case ZYDIS_REGCLASS_SEGMENT: {   // idx: es cs ss ds fs gs (what a program reads there: sem.cpp)
      const u8 si = zr == ZYDIS_REGISTER_ES ? 0 : zr == ZYDIS_REGISTER_CS ? 1 : zr == ZYDIS_REGISTER_SS ? 2 : zr == ZYDIS_REGISTER_DS ? 3 : zr == ZYDIS_REGISTER_FS ? 4 : 5;
      d = {zr == ZYDIS_REGISTER_FS ? RK_FS : zr == ZYDIS_REGISTER_GS ? RK_GS : RK_SEG0, si, 0, 2}; break;
    }
    case ZYDIS_REGCLASS_CONTROL: case ZYDIS_REGCLASS_DEBUG: d = {RK_SYS, 0, 0, 8}; break;
    case ZYDIS_REGCLASS_FLAGS: d = {RK_FLAGS, 0, 0, 8}; break;
    default: break;
    }
    if (d.rk == RK_GPR && d.idx >= 16) d.rk = RK_OTHER;        // APX registers
    if (d.rk == RK_VEC && d.idx >= 16) d.rk = RK_OTHER;
    regmap[r] = d;
  }
  regmapReady = true;
}

Engine::Engine() {
  initRegmap();
  auto* dec = new ZydisDecoder;
  ZydisDecoderInit(dec, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_STACK_WIDTH_64);
  decoder = dec;
  flushTlb();
  for (auto& b : bcache) { b.tag = ~0ull; b.b = nullptr; }
  if (const char* e = getenv("UNSHROUD_JIT")) jitOn = *e && *e != 48;
  if (const char* e = getenv("UNSHROUD_JIT_HOT")) jitHot = (u32)atoi(e);
  if (const char* e = getenv("UNSHROUD_NOMARK")) dropMarks = *e && *e != 48;
  if (const char* e = getenv("UNSHROUD_MARK_LIMIT")) markLimit = (u32)strtoul(e, nullptr, 0);
}

Engine::~Engine() {
  if (jit) jitDestroy(jit);
  journalDrop();
  for (auto& kv : pages) { Page* p = kv.second; if (--p->refs == 0) delete p; }
  for (auto& kv : blocks) delete kv.second;
  for (Block* b : graveyard) delete b;
  for (auto& kv : codeBits) delete[] kv.second;
  delete (ZydisDecoder*)decoder;
}

void Engine::flushTlb() { for (auto& e : rtlb) { e.tag = ~0ull; e.p = nullptr; } for (auto& e : wtlb) { e.tag = ~0ull; e.p = nullptr; } if (jit) jitFlushTlb(jit); }
void Engine::jitDropPage(u64 pn) { if (jit) jitDrop(jit, pn); }

// unmapped memory reads as zeros from one shared page (nothing is allocated); a write maps a page, within a budget
static Page* zeroPage() {
  static Page* z = [] { Page* p = new Page(); memset(p->d, 0, 4096); p->refs = 0x40000000; return p; }();
  return z;
}

Page* Engine::pageR(u64 pn) {
  TlbE& e = rtlb[pn & 511];
  if (e.tag == pn) return e.p;
  if (pn < guardPages) return nullptr;
  if (hiFault && (pn >> 35)) return nullptr;
  auto it = pages.find(pn);
  Page* p;
  if (it == pages.end()) {
    if (lazyMem && (inZone(pn << 12) || ucAnywhere) && (p = ucPage(pn))) {}
    else if (!autoMap) return nullptr;
    else p = zeroPage();
  } else p = it->second;
  e.tag = pn; e.p = p;
  return p;
}

// a page of the zone: every word unknown, each holding a pointer to a place of its own in the zone
Page* Engine::ucPage(u64 pn) {
  if (ucPagesMade >= ucMaxPages || pages.size() >= maxPages) return nullptr;
  Page* p = new Page();
  memset(p->d, 0, 4096);                              // (what a word holds is decided when it is first read)
  p->unk = new u64[8]; memset(p->unk, 0xff, 64);
  pages.emplace(pn, p); ucPagesMade++;
  if (baseId) journal.push_back({pn, nullptr});
  return p;
}

// what a call left out would have stored: unknown again whatever it holds now, and an input of the call (key + word) when read
void Engine::markOut(u64 addr, u64 size, OutId id, bool seeded) {
  for (u64 a = addr; a + 8 <= addr + size && (id.word & 255) < 255; a += 8, id.word++) {
    const u64 pn = a >> 12; const unsigned j = (unsigned)((a & 4095) >> 3);
    bool was = autoMap; autoMap = true; Page* p = pageW(pn); autoMap = was;
    if (!p) continue;
    if (seeded && p->sh) { bool any = false; for (int b = 0; b < 8; b++) any |= p->sh[8 * j + b].e != 0; if (any) continue; }   // (an expression is there: kept)
    if (p->sh) for (int b = 0; b < 8; b++) if (p->sh[8 * j + b].e) { p->sh[8 * j + b] = Cell{0, 0}; p->nsym--; }
    if (!p->unk) { p->unk = new u64[8]; memset(p->unk, 0, 64); }
    p->unk[j >> 6] |= 1ull << (j & 63);
    if (p->taint) { delete[] p->taint; p->taint = nullptr; }
    outKey[a] = id;
    if (seeded) outSeed.insert(a); else outSeed.erase(a);
  }
  flushTlb();
}

void Engine::markUnknown(u64 addr, u64 size) {
  for (u64 a = (addr + 7) & ~7ull; a + 8 <= addr + size; a += 8) {
    const u64 pn = a >> 12; const unsigned j = (unsigned)((a & 4095) >> 3);
    bool was = autoMap; autoMap = true; Page* p = pageW(pn); autoMap = was;
    if (!p) continue;
    if (p->sh) { u32 any = 0; for (int b = 0; b < 8; b++) any |= p->sh[8 * j + b].e; if (any) continue; }   // an input already
    if (!p->unk) { p->unk = new u64[8]; memset(p->unk, 0, 64); }
    p->unk[j >> 6] |= 1ull << (j & 63);
    if (p->taint) { delete[] p->taint; p->taint = nullptr; }      // (made again when native code comes; the flush below drops the page there)
  }
  flushTlb();
}

Page* Engine::known(u64 addr, unsigned size) {
  const u64 pn = addr >> 12;
  Page* p = pageW(pn);
  if (!p || !p->unk) return p;
  const bool was = X.lazyOn; X.lazyOn = false;
  const unsigned off = (unsigned)(addr & 4095), w1 = std::min(511u, (off + size - 1) >> 3);
  for (unsigned j = off >> 3; j <= w1; j++) {
    if (!((p->unk[j >> 6] >> (j & 63)) & 1)) continue;
    p->unk[j >> 6] &= ~(1ull << (j & 63));
    if (ucWordsMade >= ucMaxWords) { if (p->taint) taintSet(p, (pn << 12) + 8 * j, 8, false); continue; }     // (plain memory from here on)
    ucWordsMade++;
    const u64 a = (pn << 12) + 8 * j;
    u64 cur; memcpy(&cur, p->d + 8 * j, 8);
    auto ok = outKey.empty() ? outKey.end() : outKey.find(a);
    auto it = ucVars.find(a); u32 idx;
    if (ok != outKey.end()) {
      auto ov = outVars.find(ok->second);
      if (ov == outVars.end()) {
        idx = (u32)X.vars.size(); char name[48]; snprintf(name, sizeof name, "o_%llx_%u_%x", (unsigned long long)ok->second.site, ok->second.occ, ok->second.word);
        X.var(name, 64, outSeed.count(a) ? cur : ucFresh()); outVars.emplace(ok->second, idx);
        if (placesOn && outSeed.count(a) && cur < 0x10000) X.vars[idx].place = placeFresh();
      } else idx = ov->second;
      outKey.erase(ok);
    } else if (it == ucVars.end()) {
      idx = (u32)X.vars.size(); char name[24]; snprintf(name, sizeof name, "m_%llx", (unsigned long long)a);
      X.var(name, 64, inZone(a) || ucSeedZone ? ucFresh() : cur); ucVars.emplace(a, idx);
      if (placesOn && !inZone(a) && cur < 0x10000) X.vars[idx].place = placeFresh();   // (a global which holds 0 or a small number)
    } else idx = it->second;
    const u64 v = runVals && idx < runVals->size() ? (*runVals)[idx] : X.vars[idx].seed;
    if (v != cur) memcpy(p->d + 8 * j, &v, 8);
    if (!p->sh) { p->sh = new Cell[4096]; memset(p->sh, 0, sizeof(Cell) * 4096); }
    const u32 node = X.varNode(idx);
    for (u32 b = 0; b < 8; b++) { if (!p->sh[8 * j + b].e) p->nsym++; p->sh[8 * j + b] = Cell{node, b}; }
    taintSet(p, a, 8, true);
  }
  u64 left = 0; for (int i = 0; i < 8; i++) left |= p->unk[i];
  if (!left) { delete[] p->unk; p->unk = nullptr; }
  X.lazyOn = was;
  return p;
}

void Engine::unkStore(Page* p, u64 addr, unsigned size) {
  const unsigned off = (unsigned)(addr & 4095), end = off + size;
  for (unsigned j = off >> 3; j <= std::min(511u, (end - 1) >> 3) && p->unk; j++) {
    if (!((p->unk[j >> 6] >> (j & 63)) & 1)) continue;
    if (off <= 8 * j && end >= 8 * j + 8) p->unk[j >> 6] &= ~(1ull << (j & 63));     // overwritten whole
    else known((addr & ~4095ull) + 8 * j, 8);                                        // the bytes which stay are an input's
  }
  if (p->unk) { u64 left = 0; for (int i = 0; i < 8; i++) left |= p->unk[i]; if (!left) { delete[] p->unk; p->unk = nullptr; } }
}

// rip is in the zone: an unknown function was called. It returns, rax is an input of its own.
bool Engine::ucCall() {
  u64 ra = 0; readMem(g[RSP], &ra, 8);
  if (ra < 0x10000 || inZone(ra) || !isMapped(ra)) return false;       // nothing to return to: not a call
  const Val v = ucValue(ra, "r");
  g[RAX] = v.c; gs[RAX] = v.s;
  g[RSP] += 8; rip = ra; ucCalls++;
  return true;
}

Val Engine::ucValue(u64 site, const char* what) {
  const bool was = X.lazyOn; X.lazyOn = false;
  const u32 occ = ucSite[site]++;
  const u64 key = site * 0x9E3779B97F4A7C15ull + occ;
  auto it = ucRets.find(key); u32 idx;
  if (it == ucRets.end()) {
    idx = (u32)X.vars.size(); char name[40]; snprintf(name, sizeof name, "%s_%llx_%u", what, (unsigned long long)site, occ);
    X.var(name, 64, ucFresh()); ucRets.emplace(key, idx);
  } else idx = it->second;
  const Val v{runVals && idx < runVals->size() ? (*runVals)[idx] : X.vars[idx].seed, X.varNode(idx)};
  X.lazyOn = was;
  return v;
}

Val Engine::envValue(u64 site, u32 occ, u64 seed, unsigned w) {
  const bool was = X.lazyOn; X.lazyOn = false;
  const u64 key = site * 0x9E3779B97F4A7C15ull + occ;
  auto it = envRets.find(key); u32 idx;
  if (it == envRets.end()) {
    idx = (u32)X.vars.size(); char name[40]; snprintf(name, sizeof name, "e_%llx_%u", (unsigned long long)site, occ);
    X.var(name, w, seed); envRets.emplace(key, idx);
  } else idx = it->second;
  const Val v{(runVals && idx < runVals->size() ? (*runVals)[idx] : X.vars[idx].seed) & maskOf(w), X.varNode(idx)};
  X.lazyOn = was;
  return v;
}

u64 Engine::callBefore(u64 ret) {
  for (auto& kv : blocks) { const Insn& I = kv.second->ins.back(); if (I.next == ret && I.mn == ZYDIS_MNEMONIC_CALL) return I.addr; }
  for (unsigned k : {7u, 6u, 5u, 4u, 3u, 2u}) { const Insn* I = decodeAt(ret - k); if (I && I->mn == ZYDIS_MNEMONIC_CALL && I->len == k) return ret - k; }   // (the longest: with its prefix)
  return 0;
}

void Engine::addHavocSite(u64 a) { if (havocSites.insert(a).second && jit) jitFlushCode(jit); }
void Engine::addForceSite(u64 a) { if (forceSites.insert(a).second && jit) jitFlushCode(jit); }
u64 Engine::forceSwitch(u64 pc, u64 natural) {
  auto it = switchTargets.find(pc);
  if (it == switchTargets.end() || forceSeen[pc]++) return natural;
  u64 k = 0;
  for (u64 t : it->second) {
    if (t == natural) continue;
    if (oracle((pc ^ 0x5377697400000000ull) + (++k << 44), true)) continue;
    if (!havocked && covOn && jit) jitSyncCov(jit, *this);
    havocked++; forced++;
    return t;
  }
  return natural;
}
bool Engine::forceBranch(u64 pc) {
  if (forceSeen[pc]++) return false;                   // (the first time the jump is met in the run)
  if (oracle(pc ^ 0x466f726300000000ull, true)) return false;
  if (!havocked && covOn && jit) jitSyncCov(jit, *this);
  havocked++; forced++;
  return true;
}

bool Engine::havocCall(const Insn& I) {
  if (!oracle(I.addr ^ 0x4856000000000000ull, true)) return false;
  const bool was = X.lazyOn; X.lazyOn = false;
  if (!havocked && covOn && jit) jitSyncCov(jit, *this);      // (what ran before this point did not rest on the assumption)
  const u32 occ = havocSeen[I.addr]++;
  const u64 key = I.addr * 0x9E3779B97F4A7C15ull + occ;
  auto it = havocRets.find(key); u32 idx;
  if (it == havocRets.end()) {
    idx = (u32)X.vars.size(); char name[40]; snprintf(name, sizeof name, "h_%llx_%u", (unsigned long long)I.addr, occ);
    X.var(name, 64, lazyMem ? ucFresh() : 0); havocRets.emplace(key, idx);
  } else idx = it->second;
  g[RAX] = runVals && idx < runVals->size() ? (*runVals)[idx] : X.vars[idx].seed; gs[RAX] = X.varNode(idx);
  rip = I.next; havocked++;
  if (havocOut && lazyMem) for (int r : {RCX, RDX, R8, R9}) {       // what the callee was given to fill, in the caller's frame
    const u64 a = g[r];
    if (!gs[r] && a >= g[RSP] && a < havocTop && !(a & 7)) markOut(a, std::min<u64>(havocOut, havocTop - a), OutId{I.addr, occ, (u16)(r << 8)});
  }
  X.lazyOn = was;
  return true;
}

void Engine::fault(u64 addr, bool write) {
  if (stopInfo == "memory budget") trapKind = TK_NONE;
  else { trapKind = write ? TK_WRITE : TK_READ; trapArg = addr; }
  throw (int)ST_FAULT;
}

Page* Engine::pageW(u64 pn) {
  TlbE& e = wtlb[pn & 511];
  if (e.tag == pn) return e.p;
  if (pn < guardPages) return nullptr;
  if (hiFault && (pn >> 35)) return nullptr;
  auto it = pages.find(pn);
  Page* p;
  if (it == pages.end()) {
    if (lazyMem && (inZone(pn << 12) || ucAnywhere) && (p = ucPage(pn))) {}
    else {
      if (!autoMap) return nullptr;
      if (pages.size() >= maxPages || (runPageLimit && runPages >= runPageLimit)) { stopInfo = "memory budget"; return nullptr; }
      p = new Page(); memset(p->d, 0, 4096); pages.emplace(pn, p); runPages++;
      if (baseId) journal.push_back({pn, nullptr});
      if (!codeBits.empty() && codeBits.count(pn)) p->code = true;
    }
    rtlb[pn & 511] = {pn, p};
    jitDropPage(pn);
  } else p = it->second;
  if (p->refs > 1) {
    if (runPageLimit && runPages >= runPageLimit) { stopInfo = "memory budget"; return nullptr; }
    runPages++;
    Page* q = new Page(); memcpy(q->d, p->d, 4096); q->nsym = p->nsym; q->code = p->code; q->lazy = false;
    if (p->sh) { q->sh = new Cell[4096]; memcpy(q->sh, p->sh, sizeof(Cell) * 4096); }
    if (p->unk) { q->unk = new u64[8]; memcpy(q->unk, p->unk, 64); }
    if (p->taint) { q->taint = new u8[8192]; memcpy(q->taint, p->taint, 8192); }
    if (baseId) journal.push_back({pn, p}); else p->refs--;      // (the list keeps the reference, to put the page back)
    pages[pn] = q; p = q;
    rtlb[pn & 511] = {pn, p};
    jitDropPage(pn);
  }
  e.tag = pn; e.p = p;
  return p;
}

static std::atomic<u64> gStateId{1};
void Engine::journalDrop() { for (auto& e : journal) if (e.second && --e.second->refs == 0) delete e.second; journal.clear(); }

State::~State() { for (auto& kv : pages) if (--kv.second->refs == 0) delete kv.second; }

// every recorded expression the state refers to is built; the tape is emptied
void Engine::settle() {
  if (X.tape.empty()) return;
  for (int r = 0; r < 16; r++) gs[r] = X.force(gs[r]);
  fl.sa = X.force(fl.sa); fl.sb = X.force(fl.sb); fl.sr = X.force(fl.sr); fl.sx = X.force(fl.sx);
  fl.prev.sa = X.force(fl.prev.sa); fl.prev.sb = X.force(fl.prev.sb); fl.prev.sr = X.force(fl.prev.sr); fl.prev.sx = X.force(fl.prev.sx);
  for (u32& e : fl.sym) e = X.force(e);
  for (int r = 0; r < 16; r++) if (vsym & (1u << r)) for (Cell& c : vc[r]) c.e = X.force(c.e);
  for (Page* p : lazyPages) { if (p->sh) for (int i = 0; i < 4096; i++) if (p->sh[i].e >= LAZY_BASE) p->sh[i].e = X.force(p->sh[i].e); p->lazy = false; }
  lazyPages.clear();
  X.lazyReset();
}

std::shared_ptr<State> Engine::snapshot() {
  settle();
  auto st = std::make_shared<State>();
  memcpy(st->g, g, sizeof g); memcpy(st->gs, gs, sizeof gs); st->rip = rip; st->fsbase = fsbase; st->gsbase = gsbase; st->mxcsr = mxcsr;
  st->vsym = vsym; st->fl = fl; memcpy(st->v, v, sizeof v); memcpy(st->vc, vc, sizeof vc);
  st->pages = pages; for (auto& kv : st->pages) kv.second->refs++;
  st->id = gStateId++; journalDrop(); baseId = st->id;      // the engine's table is this state's from here on
  codeTouched = false;                          // (what is decoded now was decoded from this state's code)
  st->path = path; st->icount = icount; st->epoch = epoch;
  flushTlb();                                   // the write TLB must not hand out pages which are now shared
  return st;
}

void Engine::restore(const State& st) {
  memcpy(g, st.g, sizeof g); memcpy(gs, st.gs, sizeof gs); rip = st.rip; fsbase = st.fsbase; gsbase = st.gsbase; mxcsr = st.mxcsr;
  vsym = st.vsym; fl = st.fl; memcpy(v, st.v, sizeof v); memcpy(vc, st.vc, sizeof vc);
  const bool sameState = baseId && st.id == baseId;
  if (sameState) {
    // back to the state the table was last set to: only what changed since, the last change first
    for (size_t i = journal.size(); i-- > 0;) {
      auto it = pages.find(journal[i].first); Page* cur = it->second;
      if (journal[i].second) { if (cur->code) journal[i].second->code = true; it->second = journal[i].second; } else pages.erase(it);
      if (--cur->refs == 0) delete cur;
    }
    journal.clear();
  } else {
    journalDrop();
    for (auto& kv : pages) if (--kv.second->refs == 0) delete kv.second;
    pages = st.pages; for (auto& kv : pages) kv.second->refs++;
    baseId = st.id;
  }
  lazyPages.clear(); X.lazyReset();             // a saved state holds built expressions only
  ucPagesMade = 0; ucWordsMade = 0; ucSite.clear(); pinned.clear(); runPages = 0; markWrites = 0; tf = 0; movSS = 0; ssSel = 0x2b;
  dr[0] = dr[1] = dr[2] = dr[3] = 0; dr7 = 0; drUpdate(); dbHeld = dbStatus = 0; dataHits = 0; rfOnce = 0; dbWatch = false; dbgOn = 0;
  havocSeen.clear(); havocked = 0; outKey.clear(); outSeed.clear(); envSeen.clear(); recWrites.clear(); forceSeen.clear(); forced = 0; covNewRun.clear();
  if (trap) { trapMemo.clear(); softFaults = 0; trapCount = 0; softRetry = 0; guardPages = guardSet; }
  path = st.path; icount = st.icount;
  flushTlb();
  if (!sameState || codeTouched) codeWritten(nullptr);   // another state, or code was written since: what was decoded is stale
  codeTouched = false;
}

void Engine::pokeConcrete(u64 addr, const void* data, size_t size) {
  const u8* s = (const u8*)data;
  while (size) {
    u64 pn = addr >> 12; unsigned off = addr & 4095; size_t n = std::min<size_t>(size, 4096 - off);
    bool was = autoMap; autoMap = true; const u64 gp = guardPages; guardPages = 0; Page* p = pageW(pn); autoMap = was; guardPages = gp;
    if (pn < gp) wtlb[pn & 511].tag = ~0ull, rtlb[pn & 511].tag = ~0ull;
    if (!p) return;                               // the memory budget
    memcpy(p->d + off, s, n);
    if (p->code && codeHit(pn, off, n)) codeWritten(p);
    addr += n; s += n; size -= n;
  }
}

bool Engine::isMapped(u64 addr) { return pages.count(addr >> 12) != 0; }

void Engine::map(u64 addr, u64 size) {
  for (u64 pn = addr >> 12; pn <= (addr + size - 1) >> 12; pn++) {
    if (pages.count(pn)) continue;
    Page* p = new Page(); memset(p->d, 0, 4096); pages.emplace(pn, p);
    if (baseId) journal.push_back({pn, nullptr});
  }
  flushTlb();
}

void Engine::writeMem(u64 addr, const void* data, size_t size) {
  if (recW && size) recWrites.push_back({addr, (u64)size});
  const u8* s = (const u8*)data;
  while (size) {
    u64 pn = addr >> 12; unsigned off = addr & 4095; size_t n = std::min<size_t>(size, 4096 - off);
    bool was = autoMap; autoMap = true; const u64 gp = guardPages; guardPages = 0; Page* p = pageW(pn); autoMap = was; guardPages = gp;
    if (pn < gp) wtlb[pn & 511].tag = ~0ull, rtlb[pn & 511].tag = ~0ull;
    if (!p) return;                               // the memory budget
    if (p->unk) unkStore(p, addr, (unsigned)n);
    memcpy(p->d + off, s, n);
    if (p->sh) for (size_t i = 0; i < n; i++) if (p->sh[off + i].e) { p->sh[off + i].e = 0; p->nsym--; }
    if (p->taint) taintSet(p, addr, (unsigned)n, false);
    if (p->code && codeHit(pn, off, n)) codeWritten(p);
    addr += n; s += n; size -= n;
  }
}

void Engine::readMem(u64 addr, void* out, size_t size) {
  u8* d = (u8*)out;
  while (size) {
    u64 pn = addr >> 12; unsigned off = addr & 4095; size_t n = std::min<size_t>(size, 4096 - off);
    Page* p; TlbE& te = rtlb[pn & 511];
    if (te.tag == pn && te.p != zeroPage()) p = te.p;                     // (the page the interpreter's loads use)
    else {
      auto it = pages.find(pn);
      p = it == pages.end() ? (lazyMem && inZone(addr) ? ucPage(pn) : nullptr) : it->second;
      if (p && pn >= guardPages) { te.tag = pn; te.p = p; }
    }
    if (p && p->unk) { Page* q = known(addr, (unsigned)n); if (q) p = q; }
    if (!p) memset(d, 0, n); else memcpy(d, p->d + off, n);
    addr += n; d += n; size -= n;
  }
}

void Engine::flushBlocks() { codeWritten(nullptr); }

void Engine::markStorm() {
  dropMarks = true;
  for (int r = 0; r < 16; r++) if (gs[r] && gs[r] < LAZY_BASE && X.isC(gs[r])) gs[r] = 0;
}

void Engine::markCode(u64 addr, unsigned len) {
  for (u64 a = addr; a < addr + len;) {
    const u64 pn = a >> 12; const unsigned off = (unsigned)(a & 4095), n = (unsigned)std::min<u64>(addr + len - a, 4096 - off);
    auto it = codeBits.find(pn);
    if (it == codeBits.end()) it = codeBits.emplace(pn, new u64[64]()).first;
    u64* b = it->second; bool fresh = false;
    for (unsigned i = off; i < off + n; i++) { const u64 m = 1ull << (i & 63); if (!(b[i >> 6] & m)) { b[i >> 6] |= m; fresh = true; } }
    if (fresh) {
      Page* p = pageR(pn);
      if (p && p != zeroPage()) {
        p->code = true;
        // native code must see the new marks before its next store there: in the page's bytes if it has them, else the
        // page leaves the table (it gets them when it comes back)
        if (p->taint) memset(p->taint + 4096 + off, 0xff, n); else jitDropPage(pn);
      }
    }
    a += n;
  }
}

void Engine::codeWritten(Page* p) {
  if (p) { codeTouched = true; codeFlushes++; }
  for (auto& kv : codeBits) delete[] kv.second;
  codeBits.clear();
  epoch++;
  if (jit) jitFlushCode(jit);
  for (auto& b : bcache) { b.tag = ~0ull; b.b = nullptr; }
  for (auto& kv : blocks) graveyard.push_back(kv.second);
  blocks.clear();
}

// the expression of n bytes (n <= 8) given their concrete values and cells, byte 0 lowest
u32 cellsExpr(Ctx& X, const u8* bytes, const Cell* cells, unsigned n) {
  u32 acc = 0; int i = (int)n;
  while (i > 0) {
    int hi = i - 1, j = hi; u32 piece;
    if (cells[hi].e == 0) {
      while (j > 0 && cells[j - 1].e == 0) j--;
      u64 c = 0; for (int k = hi; k >= j; k--) c = (c << 8) | bytes[k];
      piece = X.cst(c, 8 * (hi - j + 1));
    } else {
      u32 e = cells[hi].e;
      while (j > 0 && cells[j - 1].e == e && cells[j - 1].off + 1 == cells[j].off) j--;
      piece = X.extract(e, cells[j].off * 8, 8 * (hi - j + 1));
    }
    acc = acc ? X.concat(acc, piece) : piece;
    i = j;
  }
  return acc;
}

void Engine::drUpdate() {
  drExec = drData = drWrOnly = 0;
  for (int i = 0; i < 4; i++) {
    if (!((dr7 >> (2 * i)) & 1)) continue;                   // (local enables: the kernel keeps no global one)
    const unsigned rw = (unsigned)(dr7 >> (16 + 4 * i)) & 3, ln = (unsigned)(dr7 >> (18 + 4 * i)) & 3;
    if (rw == 0) { drExec |= (u8)(1u << i); continue; }
    if (rw == 2) continue;                                   // (I/O)
    const u64 len = ln == 0 ? 1 : ln == 1 ? 2 : ln == 3 ? 4 : 8;   // the address bits below the length do not count
    drLo[i] = dr[i] & ~(len - 1); drHi[i] = drLo[i] + len;
    drData |= (u8)(1u << i); if (rw == 1) drWrOnly |= (u8)(1u << i);
  }
  if (drExec | drData) dbgOn = 1;
}

Val Engine::load(u64 addr, unsigned size) {
  if (dbWatch) dataCheck(addr, size, false);
  unsigned off = addr & 4095;
  if (off + size <= 4096) {
    Page* p = pageR(addr >> 12);
    if (!p) fault(addr, false);
    if (p->unk) { Page* q = known(addr, size); if (q) p = q; }
    u64 c = 0; memcpy(&c, p->d + off, size);
    if (!p->nsym) return {c, 0};
    const Cell* cl = p->sh + off;
    u32 any = 0; for (unsigned i = 0; i < size; i++) any |= cl[i].e;
    if (!any) return {c, 0};
    return {c, cellsExpr(X, p->d + off, cl, size)};
  }
  u8 b[8]; Cell cl[8]; u32 any = 0;
  for (unsigned i = 0; i < size; i++) {
    Page* p = pageR((addr + i) >> 12);
    if (!p) fault(addr + i, false);
    if (p->unk) { Page* q = known(addr + i, 1); if (q) p = q; }
    unsigned o = (addr + i) & 4095;
    b[i] = p->d[o]; cl[i] = p->sh ? p->sh[o] : Cell{0, 0}; any |= cl[i].e;
  }
  u64 c = 0; memcpy(&c, b, size);
  return {c, any ? cellsExpr(X, b, cl, size) : 0};
}

void Engine::store(u64 addr, unsigned size, Val v) {
  if (dbWatch) dataCheck(addr, size, true);
  if (v.s && v.s < LAZY_BASE && plainConst(v.s)) v.s = 0;
  unsigned off = addr & 4095;
  if (off + size <= 4096) {
    Page* p = pageW(addr >> 12);
    if (!p) fault(addr, true);
    if (p->unk) unkStore(p, addr, size);
    memcpy(p->d + off, &v.c, size);
    writeHash = (writeHash ^ addr ^ (v.c * 0x9E3779B97F4A7C15ull) ^ ((u64)v.s << 40) ^ size) * 0xff51afd7ed558ccdull;
    if (v.s) {
      if (!p->sh) { p->sh = new Cell[4096]; memset(p->sh, 0, sizeof(Cell) * 4096); }
      Cell* cl = p->sh + off;
      for (unsigned i = 0; i < size; i++) { if (!cl[i].e) p->nsym++; cl[i] = {v.s, i}; }
      if (v.s >= LAZY_BASE && !p->lazy) { p->lazy = true; lazyPages.push_back(p); }
    } else if (p->nsym) {
      Cell* cl = p->sh + off;
      for (unsigned i = 0; i < size; i++) if (cl[i].e) { cl[i].e = 0; p->nsym--; }
    }
    if (v.s || p->taint) taintSet(p, addr, size, v.s != 0);
    if (p->code && codeHit(addr >> 12, off, size)) codeWritten(p);
    return;
  }
  for (unsigned i = 0; i < size; i++) {
    Page* p = pageW((addr + i) >> 12);
    if (!p) fault(addr + i, true);
    if (p->unk) unkStore(p, addr + i, 1);
    unsigned o = (addr + i) & 4095;
    if (i == 0) writeHash = (writeHash ^ addr ^ (v.c * 0x9E3779B97F4A7C15ull) ^ ((u64)v.s << 40) ^ size) * 0xff51afd7ed558ccdull;
    p->d[o] = (u8)(v.c >> (8 * i));
    if (v.s) {
      if (!p->sh) { p->sh = new Cell[4096]; memset(p->sh, 0, sizeof(Cell) * 4096); }
      if (!p->sh[o].e) p->nsym++;
      p->sh[o] = {v.s, i};
      if (v.s >= LAZY_BASE && !p->lazy) { p->lazy = true; lazyPages.push_back(p); }
    } else if (p->sh && p->sh[o].e) { p->sh[o].e = 0; p->nsym--; }
    if (v.s || p->taint) taintSet(p, addr + i, 1, v.s != 0);
    if (p->code && codeHit((addr + i) >> 12, o, 1)) codeWritten(p);
  }
}

bool Engine::loadCells(u64 addr, unsigned size, u8* bytes, Cell* cells) {
  if (dbWatch) dataCheck(addr, size, false);
  bool any = false;
  for (unsigned i = 0; i < size;) {
    u64 a = addr + i; unsigned off = a & 4095, n = std::min<unsigned>(size - i, 4096 - off);
    Page* p = pageR(a >> 12);
    if (!p) fault(a, false);
    if (p->unk) { Page* q = known(a, n); if (q) p = q; }
    memcpy(bytes + i, p->d + off, n);
    if (p->nsym) {
      u32 hit = 0; for (unsigned k = 0; k < n; k++) hit |= p->sh[off + k].e;
      if (hit) {
        if (!any) { memset(cells, 0, i * sizeof(Cell)); any = true; }
        memcpy(cells + i, p->sh + off, n * sizeof(Cell));
      } else if (any) memset(cells + i, 0, n * sizeof(Cell));
    } else if (any) memset(cells + i, 0, n * sizeof(Cell));
    i += n;
  }
  return any;
}

void Engine::storeCells(u64 addr, unsigned size, const u8* bytes, const Cell* cells) {
  if (dbWatch) dataCheck(addr, size, true);
  for (unsigned i = 0; i < size;) {
    u64 a = addr + i; unsigned off = a & 4095, n = std::min<unsigned>(size - i, 4096 - off);
    Page* p = pageW(a >> 12);
    if (!p) fault(a, true);
    if (p->unk) unkStore(p, a, n);
    memcpy(p->d + off, bytes + i, n);
    for (unsigned k = 0; k < n; k++) writeHash = (writeHash ^ (a + k) ^ ((u64)bytes[i + k] << 48) ^ (cells ? ((u64)cells[i + k].e << 16) ^ cells[i + k].off : 0)) * 0xff51afd7ed558ccdull;
    if (!cells) {
      if (p->nsym) for (unsigned k = 0; k < n; k++) if (p->sh[off + k].e) { p->sh[off + k].e = 0; p->nsym--; }
      if (p->taint) taintSet(p, a, n, false);
      if (p->code && codeHit(a >> 12, off, n)) codeWritten(p);
      i += n; continue;
    }
    for (unsigned k = 0; k < n; k++) {
      Cell c = cells[i + k];
      if (c.e) {
        if (!p->sh) { p->sh = new Cell[4096]; memset(p->sh, 0, sizeof(Cell) * 4096); }
        if (!p->sh[off + k].e) p->nsym++;
        p->sh[off + k] = c;
        if (c.e >= LAZY_BASE && !p->lazy) { p->lazy = true; lazyPages.push_back(p); }
      } else if (p->sh && p->sh[off + k].e) { p->sh[off + k].e = 0; p->nsym--; }
      if (c.e || p->taint) taintSet(p, a + k, 1, c.e != 0);
    }
    if (p->code && codeHit(a >> 12, off, n)) codeWritten(p);
    i += n;
  }
}

u32 Engine::symbolizeMem(u64 addr, unsigned size, const std::string& name) {
  u64 c = 0; readMem(addr, &c, size);
  u32 e = X.var(name, size * 8, c);
  store(addr, size, Val{c, e});
  return e;
}

u32 Engine::symbolizeReg(int r, const std::string& name) {
  u32 e = X.var(name, 64, g[r]);
  gs[r] = e;
  return e;
}

void Engine::symbolizeVec(int r, const std::string& name) {
  for (int q = 0; q < 4; q++) {
    u64 c; memcpy(&c, v[r] + 8 * q, 8);
    u32 e = X.var(name + "_" + std::to_string(q), 64, c);
    for (int i = 0; i < 8; i++) vc[r][8 * q + i] = Cell{e, (u32)i};
  }
  vsym |= 1u << r;
}

void Engine::symbolizeFlags(const std::string& name) {
  u64 f = rflags();
  fl.lazy = 0; fl.prev.lazy = 0; fl.bits = f;
  static const int pos[6] = {0, 2, 4, 6, 7, 11};
  for (int p : pos) fl.sym[p] = X.var(name + std::to_string(p), 1, (f >> p) & 1);
}

bool Engine::tableLoad(Val a, unsigned size, Val& out) {
  if (!tableMax || size > 8 || tableLoads >= tableBudget) return false;
  const bool was = X.lazyOn; X.lazyOn = false;
  struct Back { Ctx& X; bool was; ~Back() { X.lazyOn = was; } } back{X, was};
  // (the entries read here are no access of the program's: the one it makes is checked at its address by the caller)
  struct NoWatch { Engine& E; bool w; ~NoWatch() { E.dbWatch = w; } } noWatch{*this, dbWatch}; dbWatch = false;
  const u32 e = X.force(a.s);
  // an address which is itself selected (a pointer chosen by a condition) is control, not an index: it is fixed, as before
  if (X.isC(e) || X.hasIte(e)) return false;
  const Ctx::Range r = X.range(e);
  if (r.hi < r.lo || r.hi - r.lo > (u64)tableMax * 64) return false;
  // the low bits which are fixed give the distance between two addresses it can take
  const Ctx::Known k = X.known(e);
  unsigned sh = 0; while (sh < 6 && ((k.zeros | k.ones) >> sh) & 1) sh++;
  const u64 lowm = maskOf(sh) & (sh ? ~0ull : 0), low = k.ones & lowm;
  u64 lo = r.lo;
  if ((lo & lowm) != low) { lo = (lo & ~lowm) + ((lo & lowm) > low ? (1ull << sh) : 0) + low; if (lo < r.lo || lo > r.hi) return false; }
  const u64 n = ((r.hi - lo) >> sh) + 1;
  // (two entries: a branch written as a selection - what it picks is usually where the code goes next; fixed and explored)
  if (n < 3 || n > tableMax || a.c < lo || a.c > r.hi || ((a.c - lo) & lowm)) return false;
  for (u64 j = 0; j < n; j++) if (!autoMap && (!isMapped(lo + (j << sh)) || !isMapped(lo + (j << sh) + size - 1))) return false;
  unsigned long hb = 0; _BitScanReverse64(&hb, n - 1); const unsigned bits = (unsigned)hb + 1;
  const u32 idx = X.extract(X.sub(e, X.cst(lo, 64)), sh, bits);
  std::vector<u32> lv((size_t)1 << bits);
  for (u64 j = 0; j < n; j++) { Val v = load(lo + (j << sh), size); if (v.s && !X.isC(X.force(v.s))) return false; lv[j] = X.cst(v.c, size * 8); }   // constant entries only
  for (u64 j = n; j < lv.size(); j++) lv[j] = lv[n - 1];           // never selected
  // a tree of selections, one index bit per level
  size_t cnt = lv.size();
  for (unsigned b = 0; b < bits; b++) {
    const u32 c = X.extract(idx, b, 1);
    for (size_t j = 0; j < cnt / 2; j++) lv[j] = X.ite(c, lv[2 * j + 1], lv[2 * j]);
    cnt /= 2;
  }
  out = {load(a.c, size).c, X.isC(lv[0]) ? 0 : lv[0]};
  tableLoads++;
  return true;
}

void Engine::addConstraint(u32 cond, u64 pc, u64 taken, u64 other, u8 kind, u32 expr) {
  cond = X.force(cond); expr = X.force(expr);       // what decides the path is built now
  if (X.isC(cond)) {
    // a branch on values which depend on the inputs, decided by the rules alone: its other side is impossible (proved)
    if (kind == 0 && other >= 0x10000) noteFolded(pc, taken, other);
    return;
  }
  if (kind == 1 && !keepAddressConstraints) return;
  path.push_back({cond, expr, pc, taken, other, kind, icount});
  if (spinLimit) {
    const u32 i = (u32)((pc * 0x9E3779B97F4A7C15ull) >> 56);
    if (spinTag[i] != pc) { spinTag[i] = pc; spinCount[i] = 0; }
    if (++spinCount[i] > spinLimit) spinning = true;
  }
}

bool Engine::oracle(u64 key, bool dflt) {
  auto it = oracleVars.find(key); u32 node;
  const bool was = X.lazyOn; X.lazyOn = false;
  if (it == oracleVars.end()) { char name[32]; snprintf(name, sizeof name, "env_%llx", (unsigned long long)key); node = X.var(name, 1, dflt); oracleVars[key] = node; }
  else node = it->second;
  const u32 idx = (u32)X.N(node).k;
  const bool v = runVals && idx < runVals->size() ? ((*runVals)[idx] & 1) != 0 : dflt;
  path.push_back({v ? node : X.not_(node), 0, key, v ? 1ull : 2ull, v ? 2ull : 1ull, 0, icount});
  X.lazyOn = was;
  return v;
}

void Engine::concretized(u32 expr, u64 value, unsigned w, u64 pc, u8 kind) {
  if (!expr) return;
  expr = X.force(expr);
  if (X.isC(expr)) return;
  if (lazyMem && kind == 1) {
    // every variable it depends on is fixed on this path already: its value follows, nothing to add
    auto it = pinVars.find(expr);
    if (it == pinVars.end()) { std::vector<u32> v; if (X.N(expr).size <= 64) X.collectVars(expr, v); it = pinVars.emplace(expr, std::move(v)).first; }
    bool all = !it->second.empty();
    for (u32 v : it->second) if (v >= pinned.size() || !pinned[v]) { all = false; break; }
    if (all) { pinSkips++; return; }
  }
  const u32 cond = X.eq(expr, X.cst(value, w));
  addConstraint(cond, pc, value, 0, kind, expr);
  if (lazyMem && kind == 1) {
    // x == c: the variable is fixed from here on
    const Node& c = X.N(cond);
    if (c.op == O_EQ) {
      const u32 v = X.N(c.a).op == O_VAR && X.isC(c.b) ? c.a : X.N(c.b).op == O_VAR && X.isC(c.a) ? c.b : 0;
      if (v) { const u32 idx = (u32)X.N(v).k; if (pinned.size() <= idx) pinned.resize(X.vars.size() + 64, 0); pinned[idx] = 1; }
    }
  }
}

// ------------------------------------------------------------------------------------------------ decoding
static bool isControlFlow(const ZydisDecodedInstruction& zi) {
  switch (zi.meta.category) {
  case ZYDIS_CATEGORY_COND_BR: case ZYDIS_CATEGORY_UNCOND_BR: case ZYDIS_CATEGORY_CALL: case ZYDIS_CATEGORY_RET:
  case ZYDIS_CATEGORY_SYSCALL: case ZYDIS_CATEGORY_INTERRUPT: case ZYDIS_CATEGORY_SYSRET: case ZYDIS_CATEGORY_SYSTEM:
    return true;
  default: break;
  }
  switch (zi.mnemonic) {
  case ZYDIS_MNEMONIC_UD0: case ZYDIS_MNEMONIC_UD1: case ZYDIS_MNEMONIC_UD2: case ZYDIS_MNEMONIC_HLT: case ZYDIS_MNEMONIC_INT3:
  case ZYDIS_MNEMONIC_INT: case ZYDIS_MNEMONIC_INT1: case ZYDIS_MNEMONIC_INTO: case ZYDIS_MNEMONIC_LOOP: case ZYDIS_MNEMONIC_LOOPE:
  case ZYDIS_MNEMONIC_LOOPNE: case ZYDIS_MNEMONIC_JRCXZ: case ZYDIS_MNEMONIC_JECXZ: case ZYDIS_MNEMONIC_CPUID: case ZYDIS_MNEMONIC_POPFQ:
    return true;
  default: return false;
  }
}

static bool decodeOne(Engine& E, ZydisDecoder* dec, u64 addr, Insn& I, bool& cf) {
  u8 buf[16];
  if (!E.isMapped(addr)) return false;
  E.readMem(addr, buf, 15);
  ZydisDecodedInstruction zi; ZydisDecodedOperand zo[ZYDIS_MAX_OPERAND_COUNT];
  if (!ZYAN_SUCCESS(ZydisDecoderDecodeFull(dec, buf, 15, &zi, zo))) return false;
  I = Insn{};
  I.addr = addr; I.len = zi.length; I.next = addr + zi.length; I.mn = (u16)zi.mnemonic;
  I.opsz = (u8)(zi.operand_width / 8); I.asz = (u8)(zi.address_width / 8);
  if (zi.attributes & ZYDIS_ATTRIB_HAS_REPNE) I.rep = 2;
  else if (zi.attributes & (ZYDIS_ATTRIB_HAS_REP | ZYDIS_ATTRIB_HAS_REPE)) I.rep = 1;
  I.vex = zi.encoding == ZYDIS_INSTRUCTION_ENCODING_VEX || zi.encoding == ZYDIS_INSTRUCTION_ENCODING_EVEX;
  I.vl = (u8)(zi.avx.vector_length / 8);
  unsigned nv = zi.operand_count_visible; if (nv > 4) nv = 4;
  I.nops = (u8)nv;
  for (unsigned i = 0; i < nv; i++) {
    const ZydisDecodedOperand& o = zo[i]; Opnd& d = I.op[i];
    d.size = (u8)(o.size / 8);
    if (o.type == ZYDIS_OPERAND_TYPE_REGISTER) {
      const RegDesc& r = regmap[o.reg.value];
      d.type = OT_REG; d.rk = r.rk; d.reg = r.idx; d.roff = r.off;
      if (r.rk == RK_GPR && d.size == 0) d.size = r.size;
    } else if (o.type == ZYDIS_OPERAND_TYPE_MEMORY) {
      d.type = OT_MEM;
      if (o.mem.base != ZYDIS_REGISTER_NONE) { const RegDesc& r = regmap[o.mem.base]; d.base = r.rk == RK_RIP ? 16 : r.idx; if (r.rk != RK_GPR && r.rk != RK_RIP) return false; }
      if (o.mem.index != ZYDIS_REGISTER_NONE) { const RegDesc& r = regmap[o.mem.index]; if (r.rk != RK_GPR) return false; d.index = r.idx; d.scale = o.mem.scale; }
      d.disp = o.mem.disp.value;
      d.seg = o.mem.segment == ZYDIS_REGISTER_FS ? RK_FS : o.mem.segment == ZYDIS_REGISTER_GS ? RK_GS : 0;
    } else if (o.type == ZYDIS_OPERAND_TYPE_IMMEDIATE) {
      d.type = OT_IMM;
      if (o.imm.is_relative) { u64 t = 0; ZydisCalcAbsoluteAddress(&zi, &o, addr, &t); d.disp = (i64)t; }
      else d.disp = o.imm.value.s;
    } else return false;   // far pointers
  }
  cf = isControlFlow(zi);
  return true;
}

const Insn* Engine::decodeAt(u64 addr) {
  static Insn one; bool cf;
  return decodeOne(*this, (ZydisDecoder*)decoder, addr, one, cf) ? &one : nullptr;
}

Block* Engine::block(u64 addr) {
  BCache& c = bcache[(addr ^ (addr >> 12)) & 4095];
  if (c.tag == addr) return c.b;
  auto it = blocks.find(addr);
  Block* b;
  if (it != blocks.end()) b = it->second;
  else {
    if (guardSet && addr < (guardSet << 12)) return nullptr;
    const auto shared = [&](u64 x) { return apiTable && x >= apiLo && x < apiHi && apiTable->count(x) != 0; };
    b = new Block{addr, epoch, stops.count(addr) != 0 || hooks.count(addr) != 0 || shared(addr), {}};
    u64 a = addr;
    for (int k = 0; k < 64; k++) {
      Insn I; bool cf = false;
      if (!decodeOne(*this, (ZydisDecoder*)decoder, a, I, cf)) break;
      b->ins.push_back(I);
      markCode(a, I.len);
      a = I.next;
      if (cf) break;
      if (stops.count(a) || hooks.count(a) || shared(a)) break;
    }
    if (b->ins.empty()) { delete b; return nullptr; }
    blocks.emplace(addr, b);
    blocksDecoded++;
  }
  c.tag = addr; c.b = b;
  return b;
}

const char* Engine::mnemonicName(int mn) { return ZydisMnemonicGetString((ZydisMnemonic)mn); }

std::string Engine::disasm(u64 addr) {
  u8 buf[16]; readMem(addr, buf, 15);
  ZydisDisassembledInstruction di;
  if (!ZYAN_SUCCESS(ZydisDisassembleIntel(ZYDIS_MACHINE_MODE_LONG_64, addr, buf, 15, &di))) return "(bad)";
  return di.text;
}

Stop Engine::step() { return run(1); }

u64 Engine::stateHash() const {
  u64 h = 0x9E3779B97F4A7C15ull ^ rip;
  auto mix = [&](u64 v) { h = (h ^ v) * 0xff51afd7ed558ccdull; h ^= h >> 29; };
  for (int r = 0; r < 16; r++) { mix(g[r]); mix(gs[r]); }
  mix(fl.op | ((u64)fl.w << 8) | ((u64)fl.lazy << 16)); mix(fl.a); mix(fl.b); mix(fl.r); mix(fl.x); mix(((u64)fl.sa << 32) | fl.sb); mix(((u64)fl.sr << 32) | fl.sx); mix(fl.bits);
  mix(fl.prev.op | ((u64)fl.prev.lazy << 16)); mix(fl.prev.a); mix(fl.prev.b); mix(fl.prev.r); mix(fl.prev.x); mix(((u64)fl.prev.sa << 32) | fl.prev.sb); mix(((u64)fl.prev.sr << 32) | fl.prev.sx);
  for (u32 e : fl.sym) mix(e);
  mix(mxcsr); mix(fsbase); mix(gsbase); mix(vsym);
  for (int r = 0; r < 16; r++) { u64 q[4]; memcpy(q, v[r], 32); mix(q[0]); mix(q[1]); mix(q[2]); mix(q[3]); if (vsym & (1u << r)) for (const Cell& c : vc[r]) mix(((u64)c.e << 32) | c.off); }
  return h;
}

namespace { struct LazyScope { Ctx& X; LazyScope(Ctx& X, bool on) : X(X) { X.lazyOn = on; } ~LazyScope() { X.lazyOn = false; } }; }

Stop Engine::run(u64 maxIns) {
  const Stop s = runLoop(maxIns);
  if (covOn && jit) jitSyncCov(jit, *this);
  return s;
}

Stop Engine::runLoop(u64 maxIns) {
  const u64 end = icount + maxIns;
  stopInfo.clear();
  LazyScope scope(X, lazy);
  bool lazyNow = lazy; size_t markTape = X.tape.size(); u64 markBuilt = X.forcedCount;
  struct Depth { u32& d; explicit Depth(u32& d) : d(d) { d++; } ~Depth() { d--; } } depth{runDepth};
  Block* last = nullptr; u32 lastEp = 0;                // the block which just ran to its end, and the epoch it belongs to
  while (icount < end) {
    if (runDepth == 1 && !graveyard.empty()) { for (Block* x : graveyard) delete x; graveyard.clear(); }
    bool inWin = false;
    if (loopLimit) {
      const u64 sig = blocksDecoded * 0x9E3779B97F4A7C15ull + path.size() * 0xff51afd7ed558ccdull + X.n.size() + X.tape.size();
      if (sig != progressSig) { progressSig = sig; progressAt = icount; loopMark.armed = false; loopWin = 0; }
      else if (icount - progressAt > loopLimit) {
        if (!loopWin) { loopWin = 2048; loopWinEnd = icount + loopWin; }
        else if (icount >= loopWinEnd + 128 * loopWin) { loopWin = std::min<u64>(loopWin * 2, 1u << 20); loopWinEnd = icount + loopWin; loopMark.armed = false; }
        inWin = icount < loopWinEnd;
      }
      if (inWin) {
        LoopMark& m = loopMark;
        if (!m.armed) { m = LoopMark{rip, stateHash(), icount, 0, 0, 64, true, false}; writeHash = 0; }
        else if (rip == m.rip && icount != m.at) {
          if (stateHash() == m.hash) {
            const u64 period = icount - m.at;
            if (m.twice && m.period == period && m.writes == writeHash) { stopInfo = "endless loop"; return ST_COUNT; }
            m.twice = true; m.period = period; m.writes = writeHash; m.at = icount; writeHash = 0;
          }
        } else if (icount - m.at > m.span && !m.twice) { const u64 span = m.span * 2; m = LoopMark{rip, stateHash(), icount, 0, 0, span, true, false}; writeHash = 0; }
      }
    }
    Block* b = nullptr;
    Block* const prev = last && lastEp == epoch ? last : nullptr; last = nullptr;
    if (prev) { if (prev->nextA[0] == rip) b = prev->nextB[0]; else if (prev->nextA[1] == rip) b = prev->nextB[1]; }
    if (!b) { b = block(rip); if (b && prev) { const int k = prev->nextK++ & 1; prev->nextA[k] = rip; prev->nextB[k] = b; } }
    if (!b || b->special) {
      if (stops.count(rip)) { stopInfo = "address"; return ST_ADDRESS; }
      auto h = hooks.find(rip);
      if (h != hooks.end()) { X.lazyOn = false; Stop s = h->second(*this); X.lazyOn = lazyNow; if (s != ST_NONE) return s; continue; }
      if (apiTable && rip >= apiLo && rip < apiHi) {
        auto a = apiTable->find(rip);
        if (a != apiTable->end()) { X.lazyOn = false; icount++; Stop s = apiCall(*this, a->second); X.lazyOn = lazyNow; if (s != ST_NONE) return s; continue; }
      }
      if (!b) {
        if (lazyMem && inZone(rip) && ucCall()) { icount++; continue; }
        stopInfo = "cannot decode"; trapKind = isMapped(rip) && !(guardSet && rip < (guardSet << 12)) ? TK_INVALID : TK_EXEC; trapArg = rip;
        if (trap) { X.lazyOn = false; const int t = trap(*this, ST_FAULT); X.lazyOn = lazyNow; if (t == 1) { stopInfo.clear(); icount++; continue; } }
        return ST_FAULT;
      }
    }
    // a block run often, outside the loop detector's windows: as native code, while its inputs hold no expression
    if (jitOn && !inWin && !hotOn && !profile && !tf && !(drExec | drData) && !(fl.bits & 0x244100) && (b->hits >= jitHot || ++b->hits >= jitHot)) {
      // (not past the place where the loop detector's next window starts: it is the same with and without native code)
      u64 lim = end;
      if (loopLimit) { const u64 t = loopWin ? loopWinEnd + 128 * loopWin : progressAt + loopLimit + 1; if (t < lim) lim = t; }
      if (!jit && !(jit = jitCreate(*this))) jitOn = false;
      else if (lim > icount && jitRun(jit, *this, lim - icount, b)) continue;
    }
    bool trapped = false;
    if (hotOn) hot[b->addr] += b->ins.size();
    const u64 ep = epoch;                               // (what was decoded is dropped: the rest of this block is stale)
    for (const Insn& I : b->ins) {
      if (dbgOn && drExec && !rfOnce) if (const u8 hit = execHits(I.addr)) {
        // an execute breakpoint: a fault before the instruction runs (its CONTEXT has RF clear: a handler which goes on
        // without setting it, or turning the breakpoint off, gets the same exception again)
        rip = I.addr; lastInsn = I; dbStatus = hit; stopInfo = "single step"; trapKind = TK_SINGLESTEP;
        if (trap) { X.lazyOn = false; const int t = trap(*this, ST_EXCEPTION); X.lazyOn = lazyNow; if (t == 1) { stopInfo.clear(); trapped = true; break; } }
        return ST_EXCEPTION;
      }
      rip = I.next;
      Stop s;
      const u64 lk0 = X.lookups, tsc0 = profile ? __rdtsc() : 0;
      const u64 nn0 = profile ? X.n.size() : 0;
      struct Acct { Engine& E; u64 lk0, tsc0, nn0; u16 mn; ~Acct() {
        const bool sym = E.X.lookups != lk0; E.symIns += sym;
        if (E.profile) {
          const u64 dt = __rdtsc() - tsc0; (sym ? E.cycSym : E.cycCon) += dt;
          if (sym) { if (E.symHist.empty()) E.symHist.resize(ZYDIS_MNEMONIC_MAX_VALUE + 1); SymHist& h = E.symHist[mn]; h.n++; h.lookups += E.X.lookups - lk0; h.nodes += E.X.n.size() - nn0; h.cyc += dt; }
        } } } acct{*this, lk0, tsc0, nn0, (u16)I.mn};
      if (dbgOn) dbWatch = drData != 0;
      try { s = exec(I); }
      catch (int code) {
        dbWatch = false; dataHits = 0;
        rip = I.addr; lastInsn = I; if (stopInfo.empty()) stopInfo = "memory fault";
        int t = 0;
        if (code == ST_FAULT && trap && (trapKind == TK_READ || trapKind == TK_WRITE)) {
          if (softRetry == I.addr) { softRetry = 0; t = 2; }
          else { X.lazyOn = false; t = trap(*this, ST_FAULT); X.lazyOn = lazyNow; }
        }
        if (t == 1) { stopInfo.clear(); icount++; trapped = true; break; }       // a handler runs: the block may be gone
        if (t != 2) return (Stop)code;
        // nobody takes the fault: the access is done as an engine without the guard does it (zeros read, a page mapped)
        stopInfo.clear();
        if (++softFaults > softLimit) { guardPages = 0; flushTlb(); rip = I.addr; trapped = true; break; }   // too many: no guard for the rest of the run
        const u64 gp = guardPages;
        struct Back { Engine& E; u64 gp; ~Back() { E.guardPages = gp; for (u64 i = 0; i < gp && i < 512; i++) { if (E.rtlb[i].tag < gp) E.rtlb[i].tag = ~0ull; if (E.wtlb[i].tag < gp) E.wtlb[i].tag = ~0ull; } } } back{*this, gp};
        guardPages = 0; rip = I.next;
        dbWatch = drData != 0;
        try { s = exec(I); dbWatch = false; }
        catch (int code2) { dbWatch = false; rip = I.addr; if (stopInfo.empty()) stopInfo = "memory fault"; return (Stop)code2; }
      }
      icount++;
      if (dbgOn) {
        // debug traps after the instruction, one #DB whose DR6 says which: a single step (TF was on as it began; the
        // instruction which sets TF is followed by one more), the data breakpoints it hit, what mov ss held back. After
        // mov ss they all wait for the next instruction.
        dbWatch = false;
        if (s == ST_NONE && (tf || dataHits || dbHeld)) {
          if (movSS) { dbHeld |= dataHits; if (tf == 1) tf = 2; }
          else {
            u64 st = dbHeld | dataHits; dbHeld = 0;
            if (tf == 2) st |= 0x4000;
            else if (tf == 1) tf = 2;
            if (st) {
              if (st & 0x4000) { tf = 0; fl.bits &= ~0x100ull; }
              dbStatus = st; stopInfo = "single step"; trapKind = TK_SINGLESTEP; s = ST_EXCEPTION;
            }
          }
        }
        dataHits = 0; movSS = 0; rfOnce = 0;
        dbgOn = (tf | drExec | drData) || dbHeld;
      }
      if (s == ST_SYSCALL && sysCall) {
        lastInsn = I;
        X.lazyOn = false; const Stop r = sysCall(*this); X.lazyOn = lazyNow;
        if (r == ST_NONE) { stopInfo.clear(); trapped = true; break; }
        s = r;
      }
      if (s != ST_NONE) {
        lastInsn = I;
        if (trap && (s == ST_EXCEPTION || s == ST_HALT)) {
          X.lazyOn = false; const int t = trap(*this, s); X.lazyOn = lazyNow;
          if (t == 1) { stopInfo.clear(); trapped = true; break; }
        }
        return s;
      }
      if (rip != I.next || icount >= end || epoch != ep) break;
    }
    if (!trapped && epoch == ep) { last = b; lastEp = ep; }
    if (X.overBudget) { stopInfo = "expression budget"; return ST_FAULT; }
    if (spinning) { stopInfo = "spinning"; return ST_COUNT; }
    if (lazyNow && X.tape.size() - markTape > 32768) {
      // most of what is recorded gets built here (branches read it all): recording only costs, the rest of the run builds directly
      if ((X.forcedCount - markBuilt) * 2 > X.tape.size() - markTape) { settle(); lazyNow = false; X.lazyOn = false; lazyOffRuns++; }
      else if (X.tape.size() > lazyLimit) { settle(); X.lazyOn = true; }
      markTape = X.tape.size(); markBuilt = X.forcedCount;
    }
  }
  return ST_COUNT;
}

}  // namespace unshroud

namespace unshroud {

u64 Engine::memHash() const {
  u64 h = 0;
  for (auto& kv : pages) {
    const Page* p = kv.second; u64 x = kv.first * 0x9E3779B97F4A7C15ull;
    for (int i = 0; i < 4096; i += 8) { u64 w; memcpy(&w, p->d + i, 8); x = (x ^ w) * 0xff51afd7ed558ccdull; x ^= x >> 31; }
    if (p->nsym && p->sh) for (int i = 0; i < 4096; i++) if (p->sh[i].e) x = (x ^ (((u64)p->sh[i].e << 20) ^ ((u64)i << 4) ^ p->sh[i].off)) * 0xff51afd7ed558ccdull;
    if (p->unk) for (int i = 0; i < 8; i++) x = (x ^ p->unk[i]) * 0x9E3779B97F4A7C15ull;
    h += x ^ (x >> 29);
  }
  return h;
}

int Engine::memDiff(const Engine& o, FILE* out, int limit) const {
  int n = 0;
  for (auto& kv : pages) {
    if (n >= limit) break;
    auto it = o.pages.find(kv.first);
    if (it == o.pages.end()) { fprintf(out, "  page %llx: only in the first%c", (unsigned long long)kv.first, 10); n++; continue; }
    const Page* p = kv.second; const Page* q = it->second;
    if (p == q) continue;
    for (int i = 0; i < 4096 && n < limit; i++) {
      const u32 e1 = p->sh ? p->sh[i].e : 0, e2 = q->sh ? q->sh[i].e : 0;
      if (p->d[i] != q->d[i] || e1 != e2) { fprintf(out, "  %llx: %02x / %02x  expression %u / %u%c", (unsigned long long)((kv.first << 12) + i), p->d[i], q->d[i], e1, e2, 10); n++; i |= 7; }
    }
    if ((p->unk != nullptr) != (q->unk != nullptr) || (p->unk && memcmp(p->unk, q->unk, 64))) { fprintf(out, "  page %llx: unknown words differ%c", (unsigned long long)kv.first, 10); n++; }
  }
  for (auto& kv : o.pages) if (n < limit && !pages.count(kv.first)) { fprintf(out, "  page %llx: only in the second%c", (unsigned long long)kv.first, 10); n++; }
  return n;
}

}  // namespace unshroud
