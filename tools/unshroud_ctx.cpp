// Real calling contexts of functions from Tenet text traces (each file the consecutive lines of one thread):
// unshroud_ctx <pe> <module base in the trace, hex> <rva,rva,...> <occurrences per function> <out.jsonl> trace...
// For each occurrence (a line whose rip is a wanted entry, while no other occurrence is being recorded in that file),
// until the thread's stack pointer climbs above the entry's (the function returned) or 20M lines: the registers at the
// entry, every byte the call read before it wrote it (the memory it depends on), and what each call out of the module
// returned (a call whose next line is its fall-through: the callee ran outside the traced code; rax after it).
// One JSON line each: entry, line, lines, file, end, regs {name: "0x.."}, ret_rsp, mem [["0xaddr", "hex"]], api [["0xsite", "0xrax"]]
#include "../src/util.hpp"
#include "../src/engine.hpp"
#include "../src/pe.hpp"
#include <Zydis/Zydis.h>
#include <algorithm>
#include <cstdio>
#include <cstring>
#include <map>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace unshroud;
static inline u64 hexv(const char*& p, const char* e) {
  u64 v = 0;
  while (p < e) { char c = *p; int d; if (c >= '0' && c <= '9') d = c - '0'; else if (c >= 'a' && c <= 'f') d = c - 'a' + 10; else if (c >= 'A' && c <= 'F') d = c - 'A' + 10; else break; v = v * 16 + d; p++; }
  return v;
}
static inline int hx(char c) { return c <= '9' ? c - '0' : (c | 32) - 'a' + 10; }
static u64 regv(std::map<std::string, std::string>& r, const char* n) { const std::string& s = r[n]; if (s.size() < 3) return 0; const char* q = s.c_str() + 2; return hexv(q, q + strlen(q)); }
// the bytes of an mr= / mw= field: "0xADDR:HEX;0xADDR:HEX"
template <class F> static void eachByte(const char* a, const char* ae, F f) {
  while (a && a < ae) {
    const char* semi = (const char*)memchr(a, ';', (size_t)(ae - a)); if (!semi) semi = ae;
    const char* colon = (const char*)memchr(a, ':', (size_t)(semi - a));
    if (colon) {
      const char* q = a + 2; const u64 addr = hexv(q, colon); u64 k = 0;
      for (const char* h = colon + 1; h + 1 < semi; h += 2, k++) f(addr + k, (u8)(hx(h[0]) * 16 + hx(h[1])));
    }
    a = semi + 1;
  }
}
struct Rec {
  bool on = false; u64 entry = 0, line = 0, rsp = 0, lines = 0; std::map<std::string, std::string> regs;
  std::unordered_map<u64, u8> firstRead; std::unordered_set<u64> written; std::vector<std::pair<u64, u64>> api;
};
static void finish(FILE* out, Rec& r, const char* file, const char* why) {
  std::vector<std::pair<u64, u8>> m(r.firstRead.begin(), r.firstRead.end()); std::sort(m.begin(), m.end());
  char b[160];
  snprintf(b, sizeof b, "{\"entry\": \"0x%llx\", \"line\": %llu, \"lines\": %llu", (unsigned long long)r.entry, (unsigned long long)r.line, (unsigned long long)r.lines);
  std::string s = b; s += std::string(", \"file\": \"") + file + "\", \"end\": \"" + why + "\", \"regs\": {";
  bool first = true;
  for (auto& kv : r.regs) { s += (first ? "\"" : ", \"") + kv.first + "\": \"" + kv.second + "\""; first = false; }
  snprintf(b, sizeof b, "}, \"ret_rsp\": \"0x%llx\", \"mem\": [", (unsigned long long)r.rsp); s += b;
  first = true;
  for (size_t i = 0; i < m.size();) {
    size_t j = i; std::string hexs;
    while (j < m.size() && m[j].first == m[i].first + (j - i)) { snprintf(b, sizeof b, "%02x", m[j].second); hexs += b; j++; }
    snprintf(b, sizeof b, "%s[\"0x%llx\", \"", first ? "" : ", ", (unsigned long long)m[i].first);
    s += b; s += hexs + "\"]"; first = false; i = j;
  }
  s += "], \"api\": [";
  for (size_t i = 0; i < r.api.size(); i++) {
    snprintf(b, sizeof b, "%s[\"0x%llx\", \"0x%llx\"]", i ? ", " : "", (unsigned long long)r.api[i].first, (unsigned long long)r.api[i].second);
    s += b;
  }
  s += "]}";
  s += (char)10;
  fwrite(s.data(), 1, s.size(), out); fflush(out);
  r.on = false; r.firstRead.clear(); r.written.clear(); r.api.clear();
}
int main(int argc, char** argv) {
  if (argc < 7) { printf("usage: unshroud_ctx pe tracebase rvas per out.jsonl trace...%c", 10); return 1; }
  Engine E; Image img;
  if (!loadPE(E, argv[1], img)) { printf("cannot load%c", 10); return 1; }
  const u64 tb = strtoull(argv[2], nullptr, 16), tsize = img.size;
  std::unordered_map<u64, int> want;
  { std::string s = argv[3]; size_t i = 0; while (i < s.size()) { size_t j = s.find(',', i); if (j == std::string::npos) j = s.size(); want[strtoull(s.substr(i, j - i).c_str(), nullptr, 16)] = 0; i = j + 1; } }
  const int per = atoi(argv[4]);
  const u64 maxLines = getenv("UNSHROUD_CTX_LINES") ? strtoull(getenv("UNSHROUD_CTX_LINES"), nullptr, 0) : 20000000ull;
  FILE* out = fopen(argv[5], "wb");
  std::vector<char> buf((size_t)256 << 20);
  size_t left = want.size() * (size_t)per;
  for (int fi = 6; fi < argc && left; fi++) {
    FILE* f = fopen(argv[fi], "rb"); if (!f) continue;
    std::map<std::string, std::string> regs; u64 line = 0, prevRip = 0;
    std::vector<Rec> act;                                  // recordings open on this thread (nested calls too)
    size_t keep = 0; bool eof = false;
    while (!eof && (left || !act.empty())) {
      size_t n = fread(buf.data() + keep, 1, buf.size() - keep, f); size_t total = keep + n;
      if (!n) { eof = true; if (!total) break; buf[total++] = (char)10; }
      size_t start = 0;
      for (;;) {
        char* nl = (char*)memchr(buf.data() + start, 10, total - start); if (!nl) break;
        const char* s = buf.data() + start; const char* e = nl; start = (size_t)(nl - buf.data()) + 1; line++;
        u64 rip = 0; const char* p = s; const char *mr = nullptr, *mre = nullptr, *mw = nullptr, *mwe = nullptr;
        while (p < e) {
          const char* eq = (const char*)memchr(p, '=', (size_t)(e - p)); if (!eq) break;
          const char* ce = (const char*)memchr(eq, ',', (size_t)(e - eq)); if (!ce) ce = e;
          const size_t ln = (size_t)(eq - p);
          if (ln == 2 && p[0] == 'm' && p[1] == 'r') { mr = eq + 1; mre = ce; }
          else if (ln == 2 && p[0] == 'm' && p[1] == 'w') { mw = eq + 1; mwe = ce; }
          else if (!(ln == 2 && p[0] == 'i' && p[1] == 'b')) {
            std::string name(p, eq); regs[name].assign(eq + 1, ce);
            if (name == "rip") { const char* q = eq + 3; rip = hexv(q, ce); }
          }
          p = ce + 1;
        }
        const u64 rsp = regv(regs, "rsp");
        const Insn* callBefore = nullptr;                  // a call out of the traced code: its result is in rax now
        if (prevRip >= tb && prevRip < tb + tsize) { const Insn* I = E.decodeAt(prevRip - tb + img.base); if (I && I->mn == ZYDIS_MNEMONIC_CALL && rip == prevRip + I->len) callBefore = I; }
        for (size_t k = 0; k < act.size();) {
          Rec& r = act[k]; r.lines++;
          if (rsp > r.rsp) { finish(out, r, argv[fi], "return"); left--; act.erase(act.begin() + k); continue; }   // (this line is the caller's)
          if (callBefore) r.api.push_back({prevRip - tb, regv(regs, "rax")});
          eachByte(mr, mre, [&](u64 a, u8 v) { if (!r.written.count(a) && !r.firstRead.count(a) && r.firstRead.size() < 16000000) r.firstRead[a] = v; });
          eachByte(mw, mwe, [&](u64 a, u8) { r.written.insert(a); });
          if (r.lines >= maxLines) { finish(out, r, argv[fi], "limit"); left--; act.erase(act.begin() + k); continue; }
          k++;
        }
        if (rip >= tb && rip < tb + tsize && left > act.size() && act.size() < 64) {
          auto it = want.find(rip - tb);
          if (it != want.end() && it->second < per) {
            it->second++; act.emplace_back(); Rec& r = act.back();
            r.on = true; r.entry = rip - tb; r.line = line; r.regs = regs; r.rsp = rsp;
            eachByte(mr, mre, [&](u64 a, u8 v) { if (!r.firstRead.count(a)) r.firstRead[a] = v; });
            eachByte(mw, mwe, [&](u64 a, u8) { r.written.insert(a); });
          }
        }
        prevRip = rip;
      }
      keep = total - start; if (keep == buf.size()) buf.resize(buf.size() * 2);
      memmove(buf.data(), buf.data() + start, keep);
    }
    for (Rec& r : act) { finish(out, r, argv[fi], "end of file"); left--; }
    fclose(f);
  }
  fclose(out);
  return 0;
}
