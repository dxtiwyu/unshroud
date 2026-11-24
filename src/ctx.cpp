#include "ctx.hpp"
#include <cstdio>
#include <cstring>
#include <fstream>
#include <sstream>

namespace unshroud {

static u64 hexAt(const std::string& s, size_t& i) {   // "0x..." at i (after the quote): its value, i past it
  if (s.compare(i, 2, "0x") == 0) i += 2;
  u64 v = 0;
  for (; i < s.size(); i++) {
    const char c = s[i]; int d;
    if (c >= '0' && c <= '9') d = c - '0'; else if (c >= 'a' && c <= 'f') d = c - 'a' + 10; else if (c >= 'A' && c <= 'F') d = c - 'A' + 10; else break;
    v = v * 16 + (u64)d;
  }
  return v;
}

static bool parseCtx(const std::string& s, RealCtx& c) {
  size_t i = s.find("\"entry\": \"");
  if (i == std::string::npos) return false;
  i += 10; c.entry = hexAt(s, i);
  if ((i = s.find("\"ret_rsp\": \"")) != std::string::npos) { i += 12; c.rsp = hexAt(s, i); }
  size_t a = s.find("\"regs\": {"), b = a == std::string::npos ? a : s.find('}', a);
  for (size_t p = a == std::string::npos ? b : a + 9; a != std::string::npos && p < b;) {
    const size_t q1 = s.find('"', p); if (q1 == std::string::npos || q1 >= b) break;
    const size_t q2 = s.find('"', q1 + 1); const std::string name = s.substr(q1 + 1, q2 - q1 - 1);
    size_t v = s.find('"', q2 + 1) + 1; const u64 val = hexAt(s, v);
    if (name.compare(0, 3, "xmm") != 0) c.regs[name] = val;
    p = s.find('"', v) + 1;
  }
  return true;
}

static int hx2(char a, char b) { auto h = [](char c) { return c <= '9' ? c - '0' : (c | 32) - 'a' + 10; }; return h(a) * 16 + h(b); }

static void parseLists(const std::string& s, RealCtx& c) {
  size_t m = s.find("\"mem\": [");
  if (m != std::string::npos) {
    size_t p = m + 8;
    while (p < s.size() && s[p] == '[') {
      p += 2; const u64 addr = hexAt(s, p);
      p = s.find('"', p + 1) + 1; const size_t e = s.find('"', p);
      std::vector<u8> bytes((e - p) / 2);
      for (size_t k = 0; k < bytes.size(); k++) bytes[k] = (u8)hx2(s[p + 2 * k], s[p + 2 * k + 1]);
      c.mem.push_back({addr, std::move(bytes)});
      p = e + 2; if (s.compare(p, 2, ", ") == 0) p += 2;
    }
  }
  size_t a = s.find("\"api\": [");
  if (a != std::string::npos) {
    size_t p = a + 8;
    while (p < s.size() && s[p] == '[') {
      p += 2; const u64 site = hexAt(s, p);
      p = s.find('"', p + 1) + 1; const u64 rax = hexAt(s, p);
      c.api.push_back({site, rax});
      p += 2; if (s.compare(p, 2, ", ") == 0) p += 2;
    }
  }
}

bool loadContexts(const std::string& path, std::unordered_map<u64, RealCtx>& out) {
  std::ifstream f(path, std::ios::binary); if (!f) return false;
  std::string line;
  while (std::getline(f, line)) {
    RealCtx c;
    if (!parseCtx(line, c) || out.count(c.entry)) continue;
    parseLists(line, c);
    out.emplace(c.entry, std::move(c));
  }
  return true;
}

std::map<std::string, std::pair<u64, u64>> loadModuleList(const std::string& path) {
  std::map<std::string, std::pair<u64, u64>> m;
  std::ifstream f(path); std::string line;
  while (std::getline(f, line)) {
    std::istringstream is(line); std::string ev, base, size, traced, name;
    if (!(is >> ev >> base >> size >> traced >> name) || (ev != "load" && ev != "mapped")) continue;
    for (char& ch : name) if (ch >= 'A' && ch <= 'Z') ch += 32;
    if (!m.count(name)) m[name] = {strtoull(base.c_str(), nullptr, 16), strtoull(size.c_str(), nullptr, 16)};
  }
  return m;
}

}  // namespace unshroud
