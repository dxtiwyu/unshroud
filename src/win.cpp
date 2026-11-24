// unshroud - the process: modules, loader lists, TEB / PEB / process parameters / shared system page / TLS (see win.hpp)
#include "win.hpp"
#include <windows.h>
#include <cstdio>
#include <algorithm>

namespace unshroud {

namespace {
const char* SYSTEM_DLLS[] = {"ntdll.dll", "kernel32.dll", "KernelBase.dll", "advapi32.dll", "msvcrt.dll", "sechost.dll", "rpcrt4.dll",
                             "bcryptprimitives.dll", "ucrtbase.dll",
                             // what the host (rundll32.exe) brings in: code which looks for user32 in the loader's list finds it
                             "win32u.dll", "gdi32.dll", "user32.dll"};

bool readFile(const std::string& path, std::vector<u8>& d) {
  FILE* f = fopen(path.c_str(), "rb");
  if (!f) return false;
  fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
  d.resize(sz > 0 ? (size_t)sz : 0);
  bool ok = d.empty() || fread(d.data(), 1, d.size(), f) == d.size();
  fclose(f);
  return ok && !d.empty();
}
template <class T> T rd(const std::vector<u8>& b, size_t o) { T v{}; if (o + sizeof(T) <= b.size()) memcpy(&v, b.data() + o, sizeof(T)); return v; }
std::string cstr(const std::vector<u8>& b, size_t o) { std::string s; while (o < b.size() && b[o]) s += (char)b[o++]; return s; }
std::string baseName(const std::string& p) { size_t s = p.find_last_of("/\\"); return s == std::string::npos ? p : p.substr(s + 1); }
std::string lower(std::string s) { for (char& c : s) if (c >= 'A' && c <= 'Z') c += 32; return s; }
std::string wideToText(const u8* p, size_t bytes) { std::string s; for (size_t i = 0; i + 1 < bytes; i += 2) s += (char)(p[i + 1] ? '?' : p[i]); return s; }

// a PE file laid out as the loader does, relocated to `base` (0: where it prefers): its bytes, its exports
bool loadModule(const std::string& path, u64 base, WinModule& m) {
  std::vector<u8> raw;
  if (!readFile(path, raw) || raw.size() < 0x200) return false;
  const u32 nt = rd<u32>(raw, 0x3c), opt = nt + 0x18;
  if (rd<u32>(raw, nt) != 0x4550 || rd<u16>(raw, opt) != 0x20b) return false;
  m.path = path; m.name = baseName(path);
  m.preferred = rd<u64>(raw, opt + 0x18); m.size = rd<u32>(raw, opt + 0x38); m.timestamp = rd<u32>(raw, nt + 8);
  m.base = base ? base : m.preferred;
  const u32 headers = rd<u32>(raw, opt + 0x3c), dirs = opt + 0x70;
  std::vector<u8> img((size_t)m.size, 0);
  memcpy(img.data(), raw.data(), std::min<size_t>({headers, raw.size(), img.size()}));
  const u32 sec = opt + rd<u16>(raw, nt + 0x14);
  for (unsigned i = 0; i < rd<u16>(raw, nt + 6); i++) {
    const u32 vsize = rd<u32>(raw, sec + 40 * i + 8), va = rd<u32>(raw, sec + 40 * i + 12), rsize = rd<u32>(raw, sec + 40 * i + 16), rptr = rd<u32>(raw, sec + 40 * i + 20);
    size_t n = vsize ? std::min(rsize, vsize) : rsize;
    if (rptr >= raw.size() || va >= img.size()) continue;
    n = std::min<size_t>({n, raw.size() - rptr, img.size() - va});
    memcpy(img.data() + va, raw.data() + rptr, n);
  }
  const u64 delta = m.base - m.preferred;
  const u32 rrva = rd<u32>(raw, dirs + 5 * 8), rsize = rd<u32>(raw, dirs + 5 * 8 + 4);
  if (delta && rrva) {
    for (u32 off = rrva; off + 8 <= rrva + rsize && off + 8 <= img.size();) {
      const u32 page = rd<u32>(img, off), block = rd<u32>(img, off + 4);
      if (block < 8) break;
      for (u32 k = 8; k + 2 <= block; k += 2) {
        const u16 e = rd<u16>(img, off + k);
        if ((e >> 12) == 10) { const size_t at = (size_t)page + (e & 0xfff); if (at + 8 <= img.size()) { u64 v; memcpy(&v, img.data() + at, 8); v += delta; memcpy(img.data() + at, &v, 8); } }
      }
      off += block;
    }
    memcpy(img.data() + opt + 0x18, &m.base, 8);
  }
  const u32 entry = rd<u32>(raw, opt + 0x10);
  m.entry = entry ? m.base + entry : 0;
  const u32 erva = rd<u32>(raw, dirs), esize = rd<u32>(raw, dirs + 4);
  if (erva && erva + 0x28 <= img.size()) {
    const u32 nnames = rd<u32>(img, erva + 0x18), afuncs = rd<u32>(img, erva + 0x1c), anames = rd<u32>(img, erva + 0x20), aords = rd<u32>(img, erva + 0x24);
    for (u32 i = 0; i < nnames; i++) {
      const std::string name = cstr(img, rd<u32>(img, anames + 4 * i));
      const u32 frva = rd<u32>(img, afuncs + 4 * rd<u16>(img, aords + 2 * i));
      if (frva >= erva && frva < erva + esize) m.forwards[name] = cstr(img, frva);
      else if (frva) m.exports[name] = frva;
    }
  }
  m.pdata = rd<u32>(raw, dirs + 3 * 8); m.pdataSize = rd<u32>(raw, dirs + 3 * 8 + 4);
  const u32 trva = rd<u32>(raw, dirs + 9 * 8);
  if (trva && trva + 0x28 <= img.size()) {
    m.hasTls = true; m.tlsStart = rd<u64>(img, trva); m.tlsEnd = rd<u64>(img, trva + 8); m.tlsIndex = rd<u64>(img, trva + 16);
    m.tlsCallbacks = rd<u64>(img, trva + 24); m.tlsFill = rd<u32>(img, trva + 32);
  }
  m.image = std::move(img);
  return true;
}

// the API sets (the names programs ask the loader for) and the DLL which implements each one, from the schema the system ships
void loadApiSet(const std::string& system32, std::unordered_map<std::string, std::string>& hosts, std::vector<u8>& data) {
  std::vector<u8> raw;
  if (!readFile(system32 + "\\apisetschema.dll", raw)) return;
  const u32 nt = rd<u32>(raw, 0x3c), sec = nt + 0x18 + rd<u16>(raw, nt + 0x14);
  for (unsigned i = 0; i < rd<u16>(raw, nt + 6); i++) {
    const size_t o = sec + 40 * i;
    if (o + 40 <= raw.size() && !memcmp(raw.data() + o, ".apiset", 8)) {
      const u32 rsize = rd<u32>(raw, o + 16), rptr = rd<u32>(raw, o + 20);
      if ((size_t)rptr + rsize <= raw.size()) data.assign(raw.begin() + rptr, raw.begin() + rptr + rsize);
    }
  }
  if (data.size() < 28) { data.clear(); return; }
  const u32 version = rd<u32>(data, 0), count = rd<u32>(data, 12), entries = rd<u32>(data, 16);
  if (version < 5) return;
  for (u32 i = 0; i < count; i++) {
    const size_t e = entries + 24 * (size_t)i;
    const u32 noff = rd<u32>(data, e + 4), hlen = rd<u32>(data, e + 12), voff = rd<u32>(data, e + 16), vcount = rd<u32>(data, e + 20);
    if ((size_t)noff + hlen > data.size()) continue;
    const std::string name = lower(wideToText(data.data() + noff, hlen));
    for (u32 k = 0; k < vcount; k++) {
      const size_t v = voff + 20 * (size_t)k;
      const u32 vnlen = rd<u32>(data, v + 8), vvoff = rd<u32>(data, v + 12), vvlen = rd<u32>(data, v + 16);
      if (vnlen == 0 && vvlen && (size_t)vvoff + vvlen <= data.size()) hosts[name] = wideToText(data.data() + vvoff, vvlen);
    }
  }
}
}  // namespace

WinEnv::WinEnv() {
  char buf[MAX_PATH];
  rootDir = GetWindowsDirectoryA(buf, MAX_PATH) ? buf : "C:\\Windows";
  systemDir = rootDir + "\\System32";
  // which system this is: from the shared page of this very process
  const u8* k = (const u8*)0x7ffe0000ull;
  memcpy(&verMajor, k + 0x26c, 4); memcpy(&verMinor, k + 0x270, 4); memcpy(&verBuild, k + 0x260, 4);
  cursor[LDR] = LDR + 0x8000; cursor[PARAMS] = PARAMS + 0x1000;
  defaults(); excModels(); threadModels();
}
WinEnv::~WinEnv() {}

u32 WinEnv::idOf(const std::string& name) {
  auto it = nameId.find(name);
  if (it != nameId.end()) return it->second;
  const u32 id = (u32)names.size();
  names.push_back(name); models.emplace_back(); nameId.emplace(name, id);
  return id;
}
void WinEnv::model(const std::string& name, Model m) { const u32 id = idOf(name); models[id] = std::move(m); }
void WinEnv::alias(const std::string& name, const std::string& as) { const u32 a = idOf(as), n = idOf(name); if (models[a] && !models[n]) models[n] = models[a]; }
bool WinEnv::hasModel(const std::string& name) const { auto it = nameId.find(name); return it != nameId.end() && (bool)models[it->second]; }
std::string WinEnv::apiName(u64 address) const { auto it = apiAt.find(address); return it == apiAt.end() ? std::string() : names[it->second]; }

WinModule* WinEnv::find(const std::string& name) { auto it = modules.find(winKey(name)); return it == modules.end() ? nullptr : it->second; }
WinModule* WinEnv::moduleAt(u64 a) { for (auto& m : order) if (m->contains(a)) return m.get(); return nullptr; }

void WinEnv::hookModule(WinModule* m) { for (auto& kv : m->exports) apiAt.emplace(m->base + kv.second, idOf(kv.first)); }

WinModule* WinEnv::add(Engine& E, const std::string& path, u64 base) {
  auto m = std::make_unique<WinModule>();
  if (!base) base = nextBase;
  if (!loadModule(path, base, *m)) return nullptr;
  if (base == nextBase) nextBase += DLL_STEP;
  E.writeMem(m->base, m->image.data(), m->image.size());
  m->ldr = LDR + 0x1000 + order.size() * 0x200;
  WinModule* p = m.get();
  modules[winKey(m->name)] = p; order.push_back(std::move(m));
  if (ready) enlist(E, p);
  hookModule(p);
  return p;
}

bool WinEnv::listed(Engine& E, WinModule* m) { u64 v = 0; E.readMem(m->ldr + 0x30, &v, 8); return v != 0; }

WinModule* WinEnv::load(Engine& E, const std::string& name) {
  if (WinModule* m = find(name)) {
    if (!m->image.empty()) { u8 b = 0; E.readMem(m->base, &b, 1); if (!b) E.writeMem(m->base, m->image.data(), m->image.size()); }   // loaded on another path: this one has not seen it
    if (ready && !listed(E, m)) enlist(E, m);
    return m;
  }
  std::string base = lower(baseName(name));
  if (base.empty()) return nullptr;
  if (base.rfind("api-ms-", 0) == 0 || base.rfind("ext-ms-", 0) == 0) {
    std::string key = base.size() > 4 && base.compare(base.size() - 4, 4, ".dll") == 0 ? base.substr(0, base.size() - 4) : base;
    const size_t dash = key.rfind('-');
    auto it = dash == std::string::npos ? apiset.end() : apiset.find(key.substr(0, dash));
    return it == apiset.end() ? nullptr : load(E, it->second);
  }
  if (base.find('.') == std::string::npos) base += ".dll";
  if (order.size() >= 48) return nullptr;
  return add(E, systemDir + "\\" + base, 0);
}

u64 WinEnv::resolve(Engine& E, const std::string& dll, const std::string& name, int depth) {
  if (depth > 6) return 0;
  WinModule* m = load(E, dll);
  if (!m) return 0;
  auto e = m->exports.find(name);
  if (e != m->exports.end()) return m->base + e->second;
  auto f = m->forwards.find(name);
  if (f == m->forwards.end()) return 0;
  const size_t dot = f->second.rfind('.');
  if (dot == std::string::npos) return 0;
  return resolve(E, f->second.substr(0, dot), f->second.substr(dot + 1), depth + 1);
}

u64 WinEnv::handleOf(Engine& E, const std::string* name) {
  if (!name) return host ? host->base : 0;
  WinModule* m = find(*name);
  const std::string l = lower(*name);
  if (!m && (l.rfind("api-ms-", 0) == 0 || l.rfind("ext-ms-", 0) == 0)) m = load(E, *name);
  return m && (m == sample || listed(E, m)) ? m->base : 0;
}

// ------------------------------------------------------------------------------------------------ memory
namespace {
struct Wr {
  Engine& E;
  void w(u64 a, const void* p, size_t n) { E.writeMem(a, p, n); }
  void z(u64 a, size_t n) { std::vector<u8> b(n, 0); E.writeMem(a, b.data(), n); }
  void q(u64 a, u64 v) { E.writeMem(a, &v, 8); }
  void d(u64 a, u32 v) { E.writeMem(a, &v, 4); }
  void h(u64 a, u16 v) { E.writeMem(a, &v, 2); }
  void b(u64 a, u8 v) { E.writeMem(a, &v, 1); }
  u64 rq(u64 a) { u64 v = 0; E.readMem(a, &v, 8); return v; }
};
std::vector<u8> wide(const std::string& s) { std::vector<u8> o; for (unsigned char c : s) { o.push_back(c); o.push_back(0); } o.push_back(0); o.push_back(0); return o; }
}  // namespace

u64 WinEnv::allocIn(u64 region, u64 size) { u64& c = cursor[region]; const u64 at = c; c = (at + size + 15) & ~15ull; return at; }

u64 WinEnv::wideStr(Engine& E, u64 region, const std::string& text, u64* bytes) {
  const std::vector<u8> d = wide(text);
  const u64 at = allocIn(region, d.size()); E.writeMem(at, d.data(), d.size());
  if (bytes) *bytes = d.size() - 2;
  return at;
}

void WinEnv::ustr(Engine& E, u64 address, u64 region, const std::string& text) {
  u64 n = 0; const u64 at = wideStr(E, region, text, &n);
  Wr m{E}; m.h(address, (u16)n); m.h(address + 2, (u16)(n + 2)); m.d(address + 4, 0); m.q(address + 8, at);
}

// ------------------------------------------------------------------------------------------------ blocks
void WinEnv::teb(Engine& E) {
  Wr m{E}; const u64 top = STACK_TOP;
  const std::pair<u64, u64> f[] = {{0x00, 0}, {0x08, top}, {0x10, top - STACK_SIZE}, {0x18, 0}, {0x20, 0x1e00}, {0x28, 0}, {0x30, TEB}, {0x38, 0}, {0x40, PID}, {0x48, TID},
                                   {0x50, 0}, {0x58, TLS}, {0x60, PEB}, {0x1478, top - STACK_SIZE}};
  for (auto& kv : f) m.q(TEB + kv.first, kv.second);
  m.d(TEB + 0x68, 0);                 // LastErrorValue
  m.z(TEB + 0x1480, 64 * 8);          // TlsSlots
  m.d(TEB + 0x108, 0x409);            // CurrentLocale
  m.z(FLS, 256 * 8);
}

void WinEnv::peb(Engine& E) {
  Wr m{E};
  m.z(PEB, 0x20);
  m.q(PEB + 0x08, ~0ull);             // Mutant
  m.q(PEB + 0x10, host->base);        // ImageBaseAddress
  m.q(PEB + 0x18, LDR); m.q(PEB + 0x20, PARAMS); m.q(PEB + 0x28, 0);
  m.q(PEB + 0x30, HEAP_HANDLE);       // ProcessHeap
  const u64 lock = allocIn(LDR, 0x28); m.z(lock, 0x28); m.q(PEB + 0x38, lock);
  m.d(PEB + 0xb8, 8); m.d(PEB + 0xbc, 0);                // NumberOfProcessors, NtGlobalFlag
  m.d(PEB + 0x118, verMajor); m.d(PEB + 0x11c, verMinor); m.h(PEB + 0x120, (u16)verBuild); m.h(PEB + 0x122, 0);
  m.d(PEB + 0x124, 2); m.d(PEB + 0x128, 3); m.d(PEB + 0x12c, verMajor); m.d(PEB + 0x130, verMinor);
  m.d(PEB + 0x2c0, 1);                // SessionId
  if (!schema.empty()) { m.w(APISET, schema.data(), schema.size()); m.q(PEB + 0x68, APISET); }
}

// the LDR_DATA_TABLE_ENTRY of a module, where it was given a place
void WinEnv::entry(Engine& E, WinModule* mo) {
  Wr m{E}; const u64 e = mo->ldr;
  m.z(e, 0x120);
  m.q(e + 0x30, mo->base); m.q(e + 0x38, mo->entry); m.d(e + 0x40, (u32)mo->size);
  ustr(E, e + 0x48, LDR, mo->sample ? "C:\\Users\\user\\" + mo->name : systemDir + "\\" + mo->name); ustr(E, e + 0x58, LDR, mo->name);
  m.d(e + 0x68, mo == host ? 0x000022cc : 0x000ca2cc); m.h(e + 0x6c, 0xffff);
  m.q(e + 0x70, e + 0x70); m.q(e + 0x78, e + 0x70);
  m.d(e + 0x80, mo->timestamp); m.q(e + 0xf8, mo->preferred);
  u32 hashed = 0;
  for (char c : mo->name) hashed = hashed * 65599 + (u32)(unsigned char)(c >= 'a' && c <= 'z' ? c - 32 : c);
  m.d(e + 0x108, hashed);
}

// at the end of a list of the loader
void WinEnv::link(Engine& E, u64 head, u64 node) {
  Wr m{E}; const u64 last = m.rq(head + 8);
  m.q(node, head); m.q(node + 8, last); m.q(last, node); m.q(head + 8, node);
}

// a module loaded after the process was built: its entry, at the end of the three lists
void WinEnv::enlist(Engine& E, WinModule* mo) {
  entry(E, mo);
  link(E, LDR + 0x10, mo->ldr); link(E, LDR + 0x20, mo->ldr + 0x10); link(E, LDR + 0x30, mo->ldr + 0x20);
}

void WinEnv::ldr(Engine& E) {
  Wr m{E};
  m.z(LDR, 0x58); m.d(LDR, 0x58); m.d(LDR + 4, 1);
  for (u64 head : {LDR + 0x10, LDR + 0x20, LDR + 0x30}) { m.q(head, head); m.q(head + 8, head); }
  for (auto& mo : order) { entry(E, mo.get()); link(E, LDR + 0x10, mo->ldr); link(E, LDR + 0x20, mo->ldr + 0x10); }
  std::vector<WinModule*> first;
  for (const char* k : {"ntdll", "kernelbase", "kernel32"}) if (WinModule* x = find(k)) first.push_back(x);
  for (WinModule* x : first) link(E, LDR + 0x30, x->ldr + 0x20);
  for (auto& mo : order) if (mo.get() != host && std::find(first.begin(), first.end(), mo.get()) == first.end()) link(E, LDR + 0x30, mo->ldr + 0x20);
  ready = true;
}

void WinEnv::params(Engine& E) {
  Wr m{E}; const u64 p = PARAMS;
  m.z(p, 0x410);
  m.d(p, 0x800); m.d(p + 4, 0x800); m.d(p + 8, 0x6001);
  m.q(p + 0x20, 0x50); m.q(p + 0x28, 0x54); m.q(p + 0x30, 0x58);
  ustr(E, p + 0x38, PARAMS, "C:\\Users\\user\\");
  ustr(E, p + 0x50, PARAMS, systemDir);
  ustr(E, p + 0x60, PARAMS, host->path);
  const std::string command = "rundll32.exe " + sample->name + ",run";
  ustr(E, p + 0x70, PARAMS, command);
  std::string root = rootDir; for (char& c : root) if (c == '\\') c = '/';
  const std::string home = "C:/Users/user";
  std::vector<std::string> vars = {"ALLUSERSPROFILE=C:/ProgramData", "APPDATA=" + home + "/AppData/Roaming", "CommonProgramFiles=C:/Program Files/Common Files",
    "CommonProgramFiles(x86)=C:/Program Files (x86)/Common Files", "CommonProgramW6432=C:/Program Files/Common Files", "COMPUTERNAME=DESKTOP",
    "ComSpec=" + root + "/system32/cmd.exe", "DriverData=" + root + "/System32/Drivers/DriverData", "HOMEDRIVE=C:", "HOMEPATH=/Users/user",
    "LOCALAPPDATA=" + home + "/AppData/Local", "LOGONSERVER=//DESKTOP", "NUMBER_OF_PROCESSORS=8", "OS=Windows_NT",
    "Path=" + root + "/system32;" + root + ";" + root + "/System32/Wbem", "PATHEXT=.COM;.EXE;.BAT;.CMD;.VBS;.VBE;.JS;.JSE;.WSF;.WSH;.MSC",
    "PROCESSOR_ARCHITECTURE=AMD64", "PROCESSOR_IDENTIFIER=Intel64 Family 6 Model 58 Stepping 9, GenuineIntel", "PROCESSOR_LEVEL=6", "PROCESSOR_REVISION=3a09",
    "ProgramData=C:/ProgramData", "ProgramFiles=C:/Program Files", "ProgramFiles(x86)=C:/Program Files (x86)", "ProgramW6432=C:/Program Files",
    "PUBLIC=C:/Users/Public", "SESSIONNAME=Console", "SystemDrive=C:", "SystemRoot=" + root, "TEMP=" + home + "/AppData/Local/Temp",
    "TMP=" + home + "/AppData/Local/Temp", "USERDOMAIN=DESKTOP", "USERDOMAIN_ROAMINGPROFILE=DESKTOP", "USERNAME=user", "USERPROFILE=" + home, "windir=" + root};
  auto upper = [](std::string s) { for (char& c : s) if (c >= 'a' && c <= 'z') c -= 32; return s; };
  std::sort(vars.begin(), vars.end(), [&](const std::string& a, const std::string& b) { return upper(a) < upper(b); });
  std::vector<u8> block;
  for (auto& v : vars) { for (char c : v) { block.push_back(c == '/' ? '\\' : (u8)c); block.push_back(0); } block.push_back(0); block.push_back(0); }
  block.push_back(0); block.push_back(0);
  environmentW = allocIn(PARAMS, block.size()); m.w(environmentW, block.data(), block.size());
  m.q(p + 0x80, environmentW); m.q(p + 0x3f0, block.size());
  commandW = m.rq(p + 0x78);
  commandA = allocIn(PARAMS, command.size() + 1); m.w(commandA, command.c_str(), command.size() + 1);
}

void WinEnv::kuser(Engine& E) {
  Wr m{E}; const u64 k = KUSER;
  m.z(k, 0x3d8);
  m.d(k + 0x004, 0x0fa00000);
  m.d(k + 0x008, 0x61c46800); m.d(k + 0x00c, 8); m.d(k + 0x010, 8);                    // InterruptTime: an hour
  m.d(k + 0x014, 0x4a5f8000); m.d(k + 0x018, 0x01dc7b2d); m.d(k + 0x01c, 0x01dc7b2d);  // SystemTime
  m.h(k + 0x02c, 0x8664); m.h(k + 0x02e, 0x8664);
  const std::vector<u8> r = wide(rootDir); m.w(k + 0x030, r.data(), r.size() - 2);
  m.d(k + 0x244, 0x200000);
  m.d(k + 0x260, verBuild); m.d(k + 0x264, 1); m.b(k + 0x268, 1); m.h(k + 0x26a, 9);
  m.d(k + 0x26c, verMajor); m.d(k + 0x270, verMinor);
  memset(features, 0, sizeof features);
  for (int f : {2, 3, 6, 8, 9, 10, 12, 13, 14, 17, 20, 21, 22, 23, 28, 32, 36, 37, 38}) features[f] = 1;   // no AVX claimed
  m.w(k + 0x274, features, 64);
  m.d(k + 0x2d0, 0x110); m.b(k + 0x2d4, 0); m.b(k + 0x2d5, 0x0a); m.d(k + 0x2d8, 1);
  m.d(k + 0x2e8, 0x7fe00); m.b(k + 0x2f8, 0xc3);
  m.q(k + 0x300, 10000000);
  m.d(k + 0x320, 230400); m.d(k + 0x324, 0); m.d(k + 0x328, 0);                        // TickCount
  m.d(k + 0x330, 0x5a5a1234);
  m.d(k + 0x3c0, 8); m.h(k + 0x3c4, 1);
}

// the thread's copy of the image's TLS template, as the loader makes it for index 0
void WinEnv::tls(Engine& E) {
  Wr m{E};
  m.z(TLS, 0x100);
  if (!sample->hasTls) return;
  const u64 block = TLS + 0x1000, n = sample->tlsEnd > sample->tlsStart ? sample->tlsEnd - sample->tlsStart : 0;
  std::vector<u8> t((size_t)std::min<u64>(n, 1u << 24) + sample->tlsFill + 0x40, 0);
  if (n) E.readMem(sample->tlsStart, t.data(), (size_t)std::min<u64>(n, 1u << 24));
  m.w(block, t.data(), t.size());
  m.q(TLS, block);
}

bool WinEnv::build(Engine& E, const Image& img, const std::string& path) {
  loadApiSet(systemDir, apiset, schema);
  host = add(E, systemDir + "\\rundll32.exe", HOST_BASE);
  if (!host) return false;
  for (const char* n : SYSTEM_DLLS) add(E, systemDir + "\\" + n, 0);
  if (!find("ntdll") || !find("kernel32")) return false;
  auto s = std::make_unique<WinModule>();
  if (!loadModule(path, img.base, *s)) return false;
  s->image.clear(); s->image.shrink_to_fit();      // mapped by loadPE already, with its imports bound to stubs
  s->sample = true; s->ldr = LDR + 0x1000 + order.size() * 0x200;
  sample = s.get(); modules[winKey(s->name)] = sample; order.push_back(std::move(s));
  for (auto& kv : img.stubs) apiAt[kv.first] = idOf(kv.second);
  for (int k = 0; k < 16; k++) apiAt[magic(k)] = idOf("@magic" + std::to_string(k));
  { std::vector<u8> cc(0x100, 0xcc); E.writeMem(MAGIC, cc.data(), cc.size()); }
  teb(E); peb(E); ldr(E); params(E); kuser(E); tls(E);
  Wr m{E};
  m.z(STATE, 0x400); m.q(STATE, ALLOC_BASE); m.q(STATE + 8, 1); m.q(STATE + 0x10, 1);
  E.map(STACK_TOP - STACK_SIZE, STACK_SIZE);
  E.gsbase = TEB;
  return true;
}

void WinEnv::attach(Engine& E) {
  E.apiTable = &apiAt; E.apiLo = HOST_BASE; E.apiHi = 0x7fff00000000ull;
  E.apiCall = [this](Engine& e, u32 id) { return call(e, id); };
  if (exceptions) {
    E.trap = [this](Engine& e, Stop s) { return onTrap(e, s); };
    E.setGuard(nullFaults ? 0x10 : 0);
  } else {
    E.trap = nullptr; E.setGuard(0);
  }
  E.hiFault = exceptions;                               // what is above user space faults, as it does in a process
  E.sysCall = [this](Engine& e) { return onSyscall(e); };
  E.gsbase = TEB;
  E.flushBlocks();
}

Stop WinEnv::onSyscall(Engine& E) {
  if (!sysReady) {
    sysReady = true;
    if (WinModule* nt = find("ntdll")) for (const auto& kv : nt->exports) {
      const std::string& n = kv.first;
      if (n.size() < 3 || n[0] != 'N' || n[1] != 't') continue;
      u8 b[8] = {}; E.readMem(nt->base + kv.second, b, 8);
      if (b[0] == 0x4c && b[1] == 0x8b && b[2] == 0xd1 && b[3] == 0xb8) { u32 num; memcpy(&num, b + 4, 4); sysNames.emplace(num, n); }   // mov r10, rcx; mov eax, number
    }
  }
  sysCalls++;
  const u64 next = E.rip, sp = E.g[RSP];
  const auto it = sysNames.find((u32)E.g[RAX]);
  if (it == sysNames.end()) {
    char b[40]; snprintf(b, sizeof b, "syscall 0x%x", (unsigned)E.g[RAX]); unmodeled[b]++;
    E.g[RAX] = 0xC000001Cull; E.gs[RAX] = 0;            // STATUS_INVALID_SYSTEM_SERVICE
  } else {
    u32 id = idOf(it->second);
    if (!models[id]) { const std::string zw = "Zw" + it->second.substr(2); if (hasModel(zw)) id = idOf(zw); }
    u64 ra = 0; E.readMem(sp, &ra, 8);
    E.g[RCX] = E.g[R10]; E.gs[RCX] = E.gs[R10];          // the first argument, where a called function has it
    sysSite = next;
    const Stop s = call(E, id);
    if (s != ST_NONE) return s;
    if (E.g[RSP] == sp + 8 && E.rip == ra) { E.g[RSP] = sp; E.rip = next; }   // the model returned like a called function: a system call returns after its instruction
  }
  E.g[RCX] = next; E.gs[RCX] = 0; E.g[R11] = E.rflags(); E.gs[R11] = 0;       // what the instruction leaves there
  return ST_NONE;
}

Stop WinEnv::call(Engine& E, u32 id) {
  const std::string& name = names[id];
  Api a{E, *this, name, name.empty() || name.back() != 'A'};
  const bool internal = !name.empty() && name[0] == '@';
  if (!internal) calls[name]++;
  if (trace && !internal) fprintf(stderr, "  api %s(%llx, %llx, %llx, %llx) from %llx\n", name.c_str(), (unsigned long long)E.g[RCX], (unsigned long long)E.g[RDX], (unsigned long long)E.g[R8],
                      (unsigned long long)E.g[R9], (unsigned long long)a.q(E.g[RSP]));
  const Model& m = models[id];
  const u64 sp = E.g[RSP], ra = a.q(sp), site = sysSite ? sysSite : ra; sysSite = 0;
  const bool sym = envSym && !internal && !envKeeps(name);
  if (!m) { unmodeled[name]++; a.ret(0); if (sym) answer(E, site, false); return ST_NONE; }
  if (sym && (envSym & 2) && !envAllocates(name)) { E.recW = true; E.recWrites.clear(); }
  try { m(a); }
  catch (int) { errors[name]++; E.stopInfo.clear(); E.g[RSP] = sp; E.gs[RSP] = 0; a.done = false; a.stop = ST_NONE; }   // a model which cannot answer: the call fails, the path goes on
  catch (const std::bad_alloc&) { throw; }
  catch (const std::exception&) { errors[name]++; E.g[RSP] = sp; E.gs[RSP] = 0; a.done = false; a.stop = ST_NONE; }
  E.recW = false;
  if (!a.done && a.stop == ST_NONE) a.ret(0);
  if (sym && a.stop == ST_NONE && E.rip == ra && E.g[RSP] == sp + 8) answer(E, site, true);
  E.recWrites.clear();
  return a.stop;
}

// what the model answered becomes an input: its result, and (bit 2) the words it wrote for the caller
void WinEnv::answer(Engine& E, u64 site, bool outputs) {
  const u32 occ = E.envOcc(site);
  if ((envSym & 1) && !E.gs[RAX]) {
    const u64 v = E.g[RAX];
    if (v >= 0x10000 && E.isMapped(v)) { if (!E.oracle((site * 0x9E3779B97F4A7C15ull + occ) ^ 0x456e760000000000ull, true)) E.g[RAX] = 0; }
    else { const Val x = E.envValue(site, occ, v); E.g[RAX] = x.c; E.gs[RAX] = x.s; }
  }
  if ((envSym & 2) && outputs) {
    int k = 0;
    for (const auto& w : E.recWrites) {
      if (k >= 32) break;
      const u64 a0 = w.first & ~7ull, a1 = (w.first + w.second + 7) & ~7ull;
      if (a1 - a0 > 0x400 || (a0 >= TEB && a0 < APISET + 0x100000) || (a0 >> 12) == (KUSER >> 12)) continue;
      if (const WinModule* mm = moduleAt(a0)) if (!mm->sample) continue;   // (a system DLL's own data)
      E.markOut(a0, a1 - a0, Engine::OutId{site, occ, (u16)((0x40 + k) << 8)}, true); k++;
    }
  }
}

// ------------------------------------------------------------------------------------------------ Api
u64 Api::arg(int k) const {
  static const int r[4] = {RCX, RDX, R8, R9};
  return k < 4 ? E.g[r[k]] : q(E.g[RSP] + 8 * (u64)(k + 1));
}
Val Api::argv(int k) const {
  static const int r[4] = {RCX, RDX, R8, R9};
  if (k < 4) return Val{E.g[r[k]], E.X.force(E.gs[r[k]])};
  Val v = E.load(E.g[RSP] + 8 * (u64)(k + 1), 8); v.s = E.X.force(v.s); return v;
}
std::string Api::text(u64 a, bool wideChars, size_t limit) const {
  std::string s;
  if (a < 0x10000) return s;
  for (size_t i = 0; i < limit; i++) {
    u16 c = 0; E.readMem(a + i * (wideChars ? 2 : 1), &c, wideChars ? 2 : 1);
    if (!c) break;
    s += (char)(c > 0xff ? '?' : c);
  }
  return s;
}
bool Api::ustring(u64 a, std::string& out) const {
  if (a < 0x10000) return false;
  const u16 n = h(a); const u64 buf = q(a + 8);
  if (buf < 0x10000) return false;
  out.clear();
  for (u16 i = 0; i + 1 < n; i += 2) { u16 c = h(buf + i); out += (char)(c > 0xff ? '?' : c); }
  return true;
}
bool Api::astring(u64 a, std::string& out) const {
  if (a < 0x10000) return false;
  const u16 n = h(a); const u64 buf = q(a + 8);
  if (buf < 0x10000) return false;
  out.resize(n); if (n) E.readMem(buf, out.data(), n);
  return true;
}
void Api::ret(u64 value) { retv(Val{value, 0}); }
// models whose answers follow from what they are given (or which never answer): kept as they are under envSym
bool envKeeps(const std::string& n) {
  static const std::unordered_set<std::string> keep = {"strlen", "wcslen", "lstrlenA", "lstrlenW", "strcmp", "wcscmp", "_stricmp", "_wcsicmp", "strncmp", "wcsncmp",
    "_strnicmp", "_wcsnicmp", "lstrcmpA", "lstrcmpW", "lstrcmpiA", "lstrcmpiW", "LCMapStringEx", "LCMapStringW", "memcpy", "memmove", "memset", "memcmp",
    "RtlCompareMemory", "RtlMoveMemory", "RtlCopyMemory", "RtlZeroMemory", "RtlFillMemory", "RtlInitUnicodeString", "RtlInitAnsiString", "RaiseException",
    "RtlRaiseException", "RtlRaiseStatus", "_CxxThrowException", "RtlUnwindEx", "RtlUnwind", "RtlCaptureContext", "RtlRestoreContext", "NtContinue", "ZwContinue",
    "RtlLookupFunctionEntry", "RtlVirtualUnwind", "RtlPcToFileHeader", "RtlAddFunctionTable", "RtlAddGrowableFunctionTable", "RtlDeleteFunctionTable",
    "AddVectoredExceptionHandler", "RemoveVectoredExceptionHandler", "AddVectoredContinueHandler", "RemoveVectoredContinueHandler", "RtlAddVectoredExceptionHandler",
    "RtlRemoveVectoredExceptionHandler", "RtlAddVectoredContinueHandler", "RtlRemoveVectoredContinueHandler", "SetUnhandledExceptionFilter",
    "RtlSetUnhandledExceptionFilter", "UnhandledExceptionFilter", "TlsGetValue", "TlsSetValue", "FlsGetValue", "FlsSetValue", "GetCurrentProcess",
    "GetCurrentThread", "GetCurrentProcessId", "GetCurrentThreadId", "GetProcessHeap", "GetThreadId", "EncodePointer", "DecodePointer", "RtlEncodePointer",
    "RtlDecodePointer", "SetLastError", "RtlSetLastWin32Error", "EnterCriticalSection", "LeaveCriticalSection", "InitializeCriticalSection",
    "InitializeCriticalSectionAndSpinCount", "InitializeCriticalSectionEx", "DeleteCriticalSection", "AcquireSRWLockExclusive", "ReleaseSRWLockExclusive",
    "AcquireSRWLockShared", "ReleaseSRWLockShared", "InitializeSRWLock", "Sleep", "SleepEx", "NtTerminateProcess", "ZwTerminateProcess", "TerminateProcess",
    "ExitProcess", "ExitThread", "RtlExitUserThread", "GetStartupInfoA", "GetStartupInfoW"};
  return n.empty() || n[0] == '@' || n.compare(0, 11, "Interlocked") == 0 || keep.count(n) != 0;
}
// allocators: what they write is the program's memory (a fill), not an answer
bool envAllocates(const std::string& n) {
  static const std::unordered_set<std::string> al = {"malloc", "_malloc_base", "calloc", "_calloc_base", "realloc", "_realloc_base", "HeapAlloc", "RtlAllocateHeap",
    "HeapReAlloc", "RtlReAllocateHeap", "LocalAlloc", "GlobalAlloc", "VirtualAlloc", "VirtualAllocEx"};
  return al.count(n) != 0;
}
void Api::retv(Val value) {
  const u64 sp = E.g[RSP];
  E.rip = q(sp); E.g[RSP] = sp + 8; E.g[RAX] = value.c; E.gs[RAX] = value.s;
  done = true;
}
u64 Api::alloc(u64 size, u64 align) {
  if (size > WinEnv::BIG) return 0;
  const u64 cur = q(WinEnv::STATE), at = (cur + align - 1) & ~(align - 1);
  putq(WinEnv::STATE, at + std::max<u64>(size, 1));
  return at;
}
u64 Api::teb() const { return E.gsbase ? E.gsbase : WinEnv::TEB; }
void Api::lastError(u32 e) { putd(teb() + 0x68, e); }

void WinEnv::afterInit(Engine& E) {
  const u64 z[2] = {0, 0}; E.writeMem(STATE + 0x400, z, 16);     // the thread table: the first thread only
  E.gsbase = TEB; E.path.clear();
}

bool WinEnv::runInit(Engine& E, u64 maxIns, std::string* info) {
  if (!sample) return false;
  const u64 RET = retAddr;
  auto runOne = [&](u64 fn, u64 reason) -> bool {
    u64 sp = RSP0; E.writeMem(sp, &RET, 8);
    for (int r = 0; r < 16; r++) { E.g[r] = 0; E.gs[r] = 0; }
    E.g[RSP] = sp; E.g[RBP] = sp; E.g[RCX] = sample->base; E.g[RDX] = reason; E.g[R8] = 0;
    E.rip = fn; E.path.clear();
    const bool had = E.stops.count(RET) != 0; E.stops.insert(RET); E.flushBlocks();
    const Stop s = E.run(maxIns);
    if (!had) { E.stops.erase(RET); E.flushBlocks(); }
    if (s == ST_ADDRESS && E.rip == RET) return true;
    if (info) { char b[160]; snprintf(b, sizeof b, "stop %d (%s) at 0x%llx after %llu instructions", (int)s, E.stopInfo.c_str(), (unsigned long long)E.rip, (unsigned long long)E.icount); *info = b; }
    return false;
  };
  if (sample->hasTls && sample->tlsCallbacks)
    for (u64 p = sample->tlsCallbacks, k = 0; k < 16; p += 8, k++) { u64 cb = 0; E.readMem(p, &cb, 8); if (!cb) break; if (!runOne(cb, 1)) return false; }
  if (sample->entry) {
    if (!runOne(sample->entry, 1)) return false;
    if (!(E.g[RAX] & 0xff)) { if (info) *info = "the entry point returned FALSE"; return false; }
  }
  E.path.clear();
  return true;
}

}  // namespace unshroud
