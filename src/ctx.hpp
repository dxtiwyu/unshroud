// unshroud - real calling contexts (tools/unshroud_ctx.cpp output): the registers at a function's entry in a recorded run, the
// memory it read before writing it, what its calls out of the module returned. An explorer starts the function there:
// the values are the inputs' first values, so the first run follows the recorded one and the others go around it.
#pragma once
#include "expr.hpp"
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

namespace unshroud {

struct RealCtx {
  u64 entry = 0, rsp = 0;
  std::map<std::string, u64> regs;                        // rax .. r15, rip (xmm left out)
  std::vector<std::pair<u64, std::vector<u8>>> mem;       // address -> bytes, as the recorded process had them
  std::vector<std::pair<u64, u64>> api;                   // (call site rva, rax after it), in order
};
// the first context of each entry rva in a JSON-lines file
bool loadContexts(const std::string& path, std::unordered_map<u64, RealCtx>& out);
// address ranges of the recorded process -> this engine (modules at other bases, the stack elsewhere)
struct Reloc {
  struct R { u64 lo, hi, to; };
  std::vector<R> r;
  void add(u64 lo, u64 size, u64 to) { r.push_back({lo, lo + size, to}); }
  u64 operator()(u64 v) const { for (const R& x : r) if (v >= x.lo && v < x.hi) return v - x.lo + x.to; return v; }
  bool inside(u64 v) const { for (const R& x : r) if (v >= x.lo && v < x.hi) return true; return false; }
};
// the modules of a ".modules" file (lines: event base size traced name path): lower-case name -> (base, size)
std::map<std::string, std::pair<u64, u64>> loadModuleList(const std::string& path);

}  // namespace unshroud
