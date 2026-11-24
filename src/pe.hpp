// unshroud - mapping a PE image (no loader work: imports point at stubs)
#pragma once
#include "engine.hpp"
#include <map>
#include <string>

namespace unshroud {

struct Image {
  u64 base = 0, size = 0, entry = 0;
  std::map<u64, std::string> stubs;          // stub address -> imported function name
  std::vector<std::pair<u64, u64>> funcs;    // exception directory: (start rva, size)
  std::vector<std::pair<u64, u64>> writable; // writable sections: (address, size)
};

bool loadPE(Engine& E, const std::string& path, Image& img, u64 stubBase = 0x7ffe00000000ull);

}  // namespace unshroud
