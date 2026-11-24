#include "pe.hpp"
#include <windows.h>
#include <cstdio>
#include <fstream>

namespace unshroud {

bool loadPE(Engine& E, const std::string& path, Image& img, u64 stubBase) {
  std::vector<u8> d;
  {
    FILE* f = fopen(path.c_str(), "rb");
    if (!f) return false;
    fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
    if (sz > 0) { d.resize((size_t)sz); if (fread(d.data(), 1, d.size(), f) != d.size()) d.clear(); }
    fclose(f);
  }
  if (d.size() < 0x200) return false;
  auto* dos = (IMAGE_DOS_HEADER*)d.data();
  auto* nt = (IMAGE_NT_HEADERS64*)(d.data() + dos->e_lfanew);
  if (nt->Signature != IMAGE_NT_SIGNATURE || nt->OptionalHeader.Magic != IMAGE_NT_OPTIONAL_HDR64_MAGIC) return false;
  img.base = nt->OptionalHeader.ImageBase; img.size = nt->OptionalHeader.SizeOfImage; img.entry = img.base + nt->OptionalHeader.AddressOfEntryPoint;
  E.map(img.base, img.size);
  E.writeMem(img.base, d.data(), std::min<size_t>(nt->OptionalHeader.SizeOfHeaders, d.size()));
  auto* sec = IMAGE_FIRST_SECTION(nt);
  for (unsigned i = 0; i < nt->FileHeader.NumberOfSections; i++) {
    size_t raw = std::min<size_t>(sec[i].SizeOfRawData, sec[i].Misc.VirtualSize ? sec[i].Misc.VirtualSize : sec[i].SizeOfRawData);
    if (sec[i].PointerToRawData + raw > d.size()) raw = d.size() > sec[i].PointerToRawData ? d.size() - sec[i].PointerToRawData : 0;
    if (raw) E.writeMem(img.base + sec[i].VirtualAddress, d.data() + sec[i].PointerToRawData, raw);
    if ((sec[i].Characteristics & IMAGE_SCN_MEM_WRITE) && sec[i].Misc.VirtualSize) img.writable.push_back({img.base + sec[i].VirtualAddress, sec[i].Misc.VirtualSize});
  }
  auto rvaPtr = [&](u32 rva) -> u8* {
    for (unsigned i = 0; i < nt->FileHeader.NumberOfSections; i++)
      if (rva >= sec[i].VirtualAddress && rva < sec[i].VirtualAddress + std::max(sec[i].SizeOfRawData, sec[i].Misc.VirtualSize))
        return d.data() + sec[i].PointerToRawData + (rva - sec[i].VirtualAddress);
    return nullptr;
  };
  auto& idir = nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT];
  u64 next = stubBase + 0x10;
  if (idir.VirtualAddress) {
    for (auto* imp = (IMAGE_IMPORT_DESCRIPTOR*)rvaPtr(idir.VirtualAddress); imp && imp->Name; imp++) {
      u32 thunkRva = imp->OriginalFirstThunk ? imp->OriginalFirstThunk : imp->FirstThunk;
      auto* th = (u64*)rvaPtr(thunkRva);
      for (u32 k = 0; th && th[k]; k++) {
        std::string name = "?";
        if (!(th[k] >> 63)) { u8* p = rvaPtr((u32)th[k]); if (p) name = (const char*)(p + 2); }
        else name = "#" + std::to_string(th[k] & 0xffff);
        u64 slot = img.base + imp->FirstThunk + 8ull * k;
        E.writeMem(slot, &next, 8);
        img.stubs[next] = name;
        next += 0x10;
      }
    }
    E.map(stubBase, next - stubBase + 0x10);
    std::vector<u8> ret(next - stubBase + 0x10, 0xC3);
    E.writeMem(stubBase, ret.data(), ret.size());
  }
  auto& edir = nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXCEPTION];
  if (edir.VirtualAddress) {
    auto* rf = (RUNTIME_FUNCTION*)rvaPtr(edir.VirtualAddress);
    for (u32 i = 0; rf && i < edir.Size / sizeof(RUNTIME_FUNCTION); i++) img.funcs.push_back({rf[i].BeginAddress, rf[i].EndAddress - rf[i].BeginAddress});
  }
  return true;
}

}  // namespace unshroud
