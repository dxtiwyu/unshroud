// unshroud - process guards
#pragma once
#include <cstddef>
namespace unshroud {
// the whole process may use at most `mb` megabytes (UNSHROUD_MEM_MB overrides; 0: no limit). Windows job object.
void limitMemory(size_t mb = 3072);
}
