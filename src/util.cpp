#include "util.hpp"
#include <windows.h>
#include <cstdlib>
#include <cstdio>

namespace unshroud {
void limitMemory(size_t mb) {
  if (const char* e = getenv("UNSHROUD_MEM_MB")) mb = (size_t)atoll(e);
  if (!mb) return;
  HANDLE job = CreateJobObjectW(nullptr, nullptr);
  if (!job) return;
  JOBOBJECT_EXTENDED_LIMIT_INFORMATION li{};
  li.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_PROCESS_MEMORY;
  li.ProcessMemoryLimit = mb << 20;
  if (!SetInformationJobObject(job, JobObjectExtendedLimitInformation, &li, sizeof li) || !AssignProcessToJobObject(job, GetCurrentProcess()))
    fprintf(stderr, "unshroud: no memory limit (error %lu)\n", GetLastError());
}
}  // namespace unshroud
