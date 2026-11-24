"""opq_mem.py: keep gen_opaque.py from exhausting the machine's memory.

cap(job_mb) puts this process into a new Windows job object whose processes together
may commit at most job_mb MB (JOB_OBJECT_LIMIT_JOB_MEMORY); children (clang, lld,
validate.py) start inside the job and count against the same limit. Past the limit
an allocation fails (MemoryError / z3 'out of memory') instead of the machine
swapping. z3_limits(mb) also sets z3's own limits: past memory_high_watermark_mb a
check() returns unknown, past memory_max_size z3 raises. peak_mb() reports the
peak commit of the job (all its processes together).
"""
import ctypes
from ctypes import wintypes

JOB_OBJECT_LIMIT_JOB_MEMORY = 0x200
JobObjectExtendedLimitInformation = 9


class _IO(ctypes.Structure):
    _fields_ = [(n, ctypes.c_ulonglong) for n in ('r', 'w', 'o', 'rb', 'wb', 'ob')]


class _BASIC(ctypes.Structure):
    _fields_ = [('PerProcessUserTimeLimit', ctypes.c_int64), ('PerJobUserTimeLimit', ctypes.c_int64),
                ('LimitFlags', wintypes.DWORD), ('MinimumWorkingSetSize', ctypes.c_size_t),
                ('MaximumWorkingSetSize', ctypes.c_size_t), ('ActiveProcessLimit', wintypes.DWORD),
                ('Affinity', ctypes.c_size_t), ('PriorityClass', wintypes.DWORD),
                ('SchedulingClass', wintypes.DWORD)]


class _EXT(ctypes.Structure):
    _fields_ = [('Basic', _BASIC), ('Io', _IO), ('ProcessMemoryLimit', ctypes.c_size_t),
                ('JobMemoryLimit', ctypes.c_size_t), ('PeakProcessMemoryUsed', ctypes.c_size_t),
                ('PeakJobMemoryUsed', ctypes.c_size_t)]


_k32 = ctypes.WinDLL('kernel32', use_last_error=True)
_k32.CreateJobObjectW.restype = wintypes.HANDLE
_k32.CreateJobObjectW.argtypes = [ctypes.c_void_p, wintypes.LPCWSTR]
_k32.SetInformationJobObject.argtypes = [wintypes.HANDLE, ctypes.c_int, ctypes.c_void_p, wintypes.DWORD]
_k32.QueryInformationJobObject.argtypes = [wintypes.HANDLE, ctypes.c_int, ctypes.c_void_p,
                                           wintypes.DWORD, ctypes.c_void_p]
_k32.AssignProcessToJobObject.argtypes = [wintypes.HANDLE, wintypes.HANDLE]
_k32.GetCurrentProcess.restype = wintypes.HANDLE
_JOB = None


def cap(job_mb=3072):
    """Limit this process and its future children to job_mb MB of commit in total.
    Returns True when the limit is in place."""
    global _JOB
    if _JOB is not None:
        return True
    job = _k32.CreateJobObjectW(None, None)
    if not job:
        return False
    info = _EXT()
    info.Basic.LimitFlags = JOB_OBJECT_LIMIT_JOB_MEMORY
    info.JobMemoryLimit = job_mb << 20
    if not _k32.SetInformationJobObject(job, JobObjectExtendedLimitInformation,
                                        ctypes.byref(info), ctypes.sizeof(info)):
        return False
    if not _k32.AssignProcessToJobObject(job, _k32.GetCurrentProcess()):
        return False
    _JOB = job
    return True


def peak_mb():
    """Peak commit (MB) of the whole job so far, or None without cap()."""
    if _JOB is None:
        return None
    info = _EXT()
    if not _k32.QueryInformationJobObject(_JOB, JobObjectExtendedLimitInformation,
                                          ctypes.byref(info), ctypes.sizeof(info), None):
        return None
    return info.PeakJobMemoryUsed >> 20


def z3_limits(mb=1024):
    """z3 stops (unknown) past mb MB and raises past 1.5 * mb MB."""
    import z3
    z3.set_param('memory_high_watermark_mb', mb)
    z3.set_param('memory_max_size', mb + mb // 2)
