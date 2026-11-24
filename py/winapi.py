"""System functions for code unshroud explores inside the synthetic process of winenv.py.

Every import stub of the image and every export of the mapped system DLLs is hooked: a call there runs the model of that
function (by name) and returns to the caller. Functions which answer from the process (its modules, its blocks, memory)
answer like the system would; the rest return 0. What the models change lives in emulated memory (allocation cursors
included), so every run of the explorer starts from the same process.
"""
import collections, struct
from winenv import FLS, HEAP_HANDLE, MASK64, PID, TEB, TID, KUSER

ALLOC_BASE = 0x7e0000000000          # VirtualAlloc / heap blocks
BIG = 1 << 30                         # an allocation bigger than this fails, as it would on a real system
STATE = TEB + 0x4f0000               # allocation cursor, next TLS / FLS index
ALIASES = {"GetModuleHandleA": "GetModuleHandleW", "LoadLibraryA": "LoadLibrary", "LoadLibraryW": "LoadLibrary",
           "LoadLibraryExA": "LoadLibrary", "LoadLibraryExW": "LoadLibrary", "GetModuleFileNameA": "GetModuleFileNameW",
           "DecodePointer": "EncodePointer", "RtlEncodePointer": "EncodePointer", "RtlDecodePointer": "EncodePointer",
           "RtlAllocateHeap": "HeapAlloc", "RtlFreeHeap": "HeapFree", "RtlReAllocateHeap": "HeapReAlloc", "RtlSizeHeap": "HeapSize",
           "GetTickCount64": "GetTickCount", "FlsGetValue2": "FlsGetValue", "RtlSetLastWin32Error": "SetLastError",
           "RtlGetLastWin32Error": "GetLastError", "VirtualAllocEx": "VirtualAllocEx", "LdrGetProcedureAddressForCaller": "LdrGetProcedureAddress",
           "LdrGetProcedureAddressEx": "LdrGetProcedureAddress", "InitializeCriticalSectionAndSpinCount": "Ok1",
           "InitializeCriticalSectionEx": "Ok1", "EnterCriticalSection": "Zero", "LeaveCriticalSection": "Zero",
           "InitializeCriticalSection": "Zero", "DeleteCriticalSection": "Zero", "RtlEnterCriticalSection": "Zero",
           "RtlLeaveCriticalSection": "Zero", "InitializeSListHead": "Zero", "IsDebuggerPresent": "Zero", "TlsFree": "Ok1",
           "FlsFree": "Ok1", "VirtualFree": "Ok1", "VirtualFreeEx": "Ok1", "CloseHandle": "Ok1", "NtClose": "Zero",
           "malloc": "Malloc", "calloc": "Calloc", "free": "Zero", "_malloc_base": "Malloc", "_calloc_base": "Calloc", "_free_base": "Zero",
           "AcquireSRWLockExclusive": "Zero", "ReleaseSRWLockExclusive": "Zero", "AcquireSRWLockShared": "Zero",
           "ReleaseSRWLockShared": "Zero", "RtlAcquireSRWLockExclusive": "Zero", "RtlReleaseSRWLockExclusive": "Zero",
           "GetSystemTimePreciseAsFileTime": "GetSystemTimeAsFileTime", "NtQueryPerformanceCounter": "QueryPerformanceCounter",
           "RtlQueryPerformanceCounter": "QueryPerformanceCounter", "RtlQueryPerformanceFrequency": "QueryPerformanceFrequency"}


class Api:
    def __init__(self, e, env):
        self.e = e; self.env = env
        self.calls = collections.Counter(); self.unknown = collections.Counter(); self.errors = collections.Counter()
        self.table = {n[3:]: getattr(self, n) for n in dir(self) if n.startswith("do_")}
        for a, b in ALIASES.items():
            if b in self.table: self.table.setdefault(a, self.table[b])
        self.init_state()

    def init_state(self):
        """The allocation cursor and the next TLS / FLS indexes, in emulated memory: call it after every restore of a
        state saved before this Api existed."""
        self.e.write(STATE, struct.pack("<QQQ", ALLOC_BASE, 1, 1))

    # ---------------------------------------------------------------------------------------------- plumbing
    def arg(self, k):
        if k < 4: return self.e.reg(("rcx", "rdx", "r8", "r9")[k])
        return self.q(self.e.reg("rsp") + 8 * (k + 1))
    def q(self, a): return struct.unpack("<Q", self.e.read(a, 8))[0]
    def d(self, a): return struct.unpack("<I", self.e.read(a, 4))[0]
    def put(self, a, data):
        if a >= 0x10000: self.e.write(a, bytes(data))
    def putq(self, a, v): self.put(a, struct.pack("<Q", v & MASK64))
    def putd(self, a, v): self.put(a, struct.pack("<I", v & 0xffffffff))
    def text(self, a, wide, limit=520):
        if a < 0x10000: return None
        step = 2 if wide else 1
        raw = self.e.read(a, limit * step); out = []
        for i in range(0, len(raw), step):
            c = raw[i] | (raw[i + 1] << 8) if wide else raw[i]
            if c == 0: break
            out.append(chr(c))
        return "".join(out)
    def ustring(self, a):                 # UNICODE_STRING / ANSI_STRING at a
        if a < 0x10000: return None
        n, _, _, buf = struct.unpack("<HHIQ", self.e.read(a, 16))
        return self.e.read(buf, n).decode("utf-16-le", "replace") if buf >= 0x10000 else None
    def astring(self, a):
        if a < 0x10000: return None
        n, _, _, buf = struct.unpack("<HHIQ", self.e.read(a, 16))
        return self.e.read(buf, n).decode("latin1") if buf >= 0x10000 else None
    def ret(self, value=0):
        e = self.e; sp = e.reg("rsp")
        e.rip = self.q(sp); e.set_reg("rsp", sp + 8); e.set_reg("rax", value & MASK64)
    def alloc(self, size, align=16):
        """A block from the bump allocator (in emulated memory: every run starts over); 0 when too big. Not mapped
        ahead: unmapped memory reads as zero and a write maps its page."""
        if size > BIG: return 0
        cur = self.q(STATE)
        at = (cur + align - 1) & ~(align - 1)
        self.putq(STATE, at + max(size, 1))
        return at

    def hook(self, name):
        fn = self.table.get(name)
        def h(en):
            self.calls[name] += 1
            if fn is None:
                self.unknown[name] += 1; self.ret(0)
                return None
            try:
                fn()
            except Exception:                       # a model which cannot answer: the call fails, the path goes on
                self.errors[name] += 1; self.ret(0)
            return None
        return h

    # ---------------------------------------------------------------------------------------------- modules
    def module_handle(self, name):
        if name is None: return self.env.host.base
        m = self.env.find(name)
        if m is None and name.lower().startswith(("api-ms-", "ext-ms-")): m = self.env.load(name)
        return m.base if m is not None and (m is self.env.sample or self.env.listed(m)) else 0
    def do_GetModuleHandleW(self):
        self.ret(self.module_handle(self.text(self.arg(0), self.wide_call)))
    def do_GetModuleHandleExW(self):
        flags, name, out = self.arg(0), self.arg(1), self.arg(2)
        h = self.env.module_at(name).base if flags & 4 and self.env.module_at(name) else self.module_handle(self.text(name, True))
        self.putq(out, h); self.ret(1 if h else 0)
    def do_LoadLibrary(self):
        name = self.text(self.arg(0), True) if self.wide_call else self.text(self.arg(0), False)
        m = self.env.load(name) if name else None
        self.ret(m.base if m else 0)
    def do_GetProcAddress(self):
        h, n = self.arg(0), self.arg(1)
        m = self.env.module_at(h)
        if m is None or n < 0x10000: return self.ret(0)
        a = self.env.resolve(m.name, self.text(n, False))
        self.ret(a or 0)
    def do_LdrLoadDll(self):
        name = self.ustring(self.arg(2)); m = self.env.load(name) if name else None
        if m: self.putq(self.arg(3), m.base)
        self.ret(0 if m else 0xC0000135)
    def do_LdrGetDllHandle(self):
        h = self.module_handle(self.ustring(self.arg(2)))
        if h: self.putq(self.arg(3), h)
        self.ret(0 if h else 0xC0000135)
    def do_LdrGetProcedureAddress(self):
        m = self.env.module_at(self.arg(0)); name = self.astring(self.arg(1))
        a = self.env.resolve(m.name, name) if m and name else None
        if a: self.putq(self.arg(3), a)
        self.ret(0 if a else 0xC0000139)
    def do_GetModuleFileNameW(self):
        h, buf, size = self.arg(0), self.arg(1), self.arg(2)
        m = self.env.module_at(h) if h else self.env.host
        path = (m.path if m is not self.env.sample else "C:" + chr(92) + "Users" + chr(92) + "user" + chr(92) + m.name) if m else ""
        wide = self.wide_call
        data = (path.encode("utf-16-le") + b"\0\0") if wide else (path.encode("latin1") + b"\0")
        room = size * (2 if wide else 1)
        self.put(buf, data[:room]); self.ret(min(len(path), max(size - 1, 0)))

    # ---------------------------------------------------------------------------------------------- memory
    def do_VirtualAlloc(self):
        addr, size = self.arg(0), self.arg(1)
        if size > BIG: return self.ret(0)
        if addr: return self.ret(addr)
        self.ret(self.alloc(size, 0x10000))
    def do_VirtualAllocEx(self):
        addr, size = self.arg(1), self.arg(2)
        if size > BIG: return self.ret(0)
        if addr: return self.ret(addr)
        self.ret(self.alloc(size, 0x10000))
    def do_NtAllocateVirtualMemory(self):
        pbase, psize = self.arg(1), self.arg(3)
        base, size = self.q(pbase), self.q(psize)
        if size > BIG: return self.ret(0xC0000017)
        if not base: base = self.alloc(size, 0x10000)
        self.putq(pbase, base); self.ret(0)
    def do_VirtualProtect(self):
        if self.arg(3): self.putd(self.arg(3), 0x40)
        self.ret(1)
    def do_NtProtectVirtualMemory(self):
        if self.arg(4): self.putd(self.arg(4), 0x40)
        self.ret(0)
    def do_HeapAlloc(self): self.ret(self.alloc(self.arg(2)))
    def do_HeapReAlloc(self):
        old, size = self.arg(2), self.arg(3)
        new = self.alloc(size)
        if new and old >= 0x10000: self.put(new, self.e.read(old, min(size, 1 << 20)))
        self.ret(new)
    def do_HeapFree(self): self.ret(1)
    def do_HeapSize(self): self.ret(0x100)
    def do_Malloc(self): self.ret(self.alloc(self.arg(0)))
    def do_Calloc(self): n = self.arg(0) * self.arg(1); self.ret(self.alloc(n) if n <= BIG else 0)
    def do_GetProcessHeap(self): self.ret(HEAP_HANDLE)
    def do_GetSystemInfo(self):
        si = struct.pack("<HHIQQQIIIHH", 9, 0, 0x1000, 0x10000, 0x7ffffffeffff, 0xff, 8, 8664, 0x10000, 6, 0x3a09)
        self.put(self.arg(0), si); self.ret(0)

    # ---------------------------------------------------------------------------------------------- thread / process
    def teb(self): return self.e.gsbase or TEB
    def do_GetLastError(self): self.ret(self.d(self.teb() + 0x68))
    def do_SetLastError(self): self.putd(self.teb() + 0x68, self.arg(0)); self.ret(0)
    def do_TlsAlloc(self):
        k = self.q(STATE + 8); self.putq(STATE + 8, k + 1); self.ret(k if k < 64 else 0xffffffff)
    def do_TlsGetValue(self): k = self.arg(0); self.ret(self.q(self.teb() + 0x1480 + 8 * k) if k < 64 else 0)
    def do_TlsSetValue(self):
        k = self.arg(0)
        if k < 64: self.putq(self.teb() + 0x1480 + 8 * k, self.arg(1))
        self.ret(1 if k < 64 else 0)
    def do_FlsAlloc(self):
        k = self.q(STATE + 16); self.putq(STATE + 16, k + 1); self.ret(k if k < 256 else 0xffffffff)
    def do_FlsGetValue(self): k = self.arg(0); self.ret(self.q(FLS + 8 * k) if k < 256 else 0)
    def do_FlsSetValue(self):
        k = self.arg(0)
        if k < 256: self.putq(FLS + 8 * k, self.arg(1))
        self.ret(1 if k < 256 else 0)
    def do_GetCurrentProcess(self): self.ret(MASK64)
    def do_GetCurrentThread(self): self.ret(MASK64 - 1)
    def do_GetCurrentProcessId(self): self.ret(PID)
    def do_GetCurrentThreadId(self): self.ret(TID)
    def do_EncodePointer(self): self.ret(self.arg(0))
    def do_CheckRemoteDebuggerPresent(self): self.putd(self.arg(1), 0); self.ret(1)
    def do_NtQueryInformationProcess(self):
        buf, n, out = self.arg(2), self.arg(3), self.arg(4)
        if buf >= 0x10000 and n < 0x10000: self.put(buf, bytes(n))
        if out >= 0x10000: self.putd(out, n)
        self.ret(0)
    def do_IsProcessorFeaturePresent(self): self.ret(1 if self.arg(0) < 64 and self.env.features[self.arg(0)] else 0)
    def do_GetCommandLineW(self): self.ret(self.env.command_w)
    def do_GetCommandLineA(self): self.ret(self.env.command_a)
    def do_GetEnvironmentStringsW(self): self.ret(self.env.environment)
    def do_Ok1(self): self.ret(1)
    def do_Zero(self): self.ret(0)

    # ---------------------------------------------------------------------------------------------- time
    def do_QueryPerformanceCounter(self): self.putq(self.arg(0), 0x2540be400); self.ret(1)
    def do_QueryPerformanceFrequency(self): self.putq(self.arg(0), 10000000); self.ret(1)
    def do_GetTickCount(self): self.ret(230400)
    def do_GetSystemTimeAsFileTime(self): self.putq(self.arg(0), 0x01dc7b2d4a5f8000); self.ret(0)


def install(e, env, stubs):
    """Hooks the image's import stubs and the exports of every mapped system module. Returns the Api (call counters)."""
    api = Api(e, env)
    orig = api.hook
    def hook(name):
        fn = orig(name)
        def h(en):
            api.cur_name = name; api.wide_call = not name.endswith("A")
            return fn(en)
        return h
    for a, n in stubs.items(): e.hook(a, hook(n))
    for m in env.order:
        if m is env.sample: continue
        for n, rva in m.exports.items(): e.hook(m.base + rva, hook(n))
    return api
