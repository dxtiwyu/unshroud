"""A process for the image to run in: what a running process has and a file does not.

The thread and process blocks (TEB, PEB), the loader's list of modules with the system DLLs of this machine mapped as
data (their headers and export tables are what code which finds its imports by itself walks), the process parameters,
the shared system page. Nothing of it is ever run natively: a call which lands in a system DLL is emulated by the
explorer (ex3_api.py).
"""
import os, struct, sys

# the layout of the process (as the Triton-fork explorer had it)
RSP = 0x7f0000000000 - 0x10000
STACK_SIZE = 0x100000
TEB = 0x7fd000000000
THREAD_STEP = 0x10000000
KUSER = 0x7ffe0000


class MemoryAccess:
    def __init__(self, address, size): self.address = address; self.size = size


class TritonShim:
    """The few Triton names the environment code uses."""
    MemoryAccess = MemoryAccess


class EngineCtx:
    """An unshroud Engine seen through the Triton context calls this module makes."""
    def __init__(self, e): self.e = e
    def setConcreteMemoryAreaValue(self, address, data): self.e.write(address, bytes(data))
    def getConcreteMemoryAreaValue(self, address, size): return self.e.read(address, size)
    def isConcreteMemoryValueDefined(self, address, size): return any(self.e.read(address, size))   # written there (unmapped reads are 0)
    def symbolizeMemory(self, access, alias): self.e.symbolize_mem(access.address, access.size, alias)

PEB = TEB + 0x100000
LDR = TEB + 0x200000
PARAMS = TEB + 0x300000
TLS = TEB + 0x400000
FLS = TEB + 0x480000
ENV_END = TEB + 0x500000
HOST_BASE = 0x7ff610000000
DLL_BASE = 0x7ff810000000
DLL_STEP = 0x10000000
HEAP_HANDLE = 0x7fb000000000
PID, TID = 0x1a2c, 0x1f40
APISET = TEB + 0x500000
SYSTEM_DLLS = ("ntdll.dll", "kernel32.dll", "KernelBase.dll", "advapi32.dll", "msvcrt.dll", "sechost.dll", "rpcrt4.dll",
               "bcryptprimitives.dll", "ucrtbase.dll")
MASK64 = (1 << 64) - 1


def u16(b, o): return struct.unpack_from("<H", b, o)[0]
def u32(b, o): return struct.unpack_from("<I", b, o)[0]
def u64(b, o): return struct.unpack_from("<Q", b, o)[0]


def cstr(b, o):
    return bytes(b[o:b.index(0, o)]).decode("latin1")


class Module:
    __slots__ = ("name", "path", "base", "size", "entry", "exports", "forwards", "image", "timestamp", "preferred", "tls", "ldr")

    def contains(self, address):
        return self.base <= address < self.base + self.size


def load_pe(path, base=None):
    """A PE file laid out as the loader does, relocated to `base`: its bytes, its exports."""
    raw = open(path, "rb").read()
    nt = u32(raw, 0x3c); opt = nt + 0x18
    if u16(raw, opt) != 0x20b: raise ValueError("%s is not a 64-bit image" % path)
    m = Module(); m.path = path; m.name = os.path.basename(path)
    m.preferred = u64(raw, opt + 0x18); m.size = u32(raw, opt + 0x38); m.timestamp = u32(raw, nt + 8)
    m.base = m.preferred if base is None else base
    headers = u32(raw, opt + 0x3c); dirs = opt + 0x70
    img = bytearray(m.size)
    img[:headers] = raw[:headers]
    sec = opt + u16(raw, nt + 0x14)
    for i in range(u16(raw, nt + 6)):
        vsize, va, rsize, rptr = struct.unpack_from("<IIII", raw, sec + 40 * i + 8)
        n = min(rsize, vsize) if vsize else rsize
        img[va:va + n] = raw[rptr:rptr + n]
    delta = (m.base - m.preferred) & MASK64
    rva, size = struct.unpack_from("<II", raw, dirs + 5 * 8)
    if delta and rva:
        off = rva
        while off < rva + size:
            page, block = struct.unpack_from("<II", img, off)
            if block < 8: break
            for e in struct.unpack_from("<%dH" % ((block - 8) // 2), img, off + 8):
                if e >> 12 == 10:
                    at = page + (e & 0xfff)
                    struct.pack_into("<Q", img, at, (u64(img, at) + delta) & MASK64)
            off += block
        struct.pack_into("<Q", img, opt + 0x18, m.base)
    entry = u32(raw, opt + 0x10)
    m.entry = m.base + entry if entry else 0
    m.exports = {}; m.forwards = {}
    erva, esize = struct.unpack_from("<II", raw, dirs)
    if erva:
        nfuncs, nnames, afuncs, anames, aords = struct.unpack_from("<IIIII", img, erva + 0x14)
        for i in range(nnames):
            name = cstr(img, u32(img, anames + 4 * i))
            frva = u32(img, afuncs + 4 * u16(img, aords + 2 * i))
            if erva <= frva < erva + esize: m.forwards[name] = cstr(img, frva)
            elif frva: m.exports[name] = frva
    trva, tsize = struct.unpack_from("<II", raw, dirs + 9 * 8)
    m.tls = struct.unpack_from("<QQQQII", img, trva) if trva else None      # start, end, index, callbacks, zero fill, characteristics
    m.image = bytes(img)
    return m


def load_apiset(system32):
    """The API sets (the names programs ask the loader for) and the DLL which implements each one, from the schema the
    system ships. Returns the mapping and the schema itself (what the PEB points to)."""
    try:
        raw = open(os.path.join(system32, "apisetschema.dll"), "rb").read()
    except OSError:
        return {}, b""
    nt = u32(raw, 0x3c); sec = nt + 0x18 + u16(raw, nt + 0x14); data = b""
    for i in range(u16(raw, nt + 6)):
        o = sec + 40 * i
        if raw[o:o + 8].rstrip(b"\0") == b".apiset":
            vsize, va, rsize, rptr = struct.unpack_from("<IIII", raw, o + 8)
            data = raw[rptr:rptr + rsize]
    if len(data) < 28: return {}, b""
    version, size, flags, count, entries, hashes, factor = struct.unpack_from("<7I", data, 0)
    if version < 5: return {}, data
    hosts = {}
    for i in range(count):
        eflags, noff, nlen, hlen, voff, vcount = struct.unpack_from("<6I", data, entries + 24 * i)
        name = data[noff:noff + hlen].decode("utf-16-le").lower()
        for k in range(vcount):
            vflags, vnoff, vnlen, vvoff, vvlen = struct.unpack_from("<5I", data, voff + 20 * k)
            if vnlen == 0 and vvlen:
                hosts[name] = data[vvoff:vvoff + vvlen].decode("utf-16-le")
    return hosts, data


class Environment:
    """The process: built once in the context, before the state every function starts from is saved."""

    def __init__(self, triton, ctx, image, path):
        self.t = triton; self.ctx = ctx; self.image = image
        self.root = os.environ.get("SystemRoot", r"C:\Windows")
        self.system32 = os.path.join(self.root, "System32")
        self.version = tuple(sys.getwindowsversion()[:3])
        self.modules = {}; self.order = []; self.api_at = {}; self.next_base = DLL_BASE
        self.cursor = {LDR: LDR + 0x8000, PARAMS: PARAMS + 0x1000}
        self.apiset, self.schema = load_apiset(self.system32)
        self.ready = False                            # True once the lists of the loader are built
        self.host = self.add(os.path.join(self.system32, "rundll32.exe"), HOST_BASE)
        for name in SYSTEM_DLLS:
            if os.path.isfile(os.path.join(self.system32, name)): self.add(os.path.join(self.system32, name))
        self.sample = load_pe(path, image.base)
        self.sample.image = None                      # mapped by the explorer already, with its imports bound
        self.sample.ldr = LDR + 0x1000 + len(self.order) * 0x200
        self.modules[self.key(self.sample.name)] = self.sample; self.order.append(self.sample)
        self.teb(); self.peb(); self.ldr(); self.params(); self.kuser(); self.tls()

    # ------------------------------------------------------------------------------------------------ modules
    @staticmethod
    def key(name):
        name = os.path.basename(name).lower()
        return name[:-4] if name.endswith(".dll") else name

    def add(self, path, base=None):
        """Maps a module, and knows its exports by address."""
        if base is None:
            base = self.next_base; self.next_base += DLL_STEP
        m = load_pe(path, base)
        self.ctx.setConcreteMemoryAreaValue(m.base, m.image)
        m.ldr = LDR + 0x1000 + len(self.order) * 0x200
        self.modules[self.key(m.name)] = m; self.order.append(m)
        if self.ready: self.enlist(m)
        for name, rva in m.exports.items(): self.api_at.setdefault(m.base + rva, name)
        return m

    def find(self, name):
        return self.modules.get(self.key(name))

    def module_at(self, address):
        for m in self.order:
            if m.contains(address): return m
        return None

    def load(self, name):
        """The module of that name, mapped if it was not: an API set is the DLL which implements it. None when the
        system has no such DLL."""
        m = self.find(name)
        if m is not None:
            if m.image is not None and not self.ctx.isConcreteMemoryValueDefined(m.base, 1):
                self.ctx.setConcreteMemoryAreaValue(m.base, m.image)      # loaded on another path: this one has not seen it
            if self.ready and not self.listed(m): self.enlist(m)
            return m
        base = os.path.basename(name).lower()
        if base.startswith(("api-ms-", "ext-ms-")):
            key = base[:-4] if base.endswith(".dll") else base
            host = self.apiset.get(key[:key.rindex("-")])
            return self.load(host) if host else None
        if "." not in base: base += ".dll"
        path = os.path.join(self.system32, base)
        if not os.path.isfile(path) or len(self.order) >= 48: return None
        try:
            return self.add(path)
        except (OSError, ValueError, struct.error):
            return None

    def resolve(self, dll, name, depth=0):
        """The address of an export, forwarders followed; None when this process does not have it."""
        if depth > 6: return None
        m = self.load(dll)
        if m is None: return None
        if name in m.exports: return m.base + m.exports[name]
        if name in m.forwards:
            target, _, symbol = m.forwards[name].rpartition(".")
            return self.resolve(target, symbol, depth + 1)
        return None

    # ------------------------------------------------------------------------------------------------ memory
    def w(self, address, data): self.ctx.setConcreteMemoryAreaValue(address, bytes(data))
    def q(self, address, value): self.w(address, struct.pack("<Q", value & MASK64))
    def d(self, address, value): self.w(address, struct.pack("<I", value & 0xffffffff))
    def h(self, address, value): self.w(address, struct.pack("<H", value & 0xffff))

    def alloc(self, region, size):
        at = self.cursor[region]; self.cursor[region] = (at + size + 15) & ~15
        return at

    def wide(self, region, text):
        data = text.encode("utf-16-le") + b"\0\0"
        at = self.alloc(region, len(data)); self.w(at, data)
        return at, len(data) - 2

    def ustr(self, address, region, text):
        """A UNICODE_STRING at `address`."""
        at, size = self.wide(region, text)
        self.w(address, struct.pack("<HHIQ", size, size + 2, 0, at))

    def symbolic(self, address, size, alias):
        self.ctx.symbolizeMemory(self.t.MemoryAccess(address, size), alias)

    # ------------------------------------------------------------------------------------------------ blocks
    def teb(self):
        top = RSP + 0x10000
        for off, value in ((0x00, 0), (0x08, top), (0x10, top - STACK_SIZE), (0x18, 0), (0x20, 0x1e00), (0x28, 0), (0x30, TEB), (0x38, 0),
                           (0x40, PID), (0x48, TID), (0x50, 0), (0x58, TLS), (0x60, PEB), (0x1478, top - STACK_SIZE)):
            self.q(TEB + off, value)
        self.d(TEB + 0x68, 0)                                  # LastErrorValue
        self.w(TEB + 0x1480, bytes(64 * 8))                    # TlsSlots
        self.d(TEB + 0x108, 0x409)                             # CurrentLocale
        self.w(FLS, bytes(256 * 8))

    def peb(self):
        major, minor, build = self.version
        self.w(PEB, bytes(0x20))
        self.q(PEB + 0x08, MASK64)                             # Mutant
        self.q(PEB + 0x10, self.host.base)                     # ImageBaseAddress
        self.q(PEB + 0x18, LDR)
        self.q(PEB + 0x20, PARAMS)
        self.q(PEB + 0x28, 0)
        self.q(PEB + 0x30, HEAP_HANDLE)                        # ProcessHeap
        lock = self.alloc(LDR, 0x28); self.w(lock, bytes(0x28)); self.q(PEB + 0x38, lock)
        self.d(PEB + 0xb8, 8); self.d(PEB + 0xbc, 0)           # NumberOfProcessors, NtGlobalFlag
        self.d(PEB + 0x118, major); self.d(PEB + 0x11c, minor); self.h(PEB + 0x120, build); self.h(PEB + 0x122, 0)
        self.d(PEB + 0x124, 2); self.d(PEB + 0x128, 3); self.d(PEB + 0x12c, major); self.d(PEB + 0x130, minor)
        self.d(PEB + 0x2c0, 1)                                 # SessionId
        if self.schema:
            self.w(APISET, self.schema); self.q(PEB + 0x68, APISET)

    def entry(self, m):
        """The LDR_DATA_TABLE_ENTRY of a module, where it was given a place."""
        e = m.ldr
        self.w(e, bytes(0x120))
        self.q(e + 0x30, m.base); self.q(e + 0x38, m.entry); self.d(e + 0x40, m.size)
        full = os.path.join(self.system32, m.name) if m is not self.sample else "C:/Users/user/".replace("/", chr(92)) + m.name
        self.ustr(e + 0x48, LDR, full); self.ustr(e + 0x58, LDR, m.name)
        self.d(e + 0x68, 0x000ca2cc if m is not self.host else 0x000022cc); self.h(e + 0x6c, 0xffff)
        self.q(e + 0x70, e + 0x70); self.q(e + 0x78, e + 0x70)
        self.d(e + 0x80, m.timestamp); self.q(e + 0xf8, m.preferred)
        hashed = 0
        for ch in m.name.upper(): hashed = (hashed * 65599 + ord(ch)) & 0xffffffff
        self.d(e + 0x108, hashed)

    def link(self, head, node):
        """At the end of a list of the loader."""
        last = u64(self.ctx.getConcreteMemoryAreaValue(head + 8, 8), 0)
        self.q(node, head); self.q(node + 8, last); self.q(last, node); self.q(head + 8, node)

    def listed(self, m):
        """Is the module in the lists of the loader, in the state the context is in?"""
        return self.ctx.isConcreteMemoryValueDefined(m.ldr + 0x30, 8)

    def enlist(self, m):
        """A module loaded after the process was built: its entry, at the end of the three lists."""
        self.entry(m)
        for head, offset in ((LDR + 0x10, 0x00), (LDR + 0x20, 0x10), (LDR + 0x30, 0x20)): self.link(head, m.ldr + offset)

    def ldr(self):
        self.w(LDR, struct.pack("<IIQ", 0x58, 1, 0) + bytes(0x48))
        for head in (LDR + 0x10, LDR + 0x20, LDR + 0x30): self.q(head, head); self.q(head + 8, head)
        for m in self.order:
            self.entry(m)
            self.link(LDR + 0x10, m.ldr); self.link(LDR + 0x20, m.ldr + 0x10)
        first = [self.modules[k] for k in ("ntdll", "kernelbase", "kernel32") if k in self.modules]
        for m in first + [m for m in self.order if m not in first and m is not self.host]:
            self.link(LDR + 0x30, m.ldr + 0x20)
        self.ready = True

    def params(self):
        p = PARAMS
        self.w(p, bytes(0x410))
        self.d(p, 0x800); self.d(p + 4, 0x800); self.d(p + 8, 0x6001)
        self.q(p + 0x20, 0x50); self.q(p + 0x28, 0x54); self.q(p + 0x30, 0x58)
        self.ustr(p + 0x38, PARAMS, "C:\\Users\\user\\")
        self.ustr(p + 0x50, PARAMS, self.system32)
        self.ustr(p + 0x60, PARAMS, self.host.path)
        self.command = "rundll32.exe %s,run" % self.sample.name
        self.ustr(p + 0x70, PARAMS, self.command)
        root = self.root.replace(chr(92), "/"); home = "C:/Users/user"
        variables = ("ALLUSERSPROFILE=C:/ProgramData", "APPDATA=" + home + "/AppData/Roaming", "CommonProgramFiles=C:/Program Files/Common Files",
                     "CommonProgramFiles(x86)=C:/Program Files (x86)/Common Files", "CommonProgramW6432=C:/Program Files/Common Files",
                     "COMPUTERNAME=DESKTOP", "ComSpec=" + root + "/system32/cmd.exe", "DriverData=" + root + "/System32/Drivers/DriverData",
                     "HOMEDRIVE=C:", "HOMEPATH=/Users/user", "LOCALAPPDATA=" + home + "/AppData/Local", "LOGONSERVER=//DESKTOP",
                     "NUMBER_OF_PROCESSORS=8", "OS=Windows_NT", "Path=" + root + "/system32;" + root + ";" + root + "/System32/Wbem",
                     "PATHEXT=.COM;.EXE;.BAT;.CMD;.VBS;.VBE;.JS;.JSE;.WSF;.WSH;.MSC", "PROCESSOR_ARCHITECTURE=AMD64",
                     "PROCESSOR_IDENTIFIER=Intel64 Family 6 Model 58 Stepping 9, GenuineIntel", "PROCESSOR_LEVEL=6", "PROCESSOR_REVISION=3a09",
                     "ProgramData=C:/ProgramData", "ProgramFiles=C:/Program Files", "ProgramFiles(x86)=C:/Program Files (x86)",
                     "ProgramW6432=C:/Program Files", "PUBLIC=C:/Users/Public", "SESSIONNAME=Console", "SystemDrive=C:", "SystemRoot=" + root,
                     "TEMP=" + home + "/AppData/Local/Temp", "TMP=" + home + "/AppData/Local/Temp", "USERDOMAIN=DESKTOP",
                     "USERDOMAIN_ROAMINGPROFILE=DESKTOP", "USERNAME=user", "USERPROFILE=" + home, "windir=" + root)
        block = chr(0).join(v.replace("/", chr(92)) for v in sorted(variables, key=str.upper)) + chr(0)
        self.environment, size = self.wide(PARAMS, block)
        self.q(p + 0x80, self.environment); self.q(p + 0x3f0, size + 2)
        self.command_w = u64(self.ctx.getConcreteMemoryAreaValue(p + 0x78, 8), 0)
        data = self.command.encode("latin1") + b"\0"
        self.command_a = self.alloc(PARAMS, len(data)); self.w(self.command_a, data)

    def kuser(self):
        major, minor, build = self.version
        k = KUSER
        self.w(k, bytes(0x3d8))
        self.d(k + 0x004, 0x0fa00000)
        self.w(k + 0x008, struct.pack("<Iii", 0x61c46800, 8, 8))            # InterruptTime: an hour
        self.w(k + 0x014, struct.pack("<Iii", 0x4a5f8000, 0x01dc7b2d, 0x01dc7b2d))   # SystemTime
        self.h(k + 0x02c, 0x8664); self.h(k + 0x02e, 0x8664)
        self.w(k + 0x030, self.root.encode("utf-16-le"))
        self.d(k + 0x244, 0x200000)
        self.d(k + 0x260, build); self.d(k + 0x264, 1); self.w(k + 0x268, b"\1"); self.h(k + 0x26a, 9)
        self.d(k + 0x26c, major); self.d(k + 0x270, minor)
        features = bytearray(64)
        for f in (2, 3, 6, 8, 9, 10, 12, 13, 14, 17, 20, 21, 22, 23, 28, 32, 36, 37, 38): features[f] = 1      # no AVX: the emulator has none
        self.features = bytes(features)
        self.w(k + 0x274, features)
        self.d(k + 0x2d0, 0x110); self.w(k + 0x2d4, b"\0\x0a"); self.d(k + 0x2d8, 1)
        self.d(k + 0x2e8, 0x7fe00); self.w(k + 0x2f8, b"\xc3")
        self.q(k + 0x300, 10000000)
        self.w(k + 0x320, struct.pack("<Iii", 230400, 0, 0))                  # TickCount
        self.d(k + 0x330, 0x5a5a1234)
        self.d(k + 0x3c0, 8); self.h(k + 0x3c4, 1)

    def symbolize_inputs(self):
        """What differs from one machine or one run to the next becomes an input which starts as it is here: the clocks,
        what a debugger changes, which system this is. Both answers of a branch on them are explored."""
        k = KUSER
        self.symbolic(k + 0x008, 8, "kuser_InterruptTime")
        self.symbolic(k + 0x014, 8, "kuser_SystemTime")
        self.symbolic(k + 0x320, 8, "kuser_TickCount")
        self.symbolic(k + 0x2d4, 1, "kuser_KdDebuggerEnabled")
        self.symbolic(k + 0x260, 4, "kuser_NtBuildNumber")
        self.symbolic(k + 0x26c, 4, "kuser_NtMajorVersion"); self.symbolic(k + 0x270, 4, "kuser_NtMinorVersion")
        self.symbolic(PEB + 0x02, 1, "peb_BeingDebugged")
        self.symbolic(PEB + 0xbc, 4, "peb_NtGlobalFlag")
        self.symbolic(PEB + 0x118, 4, "peb_OSMajorVersion"); self.symbolic(PEB + 0x11c, 4, "peb_OSMinorVersion")
        self.symbolic(PEB + 0x120, 2, "peb_OSBuildNumber")

    def thread(self, k):
        """The blocks of one more thread: its TEB, its stack, its copy of the TLS template. Returns (TEB, stack pointer)."""
        teb = TEB + k * THREAD_STEP; top = RSP + 0x10000 - k * THREAD_STEP; tls = teb + (TLS - TEB)
        for off, value in ((0x00, 0), (0x08, top), (0x10, top - STACK_SIZE), (0x18, 0), (0x20, 0x1e00), (0x28, 0), (0x30, teb), (0x38, 0),
                           (0x40, PID), (0x48, TID + 4 * k), (0x50, 0), (0x58, tls), (0x60, PEB), (0x1478, top - STACK_SIZE)):
            self.q(teb + off, value)
        self.d(teb + 0x68, 0); self.w(teb + 0x1480, bytes(64 * 8)); self.d(teb + 0x108, 0x409)
        self.w(teb + (FLS - TEB), bytes(256 * 8))
        self.w(tls, bytes(0x100))
        if self.tls_block: self.w(tls + 0x1000, self.tls_block); self.q(tls, tls + 0x1000)
        return teb, top - 0x10000

    def tls(self):
        """The thread's copy of the image's TLS template, as the loader makes it for index 0."""
        self.w(TLS, bytes(0x100))
        self.tls_callbacks = 0; self.tls_block = b""
        t = self.sample.tls
        if not t: return
        start, end, index, callbacks, fill, _ = t
        block = TLS + 0x1000
        template = self.ctx.getConcreteMemoryAreaValue(start, end - start) if end > start else b""
        self.tls_block = bytes(template) + bytes(fill + 0x40)
        self.w(block, self.tls_block)
        self.q(TLS, block)
        self.tls_callbacks = callbacks
