"""Writes build/build.ninja: Zydis + Zycore (static), the engine library, one executable per tools/*.cpp, the Python module."""
import glob, os, shutil, sys, sysconfig
ROOT = os.path.dirname(os.path.abspath(__file__)).replace(os.sep, "/")
# configuration through the environment:
#   UNSHROUD_CLANG_CL  clang-cl.exe (default: the one on PATH, else C:/Program Files/LLVM/bin/clang-cl.exe)
#   BITWUZLA_DIR   a Bitwuzla install (include/, lib/bitwuzla.lib, bin/*.dll); default deps/bitwuzla-install (build.bat builds it)
#   UNSHROUD_PYTHON    a Python install to build the unshroud.pyd module against (default: the Python running this script;
#                  UNSHROUD_PYTHON=none skips the module); UNSHROUD_PYLIB overrides its python3XY.lib
#   UNSHROUD_OPT       optimization flags (default /O2 ... -march=native)
CL = os.environ.get("UNSHROUD_CLANG_CL") or shutil.which("clang-cl") or "C:/Program Files/LLVM/bin/clang-cl.exe"
CL = CL.replace(os.sep, "/")
BZ = (os.environ.get("BITWUZLA_DIR") or ROOT + "/deps/bitwuzla-install").replace(os.sep, "/").rstrip("/")
if not BZ or not os.path.exists(BZ + "/lib/bitwuzla.lib"):
    sys.exit("gen_ninja: no Bitwuzla in %s (build.bat builds the submodule; or set BITWUZLA_DIR to an install)" % BZ)
inc = "/I%s/src /I%s/deps/zydis/include /I%s/deps/zydis/src /I%s/deps/zydis/dependencies/zycore/include /I%s/include" % (ROOT, ROOT, ROOT, ROOT, BZ)
defs = "/DZYDIS_STATIC_BUILD /DZYCORE_STATIC_BUILD /DNOMINMAX /D_CRT_SECURE_NO_WARNINGS"
opt = os.environ.get("UNSHROUD_OPT", "/O2 /Ob2 /Oi /GS- -march=native")
out = []
def rel(p):
    return os.path.relpath(p, ROOT + "/build").replace(os.sep, "/")
out.append('cl = "%s"' % CL)
out.append("cxxflags = /nologo %s /std:c++20 /EHsc /MD /Zi /W3 -Wno-unused-function -Wno-unused-variable -Wno-sign-compare %s %s" % (opt, inc, defs))
out.append("cflags = /nologo /O2 /MD /Zi -march=native -w %s %s" % (inc, defs))
out.append("rule cxx\n  command = $cl $cxxflags /showIncludes /c $in /Fo$out\n  deps = msvc\n  description = cxx $in")
out.append("rule cc\n  command = $cl $cflags /c $in /Fo$out\n  description = cc $in")
out.append("rule asm\n  command = ml64 /nologo /c /Fo$out $in\n  description = asm $in")
out.append("rule lib\n  command = lib /nologo /out:$out $in\n  description = lib $out")
out.append("rule link\n  command = link /nologo /DEBUG /OPT:REF /OPT:ICF $in $libs /out:$out\n  description = link $out")
out.append("rule dll\n  command = link /nologo /DLL /DEBUG /OPT:REF /OPT:ICF $in $libs $extra /out:$out\n  description = dll $out")
out.append("rule copy\n  command = cmd /c copy /y $$(echo $in) $out >nul\n  description = copy $out")
zsrc = sorted(glob.glob(ROOT + "/deps/zydis/src/*.c") + glob.glob(ROOT + "/deps/zydis/dependencies/zycore/src/*.c") + glob.glob(ROOT + "/deps/zydis/dependencies/zycore/src/API/*.c"))
zobj = []
for s in zsrc:
    s = s.replace(os.sep, "/")
    o = "obj/zydis/" + os.path.relpath(s, ROOT + "/deps/zydis").replace(os.sep, "_").replace("/", "_") + ".obj"
    out.append("build %s: cc %s" % (o, rel(s))); zobj.append(o)
out.append("build zydis.lib: lib " + " ".join(zobj))
esrc = sorted(glob.glob(ROOT + "/src/*.cpp"))
eobj = []
for s in esrc:
    s = s.replace(os.sep, "/")
    o = "obj/" + os.path.basename(s) + ".obj"
    out.append("build %s: cxx %s" % (o, rel(s))); eobj.append(o)
for s in sorted(glob.glob(ROOT + "/src/*.asm")):
    o = "obj/" + os.path.basename(s) + ".obj"
    out.append("build %s: asm %s" % (o, rel(s))); eobj.append(o)
out.append("build unshroud.lib: lib " + " ".join(eobj))
libs = "unshroud.lib zydis.lib %s/lib/bitwuzla.lib" % BZ.replace(":", "$:")
for s in sorted(glob.glob(ROOT + "/tools/*.cpp")):
    s = s.replace(os.sep, "/")
    name = os.path.splitext(os.path.basename(s))[0]
    out.append("build obj/tools_%s.obj: cxx %s" % (name, rel(s)))
    out.append("build %s.exe: link obj/tools_%s.obj | unshroud.lib zydis.lib\n  libs = %s" % (name, name, libs))
# the Python module: nanobind (static) + the bindings + the engine
PY = (os.environ.get("UNSHROUD_PYTHON") or sys.base_prefix).replace(os.sep, "/").rstrip("/")
PYLIB = os.environ.get("UNSHROUD_PYLIB") or "%s/libs/python%d%d.lib" % (PY, sys.version_info[0], sys.version_info[1])
PYLIB = PYLIB.replace(os.sep, "/")
WITH_PY = PY.lower() != "none" and os.path.exists(PYLIB) and os.path.exists(PY + "/include/Python.h")
if not WITH_PY: print("gen_ninja: no Python headers / import library found, unshroud.pyd is not built (see UNSHROUD_PYTHON / UNSHROUD_PYLIB)")
if WITH_PY:
    nbinc = "/I%s/deps/nanobind/include /I%s/deps/nanobind/ext/robin_map/include /I%s/include" % (ROOT, ROOT, PY)
    out.append("nbflags = /nologo /O2 /MD /std:c++17 /EHsc /bigobj -fno-strict-aliasing -w /DNDEBUG /DNB_COMPACT_ASSERTIONS %s %s %s" % (nbinc, inc, defs))
    out.append("rule nbcxx\n  command = $cl $nbflags /showIncludes /c $in /Fo$out\n  deps = msvc\n  description = cxx $in")
    out.append("build obj/nb_combined.obj: nbcxx " + rel(ROOT + "/deps/nanobind/src/nb_combined.cpp"))
    out.append("build obj/unshroud_py.obj: nbcxx " + rel(ROOT + "/bind/unshroud_py.cpp"))
    out.append("build unshroud.pyd: dll obj/unshroud_py.obj obj/nb_combined.obj | unshroud.lib zydis.lib\n  libs = unshroud.lib zydis.lib %s/lib/bitwuzla.lib %s" % (BZ.replace(":", "$:"), PYLIB.replace(":", "$:")) + "\n  extra = /IMPLIB:unshroud_pyd.lib")
os.makedirs(ROOT + "/build/obj/zydis", exist_ok=True)
with open(ROOT + "/build/build.ninja", "w") as f:
    f.write("\n".join(out) + "\n")
