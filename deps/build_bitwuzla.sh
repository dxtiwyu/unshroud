#!/bin/sh
# Builds the Bitwuzla submodule (deps/bitwuzla) into deps/bitwuzla-install: one DLL with GMP, MPFR and CaDiCaL linked
# in statically (it needs only Windows system DLLs), its headers, and lib/bitwuzla.def for the MSVC import library
# (build.bat makes bitwuzla.lib from it). Bitwuzla does not build with MSVC; its C API is plain C, so the MinGW DLL is
# used from the MSVC-built engine through that API only.
# Runs inside MSYS2 UCRT64 (build.bat starts it). Packages:
#   pacman -S --needed mingw-w64-ucrt-x86_64-{gcc,meson,ninja,pkgconf,gmp,mpfr}
set -e
cd "$(dirname "$0")"
[ -f bitwuzla/meson.build ] || { echo "deps/bitwuzla is empty: git submodule update --init --recursive"; exit 1; }
[ -n "$MINGW_PREFIX" ] || { echo "run this in an MSYS2 UCRT64 shell"; exit 1; }
[ -n "$UNSHROUD_GIT" ] && PATH="$PATH:$(cygpath -u "$UNSHROUD_GIT")"   # git of Windows (build.bat passes its folder)
command -v git >/dev/null || { echo "git is needed on PATH (Bitwuzla downloads SymFPU with it): pacman -S git, or Git for Windows"; exit 1; }
HERE=$(pwd -W); P=$(cygpath -m "$MINGW_PREFIX")
mkdir -p bitwuzla-build/pc
# static GMP / MPFR: pkg-config files that name the static archives
cat > bitwuzla-build/pc/gmp.pc <<PC
Name: gmp
Description: GMP (static)
Version: $(pkg-config --modversion gmp)
Cflags: -I$P/include -DGMP_STATICLIB
Libs: $P/lib/libgmp.a
PC
cat > bitwuzla-build/pc/mpfr.pc <<PC
Name: mpfr
Description: MPFR (static)
Version: $(pkg-config --modversion mpfr)
Requires: gmp
Cflags: -I$P/include
Libs: $P/lib/libmpfr.a
PC
if [ ! -f bitwuzla-build/b/build.ninja ]; then
  meson setup bitwuzla-build/b bitwuzla --prefix="$HERE/bitwuzla-install" \
    -Dbuildtype=release -Ddefault_library=shared -Dcadical:default_library=static -Dprefer_static=true \
    "-Dcpp_link_args=['-static','-Wl,--export-all-symbols','-Wl,--exclude-libs,ALL']" \
    -Dtesting=disabled -Dunit_testing=disabled -Dmimalloc=disabled -Dpython=false \
    -Dpkg_config_path="$HERE/bitwuzla-build/pc"
fi
meson compile -C bitwuzla-build/b ${BZ_JOBS:+-j $BZ_JOBS}
meson install -C bitwuzla-build/b --quiet
# the C API exports -> bitwuzla.def
DLL=$(ls bitwuzla-install/bin/libbitwuzla*.dll | head -1)
{ echo "LIBRARY $(basename "$DLL")"; echo "EXPORTS"
  objdump -p "$DLL" | awk '/\[Ordinal\/Name Pointer\] Table/{t=1; next} t && /^\s*\[/{print $NF} t && /^$/{if (n++) t=0}' | grep '^bitwuzla_' | sed 's/^/  /'
} > bitwuzla-install/lib/bitwuzla.def
echo "bitwuzla: $(grep -c '^  bitwuzla_' bitwuzla-install/lib/bitwuzla.def) exports, $DLL"
