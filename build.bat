@echo off
rem Builds unshroud into build\ : the engine library, the tools (one exe per tools\*.cpp) and the Python module unshroud.pyd.
rem Needs: Visual Studio (C++ workload), LLVM clang-cl, ninja, Python 3, and the submodules
rem (git clone --recursive, or git submodule update --init --recursive).
rem The first build also builds the Bitwuzla submodule, with MSYS2 UCRT64 (MSYS2_ROOT, default C:\msys64);
rem set BITWUZLA_DIR to use an existing Bitwuzla install instead. Arguments are passed to ninja (targets, -j N).
setlocal
set "ROOT=%~dp0"
pushd "%ROOT%"
if not exist "deps\zydis\src\Decoder.c" ( echo submodules missing: git submodule update --init --recursive & exit /b 1 )
where cl >nul 2>nul
if errorlevel 1 (
  for /f "usebackq delims=" %%i in (`"%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe" -latest -products * -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath`) do set "VSDIR=%%i"
)
if defined VSDIR call "%VSDIR%\VC\Auxiliary\Build\vcvars64.bat" >nul || exit /b 1
if "%BITWUZLA_DIR%"=="" (
  set "BITWUZLA_DIR=%ROOT%deps\bitwuzla-install"
  if not exist "%ROOT%deps\bitwuzla-install\lib\bitwuzla.lib" call :bitwuzla || exit /b 1
)
python -I "%ROOT%gen_ninja.py" || exit /b 1
if not exist "%ROOT%build\libbitwuzla-0.dll" copy /y "%BITWUZLA_DIR%\bin\*.dll" "%ROOT%build\" >nul
ninja -C "%ROOT%build" %*
exit /b %errorlevel%

:bitwuzla
if "%MSYS2_ROOT%"=="" set "MSYS2_ROOT=C:\msys64"
if not exist "%MSYS2_ROOT%\usr\bin\bash.exe" (
  echo Bitwuzla is built with MSYS2 UCRT64: install MSYS2 or set MSYS2_ROOT, or set BITWUZLA_DIR to a Bitwuzla install
  exit /b 1
)
echo building the Bitwuzla submodule (once)
set MSYSTEM=UCRT64
for /f "delims=" %%g in ('where git 2^>nul') do if not defined UNSHROUD_GIT set "UNSHROUD_GIT=%%~dpg"
set CHERE_INVOKING=1
"%MSYS2_ROOT%\usr\bin\bash.exe" -lc "sh deps/build_bitwuzla.sh" || exit /b 1
lib /nologo /def:"%ROOT%deps\bitwuzla-install\lib\bitwuzla.def" /machine:x64 /out:"%ROOT%deps\bitwuzla-install\lib\bitwuzla.lib" || exit /b 1
exit /b 0
