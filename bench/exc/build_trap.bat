@echo off
rem builds the trap test DLL (clang-cl, static CRT)
call "C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvars64.bat" >nul || exit /b 1
cd /d %~dp0
"C:\Program Files\LLVM\bin\clang-cl.exe" /nologo /O1 /MT /LD /GS- trap_tests.cpp /Fetrap_clang.dll /Fotrap_clang.obj /link /NOIMPLIB /NOEXP /MAP:trap_clang.map || exit /b 1
