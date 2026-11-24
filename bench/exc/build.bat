@echo off
rem builds the exception test DLLs: clang-cl (__CxxFrameHandler3) and cl (__CxxFrameHandler4), static CRT
call "C:\Program Files\Microsoft Visual Studio\18\Enterprise\VC\Auxiliary\Build\vcvars64.bat" >nul || exit /b 1
cd /d %~dp0
"C:\Program Files\LLVM\bin\clang-cl.exe" /nologo /O1 /EHa /MT /LD /GS- exc_tests.cpp /Feexc_clang.dll /Foexc_clang.obj /link /NOIMPLIB /NOEXP /MAP:exc_clang.map || exit /b 1
cl /nologo /O1 /EHsc /MT /LD exc_tests.cpp /Feexc_msvc.dll /Foexc_msvc.obj /link /NOIMPLIB /NOEXP /MAP:exc_msvc.map || exit /b 1
