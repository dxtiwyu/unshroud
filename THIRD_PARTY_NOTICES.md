# Third-party software

Unshroud itself is licensed under the Apache License 2.0 (`LICENSE`). It uses the following third-party code, included
as git submodules pinned to fixed commits; each keeps its own license (the full text is in the submodule):

| Component | Submodule | Commit | License | Copyright |
|---|---|---|---|---|
| [Zydis](https://github.com/zyantific/zydis) (x86 decoder / encoder) | `deps/zydis` | `a95bb710` | MIT | Florian Bernd, Joel Höner |
| [Zycore](https://github.com/zyantific/zycore-c) | `deps/zydis/dependencies/zycore` | `75a36c45` | MIT | Florian Bernd, Joel Höner |
| [nanobind](https://github.com/wjakob/nanobind) (Python bindings) | `deps/nanobind` | `68480a9e` (v3.1.0) | BSD 3-Clause | Wenzel Jakob |
| [robin-map](https://github.com/Tessil/robin-map) | `deps/nanobind/ext/robin_map` | `4ec1bf19` (v1.4.0) | MIT | Thibaut Goetghebuer-Planchon |
| [Bitwuzla](https://github.com/bitwuzla/bitwuzla) (SMT solver) | `deps/bitwuzla` | `4c2181f8` | MIT | the Bitwuzla authors |

The Bitwuzla DLL that `build.bat` builds links in, statically, CaDiCaL (MIT, fetched by Bitwuzla's build) and GMP
and MPFR from MSYS2 (LGPL-3.0 or later). Anyone who redistributes that DLL takes on the LGPL obligations for GMP and
MPFR; this repository contains only source.

Not included, used by the benchmark scripts only:

| Component | Use | License |
|---|---|---|
| [GAMBA data sets](https://github.com/DenuvoSoftwareSolutions/GAMBA) | `bench/gamba/fetch.py` downloads them | GPL-3.0 (Denuvo GmbH), not redistributed here |
| [Triton](https://github.com/JonathanSalwan/Triton) (`pip install triton-library`) | the comparison in `bench/gamba/tgamba.py` | Apache-2.0 |
