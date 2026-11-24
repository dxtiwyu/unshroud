// MBA simplifier on expressions given in SMT-LIB (one assert (= e e) per expression is enough) or built-in tests.
#include "../src/util.hpp"
#include "../src/mba.hpp"
#include "../src/smtlib.hpp"
#include "../src/solver.hpp"
#include <chrono>
#include <cstdio>
#include <cstring>
using namespace unshroud;

int main(int argc, char** argv) {
  unshroud::limitMemory();
  Ctx X; Solver S(X); Mba M(X, &S);
  u32 x = X.var("x", 64, 1), y = X.var("y", 64, 2), z = X.var("z", 64, 3);
  struct T { const char* name; u32 e; };
  std::vector<T> ts = {
    {"(x^y)+2(x&y)", X.add(X.xor_(x, y), X.mul(X.and_(x, y), X.cst(2, 64)))},
    {"(x|y)-(x&y)", X.sub(X.or_(x, y), X.and_(x, y))},
    {"(x|y)+(x&y)", X.add(X.or_(x, y), X.and_(x, y))},
    {"x+~y+1", X.add(X.add(x, X.not_(y)), X.cst(1, 64))},
    {"(x&y)*(x|y)+(x&~y)*(~x&y)", X.add(X.mul(X.and_(x, y), X.or_(x, y)), X.mul(X.and_(x, X.not_(y)), X.and_(X.not_(x), y)))},
    {"((x^y)+2(x&y))^z ...", X.add(X.xor_(X.add(X.xor_(x, y), X.mul(X.and_(x, y), X.cst(2, 64))), z), X.mul(X.and_(X.add(X.xor_(x, y), X.mul(X.and_(x, y), X.cst(2, 64))), z), X.cst(2, 64)))},
    {"const (x|y)-(x&y)-(x^y)+0x1337", X.add(X.sub(X.sub(X.or_(x, y), X.and_(x, y)), X.xor_(x, y)), X.cst(0x1337, 64))},
    {"x*y+z hidden", X.add(X.add(X.mul(X.and_(x, y), X.or_(x, y)), X.mul(X.and_(x, X.not_(y)), X.and_(X.not_(x), y))), X.sub(X.add(X.xor_(z, y), X.mul(X.and_(z, y), X.cst(2, 64))), y))},
    {"(x|0x53)-(x&0x53)  [x^0x53]", X.sub(X.or_(x, X.cst(0x53, 64)), X.and_(x, X.cst(0x53, 64)))},
    {"(x^0xff)+2(x&0xff) [x+0xff]", X.add(X.xor_(x, X.cst(0xff, 64)), X.mul(X.and_(x, X.cst(0xff, 64)), X.cst(2, 64)))},
    {"~(~x|0x77)&... nand/nor", X.not_(X.or_(X.not_(X.and_(x, X.cst(0x77, 64))), X.not_(y)))},
    {"mba mul of (x+y),(y^z)", [&] { u32 a = X.add(x, y), b = X.xor_(y, z);
        return X.add(X.mul(X.and_(a, b), X.or_(a, b)), X.mul(X.and_(a, X.not_(b)), X.and_(X.not_(a), b))); }()},
    {"mba add of mba products", [&] { u32 a = X.mul(x, y), b = X.add(z, X.cst(7, 64));
        return X.add(X.xor_(a, b), X.mul(X.and_(a, b), X.cst(2, 64))); }()},
  };
  for (auto& t : ts) {
    auto t0 = std::chrono::steady_clock::now();
    u32 r = M.simplify(t.e);
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    printf("%-34s %4u -> %3u nodes  %8.4fs  %s\n", t.name, X.countNodes(t.e), X.countNodes(r), dt, X.str(r, 8).c_str());
  }
  printf("stats: linear %llu boolean %llu constant %llu synth %llu proved %llu tested %llu\n", (unsigned long long)M.st.linear, (unsigned long long)M.st.boolean,
         (unsigned long long)M.st.constant, (unsigned long long)M.st.synth, (unsigned long long)M.st.proved, (unsigned long long)M.st.tested);
  return 0;
}
