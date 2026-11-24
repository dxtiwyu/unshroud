// unshroud - a reader for SMT-LIB 2 bit-vector queries (what Triton and Bitwuzla write), into the expression DAG.
// Terms wider than 64 bits are kept as (high, low) pairs for the forms Triton writes (128-bit products and divisions).
#pragma once
#include "expr.hpp"
#include <string>
#include <vector>

namespace unshroud {
bool parseSmt2(Ctx& X, const std::string& text, std::vector<u32>& asserts, std::string& err);
}
