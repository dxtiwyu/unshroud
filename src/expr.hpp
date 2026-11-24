// unshroud - expression DAG: hash-consed nodes of at most 64 bits, simplified while they are built.
#pragma once
#include <cstdint>
#include <cstring>
#include <intrin.h>
#include <string>
#include <vector>
#include <unordered_map>

namespace unshroud {

using u8 = uint8_t; using u16 = uint16_t; using u32 = uint32_t; using u64 = uint64_t;
using i8 = int8_t; using i16 = int16_t; using i32 = int32_t; using i64 = int64_t;

enum Op : u8 {
  O_NONE = 0,
  O_CONST, O_VAR,
  O_ADD, O_MUL, O_UDIV, O_UREM, O_SDIV, O_SREM, O_MULHU, O_MULHS, O_NEG,
  O_AND, O_OR, O_XOR, O_NOT,
  O_SHL, O_LSHR, O_ASHR, O_ROL, O_ROR,
  O_EXTRACT,   // a; lo = low bit; w = width
  O_ZEXT,      // a; lo = width of a
  O_SEXT,      // a; lo = width of a
  O_CONCAT,    // a = high part, b = low part; lo = width of b
  O_ITE,       // a = condition (1 bit), b = then, c = else
  O_EQ, O_ULT, O_ULE, O_SLT, O_SLE,   // 1-bit results; lo = width of the operands
  O_POPCNT, O_CLZ, O_CTZ,             // lo = width of a
  O_COUNT
};

const char* opName(u8 op);

inline u64 maskOf(unsigned w) { return w >= 64 ? ~0ull : ((1ull << w) - 1); }
inline u64 signBit(unsigned w) { return 1ull << (w - 1); }
inline i64 sx(u64 v, unsigned w) { return w >= 64 ? (i64)v : (i64)(v << (64 - w)) >> (64 - w); }

struct Node {
  u8 op; u8 w; u8 lo; u8 flags;   // flags: F_SYM (depends on a variable)
  u32 a, b, c;
  u64 k;                           // constant value, or variable index
  u32 h;                           // hash
  u32 size;                        // number of distinct nodes below, saturating (a size estimate)
};
enum : u8 { F_SYM = 1, F_ITE = 2 };             // depends on a variable; has a selection (ite) below

// Deferred operations (lazy mode): while a trace runs, an operation is only recorded; the node is built (with the rules, the
// sharing) when something needs it - a branch condition, an address, an output. What nothing reads is never built.
enum : u32 { LAZY_BASE = 0x80000000u };          // ids from there on are records of the tape
enum : u8 { O_SUBL = O_COUNT };                  // a - b, recorded (there is no subtraction node)
struct TapeRec { u8 op, w, lo, pad; u32 a, b, c, real; u64 k; };

// The semantics of one operation on concrete operand values (single source of truth: folding, evaluation, solver).
u64 evalOp(u8 op, unsigned w, unsigned lo, u64 k, u64 va, u64 vb, u64 vc);

struct VarInfo { std::string name; u8 w; u64 seed; u64 place = 0; };   // place: a pointer value of its own (unknown memory), tried first when a model makes it non-zero

class Ctx {
public:
  Ctx();
  std::vector<Node> n;             // id 0 is "no expression"
  std::vector<VarInfo> vars;
  bool check = false;              // every simplification is checked on random values (UNSHROUD_CHECK)
  bool norules = false;            // constructors only fold constants (to measure what the rules do)
  u32 off = 0;                     // rule groups turned off (UNSHROUD_RULES_OFF): 1 magic division, 2 extract pushdown, 4 ranges, 8 linear rebuild, 16 equality peeling
  size_t maxNodes = 40000000;      // past that many nodes, overBudget is set: the engine stops (memory guard)
  bool overBudget = false;
  u32 plain(u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c, u64 k);
  u64 checks = 0;
  u64 lookups = 0;                 // nodes asked for (found or made): what symbolic work is counted by

  const Node& N(u32 id) const { return n[id]; }
  bool isC(u32 id) const { return id < LAZY_BASE ? n[id].op == O_CONST : tape[id - LAZY_BASE].op == O_CONST; }
  u64 cv(u32 id) const { return id < LAZY_BASE ? n[id].k : tape[id - LAZY_BASE].k; }
  unsigned W(u32 id) const { return id < LAZY_BASE ? n[id].w : tape[id - LAZY_BASE].w; }

  // ---- lazy mode
  bool lazyOn = false;             // the constructors record instead of building
  std::vector<TapeRec> tape;
  u64 deferred = 0, forcedCount = 0;
  static bool isLazy(u32 id) { return id >= LAZY_BASE; }
  u32 force(u32 id);               // the node of a recorded operation (built now, with what it is made of); a node: itself
  void lazyReset() { tape.clear(); }   // every recorded id is dead from now on
  u32 defer(u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c);
  u32 deferConst(u64 v, unsigned w);
  // the same operation on the same operands is the same record: a loop which computes something again finds it (built, if it was read)
  std::vector<u32> lazyMemo;       // direct-mapped: hash of the operation -> record (checked against the tape)
  std::vector<u32> forceStack;
  unsigned lazyDepth = 48;         // a recorded operation on top of that many unbuilt ones is built at once
  bool sym(u32 id) const { return n[id].flags & F_SYM; }
  bool hasIte(u32 id) const { return n[id].flags & F_ITE; }

  u32 cst(u64 v, unsigned w);
  u32 var(const std::string& name, unsigned w, u64 seed);
  u32 varNode(u32 index) const { return varIds[index]; }

  // constructors (they simplify)
  u32 add(u32 a, u32 b);
  u32 sub(u32 a, u32 b);
  u32 mul(u32 a, u32 b);
  u32 neg(u32 a);
  u32 udiv(u32 a, u32 b);
  u32 urem(u32 a, u32 b);
  u32 sdiv(u32 a, u32 b);
  u32 srem(u32 a, u32 b);
  u32 mulhu(u32 a, u32 b);
  u32 mulhs(u32 a, u32 b);
  u32 and_(u32 a, u32 b);
  u32 or_(u32 a, u32 b);
  u32 xor_(u32 a, u32 b);
  u32 not_(u32 a);
  u32 shl(u32 a, u32 b);
  u32 lshr(u32 a, u32 b);
  u32 ashr(u32 a, u32 b);
  u32 rol(u32 a, u32 b);
  u32 ror(u32 a, u32 b);
  u32 extract(u32 a, unsigned lo, unsigned w);
  u32 zext(u32 a, unsigned w);
  u32 sext(u32 a, unsigned w);
  u32 concat(u32 hi, u32 lo);
  u32 ite(u32 c, u32 t, u32 f);
  u32 eq(u32 a, u32 b);
  u32 ne(u32 a, u32 b) { return not_(eq(a, b)); }
  u32 ult(u32 a, u32 b);
  u32 ule(u32 a, u32 b);
  u32 slt(u32 a, u32 b);
  u32 sle(u32 a, u32 b);
  u32 popcnt(u32 a);
  u32 clz(u32 a);
  u32 ctz(u32 a);
  u32 resize(u32 a, unsigned w) { return W(a) == w ? a : W(a) > w ? extract(a, 0, w) : zext(a, w); }

  // generic: build op with the rules
  u32 make(u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c, u64 k);
  // raw node, no rules
  u32 raw(u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c, u64 k);

  // evaluation of a node under the variables' values (vals[i] for variable i); memo by generation
  u64 eval(u32 id, const u64* vals);
  u64 evalSeed(u32 id);            // under the seeds of the variables
  std::string str(u32 id, int maxDepth = 12) const;
  std::string smt(u32 id) const;   // SMT-LIB2 text (define-funs for shared nodes)
  // exact Python: a function `name(x, y, z, w)` returning the values of roots (helpers in unshroud/py/unshroudpy.py)
  // (variables other than x, y, z, w are parameters too, with defaults[index] as their default value)
  std::string py(const std::vector<u32>& roots, const std::string& name, const std::vector<u64>* defaults = nullptr) const;
  u32 countNodes(u32 id);          // distinct nodes below id
  // unsigned interval of the values a node can take (sound over-approximation)
  struct Range { u64 lo, hi; };
  Range range(u32 id, int depth = 0);
  void collectVars(u32 id, std::vector<u32>& out);   // variable indexes below id
  // bits which have the same value whatever the inputs (sound): zeros / ones are masks of the bits known to be 0 / 1
  struct Known { u64 zeros, ones; };
  Known known(u32 id);
  unsigned unknownBits(u32 id) { Known k = known(id); return (unsigned)__popcnt64(maskOf(W(id)) & ~(k.zeros | k.ones)); }

  // visit stamps for traversals
  std::vector<u32> stamp; u32 gen = 1;
  std::vector<u64> memo;
  void newGen() { if (++gen == 0) { std::fill(stamp.begin(), stamp.end(), 0); gen = 1; } if (stamp.size() < n.size()) { stamp.resize(n.size() + n.size() / 2 + 1024, 0); memo.resize(n.size() + n.size() / 2 + 1024, 0); } }

private:
  std::vector<u64> table; u32 tmask = 0; u32 tcount = 0;   // (hash << 32) | id, 0: empty
  // The last NURSERY nodes are not in the table yet: they are found by their hash in a small ring, and enter the table
  // when they leave it (the slot was prefetched when they were made). A node made of a recent one can only already exist
  // among the recent ones: a chain of new nodes (each made of the one before) never waits for the table.
  enum { NURSERY = 32 };
  u32 ringHash[NURSERY] = {}; u32 ringId[NURSERY] = {}; u32 ringPos = 0; u32 ringCount = 0;
  void tableInsert(u32 h, u32 id);
  u64 front[4096] = {};            // direct-mapped: (hash << 32) | id of nodes looked up lately (constants, terms used again)
  std::vector<u32> varIds;
  struct EMC { u64 key; u32 val; u32 pad; };
  std::vector<EMC> extractMemo;   // direct-mapped cache (key 0: empty)
  std::vector<Range> rmemo; std::vector<u8> rhave;
  std::vector<Known> kmemo; std::vector<u8> khave;
  u32 magicDiv(u32 a, u64 M, unsigned N, unsigned s);   // floor(a*M / 2^(N+s)) as udiv(a, d), or 0
  int extractDepth = 0;
  u32 eqConst(u32 a, u64 c);
  void grow();
  u32 lookupOrAdd(const Node& x);
  u32 bit0(u32 e, int& budget);
  u32 checked(u32 r, u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c, u64 k) { return check ? checkedSlow(r, op, w, lo, a, b, c, k) : r; }
  u32 checkedSlow(u32 r, u8 op, unsigned w, unsigned lo, u32 a, u32 b, u32 c, u64 k);
  // linear / xor / and-or normalization helpers
  u32 linear(u32 a, u64 ca, u32 b, u64 cb, unsigned w);
  u32 xorChain(u32 a, u32 b, unsigned w);
  u32 andOr(u8 op, u32 a, u32 b, unsigned w);
};

}  // namespace unshroud
