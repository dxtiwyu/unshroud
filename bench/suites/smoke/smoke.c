typedef unsigned long long u64;
typedef long long s64;
#define EXPORT __declspec(dllexport)
#define BAR(v) __asm__ volatile("" : "+r"(v))

/* MBA: x + y == (x | y) + (x & y); without the barriers clang folds it to one lea */
EXPORT u64 smoke_mba_add(u64 x, u64 y)
{
    u64 a = x | y; BAR(a);
    u64 b = x & y; BAR(b);
    return a + b;
}

/* a real branch on a signed comparison: each arm puts a barrier on its own result */
EXPORT u64 smoke_branch(u64 x, u64 y)
{
    u64 r;
    if ((s64)x < (s64)y) { r = y - x; BAR(r); }
    else                 { r = x ^ y; BAR(r); }
    return r;
}

/* opaque predicate: x * (x + 1) is always even; the dead arm returns 0xDEAD0001 */
EXPORT u64 smoke_opaque(u64 x, u64 y)
{
    u64 t = x * (x + 1); BAR(t);
    u64 r;
    if ((t & 1) == 0) { r = x + y;      BAR(r); }
    else              { r = 0xDEAD0001; BAR(r); }
    return r;
}

/* four arguments (rcx, rdx, r8, r9): two paths on z == w, an MBA in the second one */
EXPORT u64 smoke_args4(u64 x, u64 y, u64 z, u64 w)
{
    u64 r;
    if (z == w) { r = x - y; BAR(r); }
    else {
        u64 a = x ^ z; BAR(a);
        u64 b = y & w; BAR(b);
        u64 o = a | b; BAR(o);
        u64 n = a & b; BAR(n);
        r = o + n;     BAR(r);          /* (x ^ z) + (y & w) */
    }
    return r;
}

/* the language helpers against the CPU: rol by a variable count, sar, mulhu, udiv */
EXPORT u64 smoke_helpers(u64 x, u64 y)
{
    u64 k = y & 63;
    u64 r = (x << k) | (x >> ((64 - k) & 63));               /* rol(x, y & 63) */
    u64 s = (u64)((s64)y >> 7);                               /* sar(y, 7)      */
    u64 h = (u64)(((unsigned __int128)x * y) >> 64);          /* mulhu(x, y)    */
    u64 q = x / (y | 1);                                      /* udiv(x, y | 1) */
    return (r ^ s) + (h ^ q);
}
