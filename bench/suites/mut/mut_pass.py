"""mut_pass.py: VMProtect-style mutation passes over the x86 code of mut_emit.

Exactness. Every pass recomputes the liveness of its input (mut_x86.liveness: registers
and flags, exact over the control flow; slot_liveness: the junk stack slots) and keeps
the observable behaviour of the code:
  * a register is written only where it is dead (no path reads it before its next
    write), or inside a push / pop pair or a slot store / load pair that restores it;
  * flags are clobbered only where they are dead, or between pushfq and popfq; the
    substitute of an instruction whose flags are read later produces the same flags;
  * the junk stack slots ([rbp - 8k] below the program's spill slots) are used only
    while the frame is set up, and only where the slot is dead;
  * every inserted sequence leaves rsp as it found it on every path through it.
Mutation kinds (counted per function in Ctx.stats):
  subst.<rule>  equivalent substitution of one instruction (MBA forms, De Morgan forms,
                split immediates, push / pop forms of mov, push and pop as lea + mov, ...)
  unfold        constant unfolding: an immediate rebuilt in a register by a mov of another
                constant and 1..3 invertible steps (xor / add / sub / rol / ror / not / neg /
                bswap / lea / imul by an odd constant)
  junk.<kind>   dead computations, push / pop pairs, stack round trips through a junk slot,
                pushfq / popfq protected junk, a live value split in two registers and
                recombined
  opaque.skip   opaque predicate: an always-taken jcc over a dead block that writes live
                registers; opaque.ret: a never-taken jcc to a dead arm returning a constant.
                The jcc is tagged opq_t<k> (always taken) / opq_n<k> (never taken), k its
                record in Ctx.opaque; its inversion keeps the tags right. Dead blocks are
                tagged 'dead' and get no junk: junk (and so every opaque predicate) only
                goes in live code
  jcc           a jcc turned into the opposite jcc around a jmp (inside subst)
  shuffle       the code cut in chunks, the chunks reordered and chained by jmp
"""
from collections import Counter

from mut_x86 import (Ins, R, I, M, A, L, label, simm, MASK, BIT, USABLE, CALLEE_SAVED,
                     CC_INV, NONE, FULL, liveness, successors, mentioned, is_jcc, info)

NL = chr(10)


def s32(v):
    v &= 0xffffffff
    return v - (1 << 32) if v & 0x80000000 else v


def fits32(v):
    return -2**31 <= v < 2**31


def bswap64(v):
    return int.from_bytes((v & MASK).to_bytes(8, 'little'), 'big')


def rol64(v, n):
    v &= MASK
    n &= 63
    return ((v << n) | (v >> (64 - n))) & MASK


def ror64(v, n):
    return rol64(v, 64 - (n & 63))


def lit(v):
    v &= MASK
    return str(v) if v < 10 else hex(v)


class Ctx:
    """State of the mutation of one function: rng, junk slots (rbp displacements), the
    epilogue label, the saved callee-saved registers, dead tails, opaque records, stats."""

    def __init__(self, fname, rng, slots, epi, saved):
        self.fname = fname
        self.r = rng
        self.slots = list(slots)
        self.epi = epi
        self.saved = list(saved)
        self.n = 0
        self.opaque = []
        self.tail = []
        self.stats = Counter()

    def label(self, kind='m'):
        self.n += 1
        return f'.L{self.fname}_{kind}{self.n}'

    def k32(self):
        """A random imm32 (small or full width); -k fits imm32 as well."""
        r = self.r
        c = r.random()
        if c < 0.35:
            return r.randrange(1, 256)
        if c < 0.45:
            return -r.randrange(1, 256)
        return r.randrange(-2**31 + 1, 2**31)

    def k64(self):
        return self.r.getrandbits(64) if self.r.random() < 0.6 else self.k32() & MASK


def frame_flags(code):
    """Per instruction: is the frame (rbp, the slots below it) set up before it."""
    out, on = [], False
    for ins in code:
        out.append(on)
        if ins.tag == 'frame_set':
            on = True
        elif ins.tag == 'frame_unset':
            on = False
    return out


def _slot_ud(ins, idx):
    u = d = 0
    for k, o in enumerate(ins.ops):
        if o[0] == 'm' and o[1] == 'rbp' and o[2] in idx:
            b = 1 << idx[o[2]]
            if k == 0 and ins.m in ('mov', 'pop'):
                d |= b
            else:
                u |= b
    return u, d


def slot_liveness(code, slots):
    """Live junk slots (bit k = slots[k]) before each instruction."""
    n = len(code)
    if not slots:
        return [0] * n
    idx = {d: k for k, d in enumerate(slots)}
    succ = successors(code)
    ud = [_slot_ud(x, idx) for x in code]
    lin = [0] * n
    changed = True
    while changed:
        changed = False
        for i in range(n - 1, -1, -1):
            o = 0
            for s in succ[i]:
                o |= lin[s]
            u, d = ud[i]
            v = u | (o & ~d)
            if v != lin[i]:
                lin[i] = v
                changed = True
    return lin


class State:
    """Liveness of registers, flags and junk slots, and the frame flags, of one code."""

    def __init__(self, ctx, code):
        self.lin, self.lout, self.fin, self.fout = liveness(code)
        self.frame = frame_flags(code)
        self.slive = slot_liveness(code, ctx.slots)


def is_opq(ins):
    """An opaque predicate's jcc: tag opq_t<k> (always taken) or opq_n<k> (never
    taken), k its index in Ctx.opaque."""
    return type(ins.tag) is str and ins.tag.startswith('opq_')


def free_of(mask):
    """Usable registers (no rsp / rbp) whose bit is not in mask, in GPR order."""
    return [g for g in USABLE if not mask & BIT[g]]


STEPS_FREE = ('not', 'bswap', 'lea')
STEPS_ALL = STEPS_FREE + ('xor', 'add', 'sub', 'rol', 'ror', 'neg', 'imul', 'xor', 'add')


def const_seq(ctx, t, c, flags_ok, nmin=1, nmax=3):
    """Instructions leaving the 64-bit constant c in register t: a mov of another
    constant, then nmin..nmax invertible steps (flag-free ones unless flags_ok)."""
    r = ctx.r
    steps = [r.choice(STEPS_ALL if flags_ok else STEPS_FREE) for _ in range(r.randint(nmin, nmax))]
    cur = c & MASK
    out = []
    for s in reversed(steps):
        if s == 'not':
            cur ^= MASK
            ins = Ins('not', R(t))
        elif s == 'bswap':
            cur = bswap64(cur)
            ins = Ins('bswap', R(t))
        elif s == 'neg':
            cur = -cur & MASK
            ins = Ins('neg', R(t))
        elif s == 'lea':
            k = ctx.k32()
            cur = (cur - k) & MASK
            ins = Ins('lea', R(t), A(t, None, 1, k))
        elif s == 'xor':
            k = ctx.k32()
            cur ^= k & MASK
            ins = Ins('xor', R(t), I(k))
        elif s == 'add':
            k = ctx.k32()
            cur = (cur - k) & MASK
            ins = Ins('add', R(t), I(k))
        elif s == 'sub':
            k = ctx.k32()
            cur = (cur + k) & MASK
            ins = Ins('sub', R(t), I(k))
        elif s == 'rol':
            k = r.randrange(1, 64)
            cur = ror64(cur, k)
            ins = Ins('rol', R(t), I(k))
        elif s == 'ror':
            k = r.randrange(1, 64)
            cur = rol64(cur, k)
            ins = Ins('ror', R(t), I(k))
        else:
            k = r.randrange(-2**31, 2**31) | 1
            cur = cur * pow(k & MASK, -1, 1 << 64) & MASK
            ins = Ins('imul', R(t), R(t), I(k))
        out.append(ins)
    out.reverse()
    return [Ins('mov', R(t), I(simm(cur)))] + out


# ---------------------------------------------------------------- substitutions
def _touches_sp(ins):
    for o in ins.ops:
        if o[0] in ('r', 'r32', 'r8', 'm') and o[1] == 'rsp':
            return True
        if o[0] == 'a' and 'rsp' in (o[1], o[2]):
            return True
    return False


def _valid(cls, ofw, fin, fout):
    """May a candidate of class cls replace an instruction with flag write ofw, given
    the flag liveness before (fin) and after (fout) it."""
    if cls == 'exact':
        return True
    if cls == 'free':
        return ofw == NONE or not fout
    return not fin and not fout


def subst_cands(ctx, ins, temps, pf):
    """Candidate replacements of ins: [(name, cls, thunk)]. cls 'exact': the same final
    flags (and no flag written at all when ins writes none, unless pf); 'free': writes no
    flag; 'clob': other flags. temps: registers free across ins (shuffled); pf: flags are
    dead before ins."""
    m, ops = ins.m, ins.ops
    C = []
    if is_jcc(m):
        def jinv():
            n = ctx.label('n')
            j, jm = Ins('j' + CC_INV[m[1:]], L(n)), Ins('jmp', ops[0])
            if is_opq(ins):
                # an opaque jcc: the inverse one goes the other way for sure, and the
                # jmp to the dead arm of a never-taken one never runs
                j.tag = ('opq_n' if ins.tag.startswith('opq_t') else 'opq_t') + ins.tag[5:]
                if ins.tag.startswith('opq_n'):
                    jm.tag = 'dead'
            return [j, jm, label(n)]
        C.append(('jcc', 'exact', jinv))
    elif m == 'push' and ops[0][0] == 'r':
        C.append(('push', 'exact', lambda: [Ins('lea', R('rsp'), A('rsp', None, 1, -8)),
                                            Ins('mov', M('rsp'), ops[0])]))
    elif m == 'pop' and ops[0][0] == 'r':
        C.append(('pop', 'exact', lambda: [Ins('mov', ops[0], M('rsp')),
                                           Ins('lea', R('rsp'), A('rsp', None, 1, 8))]))
    elif ops and ops[0][0] in ('r', 'm') and not _touches_sp(ins):
        t = temps[0] if temps else None
        if m in ('mov', 'lea'):
            _cands_mov(ctx, ins, t, pf, C)
        elif m in ('cmp', 'test'):
            _cands_cmp(ctx, ins, t, pf, C)
        elif ops[0][0] == 'r':
            _cands_alu(ctx, ins, t, pf, C)
    return C


def _cands_mov(ctx, ins, t, pf, C):
    r = ctx.r
    m, (D, S) = ins.m, ins.ops
    d = D[1] if D[0] == 'r' else None
    s = S[1] if S[0] == 'r' else None
    if m == 'lea':
        base, idx, sc, disp = S[1:]
        k1 = ctx.k32()
        if base and (idx is None or idx != d) and fits32(disp - k1):
            C.append(('lea_split', 'exact', lambda: [Ins('lea', D, A(base, None, 1, k1)),
                                                     Ins('lea', D, A(d, idx, sc, disp - k1))]))
        if base and idx and sc == 1 and disp == 0 and base != idx:
            if d == base:
                C.append(('lea_add', 'clob', lambda: [Ins('add', D, R(idx))]))
            elif d == idx:
                C.append(('lea_add', 'clob', lambda: [Ins('add', D, R(base))]))
            else:
                C.append(('lea_add', 'clob', lambda: [Ins('mov', D, R(base)), Ins('add', D, R(idx))]))
        return
    if D[0] == 'r' and S[0] == 'i':
        v = S[1] & MASK
        C.append(('unfold', 'exact', lambda: const_seq(ctx, d, v, pf)))
        if fits32(simm(v)):
            C.append(('push_imm', 'exact', lambda: [Ins('push', I(simm(v))), Ins('pop', D)]))
        if v == 0:
            C.append(('zero', 'clob', lambda: [Ins(r.choice(('xor', 'sub')), D, D)]))
        if v == MASK:
            C.append(('ones', 'clob', lambda: [Ins('or', D, I(-1))]))
    elif D[0] == 'r' and S[0] == 'r' and d != s:
        k = ctx.k32()
        C.append(('lea_mov', 'exact', lambda: [Ins('lea', D, A(s))]))
        C.append(('push_pop', 'exact', lambda: [Ins('push', S), Ins('pop', D)]))
        C.append(('lea_pair', 'exact', lambda: [Ins('lea', D, A(s, None, 1, k)),
                                                Ins('lea', D, A(d, None, 1, -k))]))
        C.append(('xor_or', 'clob', lambda: [Ins('xor', D, D), Ins(r.choice(('or', 'add', 'xor')), D, S)]))
    elif (D[0] == 'r' and S[0] == 'm') or (D[0] == 'm' and S[0] in ('r', 'i')):
        C.append(('push_pop', 'exact', lambda: [Ins('push', S), Ins('pop', D)]))
        if D[0] == 'm' and S[0] == 'i' and t:
            C.append(('unfold', 'exact', lambda: const_seq(ctx, t, S[1], pf) + [Ins('mov', D, R(t))]))


def _cands_cmp(ctx, ins, t, pf, C):
    """cmp / test: the same flags from a sub / and on a copy (a free register, or the
    register itself between push and pop), or the immediate unfolded in a register."""
    m, (X, Y) = ins.m, ins.ops
    op = 'sub' if m == 'cmp' else 'and'
    if t:
        C.append(('mov_' + op, 'exact', lambda: [Ins('mov', R(t), X), Ins(op, R(t), Y)]))
        if Y[0] == 'i':
            C.append(('unfold', 'exact', lambda: const_seq(ctx, t, Y[1], pf) + [Ins(m, X, R(t))]))
    if X[0] == 'r':
        C.append(('push_' + op, 'exact', lambda: [Ins('push', X), Ins(op, X, Y), Ins('pop', X)]))


def _cands_alu(ctx, ins, t, pf, C):
    m, ops = ins.m, ins.ops
    D = ops[0]
    S = ops[1] if len(ops) > 1 else None
    if m in ('add', 'sub', 'xor', 'and', 'or'):
        if S[0] == 'm':
            if t:
                C.append(('load', 'exact', lambda: [Ins('mov', R(t), S), Ins(m, D, R(t))]))
        elif S[0] == 'i':
            if t:
                C.append(('unfold', 'exact', lambda: const_seq(ctx, t, S[1], pf) + [Ins(m, D, R(t))]))
            _alu_imm(ctx, m, D, S[1], C)
        elif S[0] == 'r':
            _alu_reg(m, D, S, t, C)
    else:
        _alu_other(ctx, ins, t, pf, C)


def _alu_imm(ctx, m, D, k, C):
    d = D[1]
    if m in ('add', 'sub'):
        sg = 1 if m == 'add' else -1
        other = 'sub' if m == 'add' else 'add'
        if fits32(-k):
            C.append(('neg_imm', 'clob', lambda: [Ins(other, D, I(-k))]))
            C.append(('lea', 'free', lambda: [Ins('lea', D, A(d, None, 1, sg * k))]))
        k1 = ctx.k32()
        if fits32(k - k1):
            C.append(('split', 'clob', lambda: [Ins(m, D, I(k1)), Ins(m, D, I(k - k1))]))
        C.append(('not_' + other, 'clob', lambda: [Ins('not', D), Ins(other, D, I(k)), Ins('not', D)]))
        if sg * k == 1:
            C.append(('inc', 'clob', lambda: [Ins('inc', D)]))
            C.append(('negnot', 'clob', lambda: [Ins('not', D), Ins('neg', D)]))
        if sg * k == -1:
            C.append(('dec', 'clob', lambda: [Ins('dec', D)]))
            C.append(('notneg', 'clob', lambda: [Ins('neg', D), Ins('not', D)]))
    elif m == 'xor':
        k1 = ctx.k32()
        C.append(('not_xor', 'exact', lambda: [Ins('not', D), Ins('xor', D, I(~k))]))
        C.append(('split', 'exact', lambda: [Ins('xor', D, I(k1)), Ins('xor', D, I(k ^ k1))]))
    else:
        p = s32(ctx.r.getrandbits(32))
        inv = 'or' if m == 'and' else 'and'
        k1, k2 = (k | p, k | ~p) if m == 'and' else (k & p, k & ~p)
        C.append(('demorgan', 'clob', lambda: [Ins('not', D), Ins(inv, D, I(~k)), Ins('not', D)]))
        C.append(('split', 'exact', lambda: [Ins(m, D, I(k1)), Ins(m, D, I(k2))]))


def _alu_reg(m, D, S, t, C):
    d, s = D[1], S[1]
    T = R(t) if t else None
    add = C.append
    if s == d:
        if m == 'add':
            add(('shl1', 'clob', lambda: [Ins('shl', D, I(1))]))
            add(('lea2', 'free', lambda: [Ins('lea', D, A(None, d, 2))]))
            add(('imul2', 'clob', lambda: [Ins('imul', D, D, I(2))]))
        elif m in ('sub', 'xor'):
            add(('zero', 'exact', lambda: [Ins('xor' if m == 'sub' else 'sub', D, D)]))
            add(('and0', 'exact', lambda: [Ins('and', D, I(0))]))
            add(('mov0', 'free', lambda: [Ins('mov', D, I(0))]))
        return
    if m == 'add':
        add(('lea', 'free', lambda: [Ins('lea', D, A(d, s))]))
        add(('not_sub', 'clob', lambda: [Ins('not', D), Ins('sub', D, S), Ins('not', D)]))
        if t:
            add(('mba_or_and', 'clob', lambda: [Ins('mov', T, D), Ins('and', T, S), Ins('or', D, S),
                                                Ins('add', D, T)]))
            add(('mba_xor_and', 'clob', lambda: [Ins('mov', T, D), Ins('and', T, S), Ins('xor', D, S),
                                                 Ins('lea', D, A(d, t, 2))]))
            add(('neg_sub', 'clob', lambda: [Ins('mov', T, S), Ins('neg', T), Ins('sub', D, T)]))
    elif m == 'sub':
        add(('not_add', 'clob', lambda: [Ins('not', D), Ins('add', D, S), Ins('not', D)]))
        if t:
            add(('not_lea', 'free', lambda: [Ins('mov', T, S), Ins('not', T), Ins('lea', D, A(d, t, 1, 1))]))
            add(('neg_add', 'clob', lambda: [Ins('mov', T, S), Ins('neg', T), Ins('add', D, T)]))
            add(('mba_sub', 'clob', lambda: [Ins('mov', T, D), Ins('not', T), Ins('and', T, S),
                                             Ins('add', T, T), Ins('xor', D, S), Ins('sub', D, T)]))
    elif m == 'xor':
        add(('not_xor', 'clob', lambda: [Ins('not', D), Ins('xor', D, S), Ins('not', D)]))
        if t:
            add(('mba_xor', 'clob', lambda: [Ins('mov', T, D), Ins('and', T, S), Ins('or', D, S),
                                             Ins('sub', D, T)]))
            add(('andnot_or', 'clob', lambda: [Ins('mov', T, S), Ins('not', T), Ins('and', T, D),
                                               Ins('not', D), Ins('and', D, S), Ins('or', D, T)]))
    elif m == 'and' and t:
        add(('mba_and', 'clob', lambda: [Ins('mov', T, D), Ins('or', T, S), Ins('xor', D, S),
                                         Ins('sub', T, D), Ins('mov', D, T)]))
        add(('demorgan', 'clob', lambda: [Ins('mov', T, S), Ins('not', T), Ins('not', D),
                                          Ins('or', D, T), Ins('not', D)]))
    elif m == 'or' and t:
        add(('mba_or', 'clob', lambda: [Ins('mov', T, D), Ins('and', T, S), Ins('xor', D, S),
                                        Ins('add', D, T)]))
        add(('demorgan', 'clob', lambda: [Ins('mov', T, S), Ins('not', T), Ins('not', D),
                                          Ins('and', D, T), Ins('not', D)]))


def _alu_other(ctx, ins, t, pf, C):
    r = ctx.r
    m, ops = ins.m, ins.ops
    D = ops[0]
    d = D[1]
    add = C.append
    if m == 'not':
        add(('xor_m1', 'clob', lambda: [Ins('xor', D, I(-1))]))
        add(('neg_dec', 'clob', lambda: [Ins('neg', D), Ins('dec', D)]))
        add(('neg_lea', 'clob', lambda: [Ins('neg', D), Ins('lea', D, A(d, None, 1, -1))]))
    elif m == 'neg':
        add(('not_inc', 'clob', lambda: [Ins('not', D), Ins('inc', D)]))
        add(('not_lea', 'free', lambda: [Ins('not', D), Ins('lea', D, A(d, None, 1, 1))]))
        add(('imul_m1', 'clob', lambda: [Ins('imul', D, D, I(-1))]))
        add(('xor_add', 'clob', lambda: [Ins('xor', D, I(-1)), Ins('add', D, I(1))]))
        if t:
            add(('sub_from0', 'clob', lambda: [Ins('xor', R(t), R(t)), Ins('sub', R(t), D),
                                               Ins('mov', D, R(t))]))
    elif m == 'inc':
        add(('add1', 'clob', lambda: [Ins('add', D, I(1))]))
        add(('lea1', 'free', lambda: [Ins('lea', D, A(d, None, 1, 1))]))
    elif m == 'dec':
        add(('sub1', 'clob', lambda: [Ins('sub', D, I(1))]))
        add(('lea1', 'free', lambda: [Ins('lea', D, A(d, None, 1, -1))]))
    elif m in ('shl', 'shr', 'sar', 'rol', 'ror') and ops[1][0] == 'i':
        k = ops[1][1]
        if k >= 2:
            a = r.randrange(1, k)
            add(('split', 'clob', lambda: [Ins(m, D, I(a)), Ins(m, D, I(k - a))]))
        if m == 'shl' and k <= 3:
            add(('lea_scale', 'free', lambda: [Ins('lea', D, A(None, d, 1 << k))]))
        if m == 'shl' and k <= 30:
            add(('imul_pow2', 'clob', lambda: [Ins('imul', D, D, I(1 << k))]))
        if m in ('rol', 'ror'):
            add(('rot_inv', 'clob', lambda: [Ins('ror' if m == 'rol' else 'rol', D, I(64 - k))]))
    elif m == 'imul' and len(ops) == 3:
        S, K = ops[1], ops[2]
        pre = [] if S == D else [Ins('mov', D, S)]
        if pre:
            add(('mov_imul', 'exact', lambda: pre + [Ins('imul', D, D, K)]))
        if t:
            add(('unfold', 'exact', lambda: const_seq(ctx, t, K[1], pf) + pre + [Ins('imul', D, R(t))]))
    elif m == 'imul' and ops[1][0] == 'm' and t:
        add(('load', 'exact', lambda: [Ins('mov', R(t), ops[1]), Ins('imul', D, R(t))]))


def pass_subst(ctx, code, p):
    """Replace each instruction (not a label, not a tagged frame / ret / dead
    instruction; an opaque jcc only by its inversion) with probability p by one of its
    valid substitutes."""
    r = ctx.r
    st = State(ctx, code)
    out = []
    for i, ins in enumerate(code):
        if ins.m == 'label' or (ins.tag and not is_opq(ins)) or r.random() >= p:
            out.append(ins)
            continue
        _, _, fr, fw = info(ins)
        if fr and not is_jcc(ins.m):
            out.append(ins)
            continue
        temps = free_of(st.lin[i] | st.lout[i] | mentioned(ins))
        r.shuffle(temps)
        cands = [c for c in subst_cands(ctx, ins, temps, not st.fin[i])
                 if _valid(c[1], fw, st.fin[i], st.fout[i])]
        if not cands:
            out.append(ins)
            continue
        name, _, fn = r.choice(cands)
        out += fn()
        ctx.stats[name if name in ('unfold', 'jcc') else 'subst.' + name] += 1
    return out


# ---------------------------------------------------------------- junk
class Spot:
    """What junk inserted at one point may use: free (writable registers), live (live
    usable registers), flags_ok (flags dead), frame (rbp frame set up), slots (dead
    junk slots)."""

    def __init__(self, free, live, flags_ok, frame, slots):
        self.free, self.live, self.flags_ok, self.frame, self.slots = free, live, flags_ok, frame, slots

    def but(self, free=None, live=None, flags_ok=None, slots=None):
        return Spot(self.free if free is None else free, self.live if live is None else live,
                    self.flags_ok if flags_ok is None else flags_ok, self.frame,
                    self.slots if slots is None else slots)

    def plus(self, x):
        """Inside a pair that restores x: x writable, no longer live."""
        return self.but(free=[g for g in USABLE if g in self.free or g == x],
                        live=[g for g in self.live if g != x])


def spot(ctx, st, i):
    live = st.lin[i]
    frame = st.frame[i]
    slots = [s for k, s in enumerate(ctx.slots) if not (st.slive[i] >> k) & 1] if frame else []
    return Spot(free_of(live), [g for g in USABLE if live & BIT[g]], not st.fin[i], frame, slots)


DEAD_FREE = ('mov', 'movi', 'movi64', 'lea', 'lea', 'not', 'bswap', 'xchg')
DEAD_ALL = DEAD_FREE + ('alu', 'alu', 'alu', 'alui', 'alui', 'shift', 'imul', 'neg', 'incdec')
DEAD_FLAGS = ('alu', 'alui', 'shift', 'imul', 'neg', 'incdec')
ALU5 = ('add', 'sub', 'xor', 'and', 'or')
SHIFT5 = ('shl', 'shr', 'sar', 'rol', 'ror')


def dead_op(ctx, dsts, flags_ok, kinds=None):
    """One instruction writing a register of dsts (it may read any usable register);
    flag-free unless flags_ok."""
    r = ctx.r
    d = r.choice(dsts)
    D = R(d)
    s = r.choice(USABLE)
    kind = r.choice(kinds or (DEAD_ALL if flags_ok else DEAD_FREE))
    if kind == 'mov':
        return Ins('mov', D, R(s)) if s != d else Ins('not', D)
    if kind == 'movi':
        return Ins('mov', D, I(ctx.k32()))
    if kind == 'movi64':
        return Ins('mov', D, I(simm(r.getrandbits(64))))
    if kind == 'lea':
        c = r.random()
        if c < 0.4:
            return Ins('lea', D, A(s, None, 1, ctx.k32()))
        if c < 0.8:
            return Ins('lea', D, A(s, r.choice(USABLE), r.choice((1, 2, 4, 8)), r.choice((0, ctx.k32()))))
        return Ins('lea', D, A(None, s, r.choice((2, 4, 8)), ctx.k32()))
    if kind == 'not':
        return Ins('not', D)
    if kind == 'bswap':
        return Ins('bswap', D)
    if kind == 'xchg':
        others = [g for g in dsts if g != d]
        return Ins('xchg', D, R(r.choice(others))) if others else Ins('bswap', D)
    if kind == 'alu':
        return Ins(r.choice(ALU5), D, R(s))
    if kind == 'alui':
        return Ins(r.choice(ALU5), D, I(ctx.k32()))
    if kind == 'shift':
        return Ins(r.choice(SHIFT5), D, I(r.randrange(1, 64)))
    if kind == 'imul':
        return Ins('imul', D, R(s)) if r.random() < 0.5 else Ins('imul', D, R(s), I(ctx.k32()))
    if kind == 'neg':
        return Ins('neg', D)
    return Ins(r.choice(('inc', 'dec')), D)


def dead_block(ctx, n):
    """n instructions of a block that never runs: they write any register the function
    may change (volatile or saved), live ones included."""
    regs = [g for g in USABLE if g not in CALLEE_SAVED or g in ctx.saved]
    return dead([dead_op(ctx, regs, True) for _ in range(n)])


def dead(seq):
    """Tag the instructions of a dead block 'dead' (never substituted; the generator
    checks that the emulation never executes one)."""
    for ins in seq:
        if ins.m != 'label':
            ins.tag = 'dead'
    return seq


OPQ_KINDS = ('x*(x+1) even', 'x*(x+1) even', 'x*x mod 4 < 2', '7*y*y-1 != x*x',
             '(x|y)-(x&y) == x^y', '(x&y)+(x|y) == x+y', '2*x even', 'x^~x == -1', '(x|1) != 0')


def opaque_pred(ctx, t, u, v1, v2):
    """(kind, instructions, cc): after the instructions the condition cc always holds.
    They write t, u and the flags, and read v1, v2 (any values)."""
    r = ctx.r
    T, U, V, W = R(t), R(u), R(v1), R(v2)
    k = r.choice(OPQ_KINDS)
    if k == 'x*(x+1) even':
        seq = [Ins('lea', T, A(v1, None, 1, 1)), Ins('imul', T, V)]
        c = r.random()
        if c < 0.4:
            return k, seq + [Ins('test', T, I(1))], 'e'
        if c < 0.6:
            return k, seq + [Ins('and', T, I(1))], 'e'
        if c < 0.8:
            return k, seq + [Ins('bt', T, I(0))], 'ae'
        return k, seq + [Ins('shr', T, I(1))], 'ae'
    if k == 'x*x mod 4 < 2':
        seq = [Ins('mov', T, V), Ins('imul', T, T), Ins('and', T, I(3))]
        if r.random() < 0.5:
            return k, seq + [Ins('cmp', T, I(2))], 'b'
        return k, seq + [Ins('test', T, I(2))], 'e'
    if k == '7*y*y-1 != x*x':
        return k, [Ins('mov', T, V), Ins('imul', T, T), Ins('imul', T, T, I(7)), Ins('dec', T),
                   Ins('mov', U, W), Ins('imul', U, U), Ins('cmp', T, U)], 'ne'
    if k == '(x|y)-(x&y) == x^y':
        return k, [Ins('mov', T, V), Ins('or', T, W), Ins('mov', U, V), Ins('and', U, W),
                   Ins('sub', T, U), Ins('mov', U, V), Ins('xor', U, W), Ins('cmp', T, U)], 'e'
    if k == '(x&y)+(x|y) == x+y':
        return k, [Ins('mov', T, V), Ins('and', T, W), Ins('mov', U, V), Ins('or', U, W),
                   Ins('add', T, U), Ins('lea', U, A(v1, v2)), Ins('cmp', T, U)], 'e'
    if k == '2*x even':
        return k, [Ins('lea', T, A(v1, v1) if r.random() < 0.5 else A(None, v1, 2)),
                   Ins('test', T, I(1))], 'e'
    if k == 'x^~x == -1':
        return k, [Ins('mov', T, V), Ins('not', T), Ins('xor', T, V), Ins('inc', T)], 'e'
    return k, [Ins('mov', T, V), Ins('or', T, I(1))], 'ne'


def j_dead(ctx, sp, size, depth):
    ctx.stats['junk.dead'] += 1
    return [dead_op(ctx, sp.free, sp.flags_ok) for _ in range(ctx.r.randint(1, max(1, min(4, size))))]


def j_pushpop(ctx, sp, size, depth):
    """push / pop pairs: a mov through the stack, or a register saved, clobbered by
    junk, restored."""
    r = ctx.r
    ctx.stats['junk.pushpop'] += 1
    if sp.free and r.random() < 0.3:
        src = I(ctx.k32()) if r.random() < 0.4 else R(r.choice(USABLE))
        return [Ins('push', src), Ins('pop', R(r.choice(sp.free)))]
    x = r.choice(USABLE)
    inner = [dead_op(ctx, [x], sp.flags_ok)]
    if depth < 3 and size > 3:
        inner += junk(ctx, sp.plus(x), r.randint(1, size - 3), depth + 1)
    return [Ins('push', R(x))] + inner + [Ins('pop', R(x))]


def j_slot(ctx, sp, size, depth):
    """Stack round trips through a junk slot: a value copied to a free register, or a
    register stored, clobbered by junk, loaded back."""
    r = ctx.r
    ctx.stats['junk.slot'] += 1
    s = r.choice(sp.slots)
    S = M('rbp', s)
    x = r.choice(sp.live or USABLE)
    store = [Ins('mov', S, R(x))] if r.random() < 0.6 else [Ins('push', R(x)), Ins('pop', S)]
    if sp.free and r.random() < 0.3:
        t = R(r.choice(sp.free))
        return store + ([Ins('mov', t, S)] if r.random() < 0.6 else [Ins('push', S), Ins('pop', t)])
    inner = [dead_op(ctx, [x], sp.flags_ok)]
    if depth < 3 and size > 3:
        inner += junk(ctx, sp.plus(x).but(slots=[q for q in sp.slots if q != s]), r.randint(1, size - 3), depth + 1)
    load = [Ins('mov', R(x), S)] if r.random() < 0.6 else [Ins('push', S), Ins('pop', R(x))]
    return store + inner + load


def j_pushf(ctx, sp, size, depth):
    """pushfq / popfq around junk that clobbers the flags."""
    r = ctx.r
    ctx.stats['junk.pushf'] += 1
    if sp.free:
        inner = [dead_op(ctx, sp.free, True, DEAD_FLAGS) for _ in range(r.randint(1, 2))]
    else:
        x = r.choice(USABLE)
        inner = [Ins('push', R(x)), dead_op(ctx, [x], True, DEAD_FLAGS), Ins('pop', R(x))]
    if depth < 3 and size > 4:
        inner += junk(ctx, sp.but(flags_ok=True), r.randint(1, size - 4), depth + 1)
    return [Ins('pushfq')] + inner + [Ins('popfq')]


def j_opaque(ctx, sp, size, depth):
    """An opaque predicate on two free registers (reading live values when there are
    some): an always-taken jcc over a dead block (skip), or, with a frame, a never-taken
    jcc to a dead arm at the end of the function that returns a constant (ret)."""
    r = ctx.r
    t, u = r.sample(sp.free, 2)
    srcs = [g for g in sp.live if g not in (t, u)] or [g for g in USABLE if g not in (t, u)]
    kind, pred, cc = opaque_pred(ctx, t, u, r.choice(srcs), r.choice(srcs))
    if sp.frame and r.random() < 0.4:
        dl = ctx.label('dead')
        c = ctx.k64()
        ctx.tail += [label(dl)] + dead_block(ctx, r.randint(1, 4)) + dead(const_seq(ctx, 'rax', c, True)) + \
            dead([Ins('jmp', L(ctx.epi))])
        seq = pred + [Ins('j' + CC_INV[cc], L(dl), tag=f'opq_n{len(ctx.opaque)}')]
        ctx.opaque.append({'kind': kind, 'always': True, 'dead_out': lit(c)})
        ctx.stats['opaque.ret'] += 1
    else:
        ok = ctx.label('ok')
        jcc = Ins('j' + cc, L(ok), tag=f'opq_t{len(ctx.opaque)}')
        seq = pred + [jcc] + dead_block(ctx, r.randint(2, 5)) + [label(ok)]
        ctx.opaque.append({'kind': kind, 'always': True, 'dead_out': None})
        ctx.stats['opaque.skip'] += 1
    return seq if sp.flags_ok else [Ins('pushfq')] + seq + [Ins('popfq')]


def j_split(ctx, sp, size, depth):
    """A live register split in two parts (the second one in a free register) around
    junk, then recombined (bit masks, xor / add with a constant, 32-bit halves, or the
    flag-free lea form)."""
    r = ctx.r
    x = r.choice(sp.live)
    t = r.choice(sp.free)
    X, T = R(x), R(t)
    f = r.choice(('mask', 'xor', 'add', 'halves', 'lea') if sp.flags_ok else ('lea',))
    if f == 'mask':
        mk = 0
        while mk in (0, -1):
            mk = ctx.k32()
        a = [Ins('mov', T, X), Ins('and', T, I(mk)), Ins('and', X, I(~mk))]
        b = [Ins(r.choice(('or', 'add', 'xor')), X, T)]
    elif f == 'xor':
        a = const_seq(ctx, t, ctx.k64(), True, 0, 1) + [Ins('xor', X, T)]
        b = [Ins('xor', X, T)]
    elif f == 'add':
        a = const_seq(ctx, t, ctx.k64(), True, 0, 1) + [Ins('sub', X, T)]
        b = [Ins('add', X, T)]
    elif f == 'halves':
        a = [Ins('mov', T, X), Ins('shr', T, I(32)), Ins('mov', ('r32', x), ('r32', x))]
        b = [Ins('shl', T, I(32)), Ins('or', X, T)]
    else:
        a = const_seq(ctx, t, ctx.k64(), False, 0, 1) + [Ins('lea', X, A(x, t))]
        b = [Ins('not', T), Ins('lea', X, A(x, t, 1, 1))]
    inner = []
    if depth < 3:
        inner = junk(ctx, sp.but(free=[g for g in sp.free if g != t]), r.randint(1, max(1, size - 4)), depth + 1)
    ctx.stats['junk.split'] += 1
    return a + inner + b


def junk(ctx, sp, size, depth=0):
    """About size instructions of junk for spot sp (nested kinds may add more)."""
    r = ctx.r
    out = []
    while len(out) < size:
        kinds, ws = [], []
        for fn, w, ok in ((j_dead, 3.0, bool(sp.free)), (j_pushpop, 1.5, True),
                          (j_slot, 1.3, sp.frame and bool(sp.slots)),
                          (j_pushf, 0.4 if sp.flags_ok else 1.5, True),
                          (j_opaque, 1.0, depth < 2 and len(sp.free) >= 2),
                          (j_split, 0.9, depth < 3 and bool(sp.free) and bool(sp.live))):
            if ok:
                kinds.append(fn)
                ws.append(w)
        out += r.choices(kinds, ws)[0](ctx, sp, size - len(out), depth)
    return out


def pass_junk(ctx, code, density, size):
    """Insert junk before instructions (not labels, not dead code: dead-tagged
    instructions are exactly the unreachable ones) with probability density, 1..size
    instructions each (more when nested); the dead arms of opaque predicates go to the
    end of the function."""
    r = ctx.r
    st = State(ctx, code)
    out = []
    for i, ins in enumerate(code):
        live = ins.m != 'label' and ins.tag != 'dead' and (i == 0 or code[i - 1].m not in ('jmp', 'ret'))
        if live and r.random() < density:
            out += junk(ctx, spot(ctx, st, i), r.randint(1, size))
        out.append(ins)
    out += ctx.tail
    ctx.tail = []
    return out


def pass_shuffle(ctx, code, nchunks):
    """Cut the code in about nchunks chunks (never next to a dead instruction, so that
    every jmp added is live), keep the first one first, put the others in a random
    order and chain them by jmp where one fell through to the next."""
    r = ctx.r
    n = len(code)
    assert code[-1].m in ('jmp', 'ret')
    ok = [c for c in range(1, n) if code[c - 1].tag != 'dead' and code[c].tag != 'dead']
    cuts = sorted(r.sample(ok, min(max(1, nchunks - 1), len(ok))))
    chunks = [list(code[a:b]) for a, b in zip([0] + cuts, cuts + [n])]
    heads = []
    for ch in chunks:
        if ch[0].m != 'label':
            ch.insert(0, label(ctx.label('c')))
        heads.append(ch[0].ops[0][1])
    for k in range(len(chunks) - 1):
        if chunks[k][-1].m not in ('jmp', 'ret'):
            chunks[k].append(Ins('jmp', L(heads[k + 1])))
    rest = list(range(1, len(chunks)))
    r.shuffle(rest)
    ctx.stats['shuffle'] += len(chunks)
    return [x for k in [0] + rest for x in chunks[k]]


def n_insns(code):
    return sum(1 for x in code if x.m != 'label')


def grow(ctx, code, goal, size):
    """Junk passes until the code has at least goal instructions."""
    while n_insns(code) < goal:
        need = goal - n_insns(code)
        code = pass_junk(ctx, code, min(0.7, max(0.03, need / (len(code) * (size + 2.0)))), size)
    return code


# (pass, argument) rounds per strength; ('grow', ratio, size) grows to ratio x base
STRENGTH = {
    'light': ([('subst', 0.3), ('grow', 2.0, 2)], 0),
    'medium': ([('subst', 0.5), ('grow', 2.6, 3), ('subst', 0.3), ('grow', 4.7, 3)], 14),
    'heavy': ([('subst', 0.6), ('grow', 3.5, 3), ('subst', 0.4), ('grow', 8.0, 4),
               ('subst', 0.2), ('grow', 13.6, 4)], 9),
}


def mutate(ctx, code, base_n, strength):
    """The mutated code of one function (code: mut_emit's output with the junk slots
    and extra saved registers of ctx)."""
    rounds, chunk = STRENGTH[strength]
    for step in rounds:
        if step[0] == 'subst':
            code = pass_subst(ctx, code, step[1])
        else:
            code = grow(ctx, code, step[1] * base_n, step[2])
    if chunk:
        code = pass_shuffle(ctx, code, max(3, n_insns(code) // chunk))
    return code
