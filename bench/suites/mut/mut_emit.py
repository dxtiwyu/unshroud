"""mut_emit.py: register allocation and the unmutated x86-64 code of a program.

Every variable gets one home for its whole life (a register, or a stack slot
[rbp - 8k] when the linear scan runs out of registers). rax is the scratch register
and the result; rcx is reserved for shift counts when the program shifts by a
variable (x then moves out of rcx), otherwise x stays in rcx. y, z, w stay in rdx,
r8, r9 when possible. Callee-saved homes are pushed in the prologue; a stack slot
needs a frame (push rbp; mov rbp, rsp; sub rsp, n). The result goes to rax before the
label <fname>_epi, then the epilogue.
"""
import mut_prog as P
from mut_x86 import Ins, R, I, A, L, label, simm, fits32

POOL = ['rdx', 'r8', 'r9', 'r10', 'r11', 'rsi', 'rdi', 'rbx', 'r12', 'r13', 'r14', 'r15']
HINT = {'x': 'rcx', 'y': 'rdx', 'z': 'r8', 'w': 'r9'}
SAVE_ORDER = ['rbx', 'rsi', 'rdi', 'r12', 'r13', 'r14', 'r15']
CC_FALSE = {'eq': 'ne', 'ne': 'e', 'ult': 'ae', 'ule': 'a', 'ugt': 'be', 'uge': 'b',
            'slt': 'ge', 'sle': 'g', 'sgt': 'le', 'sge': 'l', 'tz': 'ne', 'tnz': 'e'}


def intervals(body, nargs):
    """start / end positions of every variable over the linearized program."""
    start, end = {}, {}
    pos = [0]

    def use(v, p):
        if type(v) is str:
            end[v] = max(end.get(v, 0), p)

    def define(v, p):
        if v not in start:
            start[v] = p
        end.setdefault(v, p)

    for a in P.ARGS[:nargs]:
        define(a, 0)

    def walk(stmts):
        for st in stmts:
            pos[0] += 1
            p = pos[0]
            if st[0] == 'op':
                use(st[3], p)
                use(st[4], p)
                define(st[1], p)
            elif st[0] == 'if':
                use(st[3], p)
                use(st[4], p)
                walk(st[5])
                walk(st[6])
            else:
                use(st[1], p)

    walk(body)
    return start, end


def allocate(body, nargs, pool):
    """({var: ('r', reg) or ('m', 'rbp', disp)}, number of stack slots): a linear
    scan; the result of an operation may take the register of an operand that dies
    there; when no register is free the interval that ends last is spilled."""
    start, end = intervals(body, nargs)
    first = {}
    for st in P.walk(body):
        if st[0] == 'op':
            first.setdefault(st[1], st)
    order = sorted(start, key=lambda v: (start[v], 0 if HINT.get(v) in pool else 1, v))
    home, active, free = {}, [], list(pool)
    nslots = 0
    for v in order:
        s = start[v]
        for u in list(active):
            if end[u] < s or (end[u] == s and s > 0):
                active.remove(u)
                free.append(home[u][1])
        reg = HINT.get(v) if HINT.get(v) in free else None
        st = first.get(v)
        if reg is None and st is not None and type(st[3]) is str:
            h = home.get(st[3])
            if h and h[0] == 'r' and h[1] in free:
                reg = h[1]
        if reg is None and free:
            reg = next(r for r in pool if r in free)
        if reg is None:
            victim = max(active, key=lambda u: end[u])
            nslots += 1
            if end[victim] > end[v]:
                reg = home[victim][1]
                home[victim] = ('m', 'rbp', -8 * nslots)
                active.remove(victim)
                free.append(reg)
            else:
                home[v] = ('m', 'rbp', -8 * nslots)
                continue
        free.remove(reg)
        home[v] = ('r', reg)
        active.append(v)
    return home, nslots


class Emitter:
    """Code of one program; see emit()."""

    def __init__(self, body, nargs, fname):
        self.body = body
        self.nargs = nargs
        self.fname = fname
        self.vshift = P.uses_vshift(body)
        self.pool = ([] if self.vshift else ['rcx']) + POOL
        self.home, self.nslots = allocate(body, nargs, self.pool)
        self.code = []

    def out(self, m, *ops, tag=None):
        self.code.append(Ins(m, *ops, tag=tag))

    def opnd(self, b):
        return self.home[b] if type(b) is str else I(simm(b))

    def via_rax(self, D, A_, fn):
        """D = f(A_) through rax when D is a stack slot: fn(reg) emits the operation."""
        self.out('mov', R('rax'), A_)
        fn(R('rax'))
        self.out('mov', D, R('rax'))

    def alu(self, kind, D, Aop, Bop):
        out = self.out
        if D[0] != 'r':
            self.via_rax(D, Aop, lambda t: out(kind, t, Bop))
        elif D == Aop:
            out(kind, D, Bop)
        elif D == Bop and kind != 'sub':
            out(kind, D, Aop)
        elif D == Bop:
            self.via_rax(D, Aop, lambda t: out('sub', t, Bop))
        elif kind == 'add' and Aop[0] == 'r' and Bop[0] == 'r':
            out('lea', D, A(Aop[1], Bop[1]))
        elif kind == 'add' and Aop[0] == 'r' and Bop[0] == 'i':
            out('lea', D, A(Aop[1], None, 1, Bop[1]))
        elif kind == 'sub' and Aop[0] == 'r' and Bop[0] == 'i' and fits32(-Bop[1]):
            out('lea', D, A(Aop[1], None, 1, -Bop[1]))
        else:
            out('mov', D, Aop)
            out(kind, D, Bop)

    def mul(self, D, Aop, Bop):
        out = self.out
        if Bop[0] == 'i':
            if D[0] == 'r':
                out('imul', D, Aop, Bop)
            else:
                out('imul', R('rax'), Aop, Bop)
                out('mov', D, R('rax'))
        elif D[0] != 'r':
            self.via_rax(D, Aop, lambda t: out('imul', t, Bop))
        elif D == Aop:
            out('imul', D, Bop)
        elif D == Bop:
            out('imul', D, Aop)
        else:
            out('mov', D, Aop)
            out('imul', D, Bop)

    def unary(self, m, D, Aop, *rest):
        """D = m(Aop, *rest) for a one-register instruction (not, neg, shifts)."""
        out = self.out
        if D[0] != 'r':
            self.via_rax(D, Aop, lambda t: out(m, t, *rest))
            return
        if D != Aop:
            out('mov', D, Aop)
        out(m, D, *rest)

    def op(self, st):
        _, dst, kind, a, b = st
        D = self.home[dst]
        if kind == 'const':
            if D[0] == 'r' or fits32(b):
                self.out('mov', D, I(simm(b)))
            else:
                self.out('mov', R('rax'), I(simm(b)))
                self.out('mov', D, R('rax'))
            return
        Aop = self.home[a]
        if kind == 'mul':
            self.mul(D, Aop, self.opnd(b))
        elif kind in P.ALU:
            self.alu(kind, D, Aop, self.opnd(b))
        elif kind in P.SHIFTS:
            self.unary(kind, D, Aop, I(b))
        elif kind in P.VSHIFTS:
            self.out('mov', R('rcx'), self.home[b])
            self.unary(kind[1:], D, Aop, ('r8', 'rcx'))
        else:
            self.unary(kind, D, Aop)

    def stmts(self, body):
        for st in body:
            if st[0] == 'op':
                self.op(st)
            elif st[0] == 'if':
                self.branch(st)
            else:
                self.out('mov', R('rax'), self.home[st[1]])

    def branch(self, st):
        _, iid, pred, a, b, th, el = st
        Aop = self.home[a]
        if pred in ('tz', 'tnz'):
            self.out('test', Aop, I(simm(b)))
        else:
            Bop = self.opnd(b)
            if Aop[0] == 'm' and Bop[0] == 'm':
                self.out('mov', R('rax'), Aop)
                Aop = R('rax')
            self.out('cmp', Aop, Bop)
        le = f'.L{self.fname}_else{iid}'
        lj = f'.L{self.fname}_join{iid}'
        self.out('j' + CC_FALSE[pred], L(le))
        self.stmts(th)
        self.out('jmp', L(lj))
        self.code.append(label(le))
        self.stmts(el)
        self.code.append(label(lj))

    def arg_moves(self):
        moves = []
        for a in P.ARGS[:self.nargs]:
            src = R(HINT[a])
            h = self.home.get(a)
            if h is not None and h != src:
                moves.append((h, src))
        for d, s in moves:
            if d[0] == 'm':
                self.out('mov', d, s)
        todo = [(d, s) for d, s in moves if d[0] == 'r']
        while todo:
            ready = [m for m in todo if all(m[0] != s for _, s in todo)]
            if not ready:
                raise RuntimeError(f'{self.fname}: cyclic argument moves {todo}')
            d, s = ready[0]
            self.out('mov', d, s)
            todo.remove((d, s))

    def build(self, extra_saved=(), njunk=0):
        """{code, epi, junk, saved, frame, nslots, home}: the whole function. extra_saved:
        callee-saved registers pushed although unused; njunk: frame slots kept for
        junk (rbp-relative displacements in 'junk'); either forces a frame when > 0."""
        used = {h[1] for h in self.home.values() if h[0] == 'r'}
        saved = [r for r in SAVE_ORDER if r in used]
        saved += [r for r in extra_saved if r not in saved]
        frame = self.nslots + njunk > 0
        self.code = []
        for r in saved:
            self.out('push', R(r))
        if frame:
            self.out('push', R('rbp'), tag='frame')
            self.out('mov', R('rbp'), R('rsp'), tag='frame')
            self.out('sub', R('rsp'), I(8 * (self.nslots + njunk)), tag='frame_set')
        self.arg_moves()
        self.stmts(self.body)
        epi = f'.L{self.fname}_epi'
        self.code.append(label(epi))
        if frame:
            self.out('mov', R('rsp'), R('rbp'), tag='frame_unset')
            self.out('pop', R('rbp'), tag='frame')
        for r in reversed(saved):
            self.out('pop', R(r))
        self.out('ret', tag='ret')
        junk = [-8 * (self.nslots + 1 + k) for k in range(njunk)]
        return {'code': self.code, 'epi': epi, 'junk': junk, 'saved': saved,
                'frame': frame, 'nslots': self.nslots, 'home': dict(self.home)}


def emit(body, nargs, fname, extra_saved=(), njunk=0):
    return Emitter(body, nargs, fname).build(extra_saved, njunk)


def n_insns(code):
    return sum(1 for i in code if i.m != 'label')
