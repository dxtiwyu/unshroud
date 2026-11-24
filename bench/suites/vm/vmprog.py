"""vmprog.py: the programs of the vm suite, their ground truth, compiler, assembler, emulator.

A program is a small AST over the arguments x, y, z, w and the locals a, b, c, d:
  expression  ('v', name) | ('k', const) | (op, l, r) for op in add sub mul and or xor shl
              shr (the shift count is taken mod 64, like the SHL / SHR handlers) |
              ('not', e) | ('neg', e)
  statement   ('set', local, e) | ('if', (cc, l, r), then, else) | ('loop', n, body) |
              ('ret', e); cc in eq ne ult ule ugt uge slt (signed lt); a loop body holds
              'set' statements only and may read the counter 'i' (n down to 1); every path
              ends with 'ret'.
paths() gives the ground truth (cond, out) of every path (loops unrolled). Compiler turns
the AST into virtual instructions in basic blocks: and / or / xor / not / sub / neg become
NOR / NAND / ADD compositions (VMProtect style), a value used twice goes through a
temporary virtual register, an if is CMP + PUSH_IMM both targets + JCC. assemble() lays the
blocks out, picks an opcode alias per instruction and encrypts; emulate() runs the
encrypted bytecode (the reference for vinsns, and a check of the compiler).
"""
from vmlib import M64, OPERAND, VSTK, COND_PY, sub_flags

ARGS = ('x', 'y', 'z', 'w')
LOCALS = ('a', 'b', 'c', 'd')
SYM = {'add': '+', 'sub': '-', 'mul': '*', 'and': '&', 'or': '|', 'xor': '^', 'shl': '<<', 'shr': '>>'}
CMP_SYM = {'eq': '==', 'ne': '!=', 'ult': '<', 'ule': '<=', 'ugt': '>', 'uge': '>=', 'slt': '<', 'sge': '>='}
NEG_CC = {'eq': 'ne', 'ne': 'eq', 'ult': 'uge', 'uge': 'ult', 'ule': 'ugt', 'ugt': 'ule', 'slt': 'sge', 'sge': 'slt'}
LIMIT_NODES = 2500              # largest truth expression accepted (nodes, roughly)
LIMIT_DEPTH = 110               # deepest parenthesis nesting accepted (Python's parser stops at 200)


class TooBig(Exception):
    """A truth expression grew past LIMIT_NODES / LIMIT_DEPTH (the generator draws again)."""


def ev(e, env):
    """Concrete value of expression e (env: name -> int)."""
    t = e[0]
    if t == 'v':
        return env[e[1]]
    if t == 'k':
        return e[1]
    if t == 'not':
        return ~ev(e[1], env) & M64
    if t == 'neg':
        return -ev(e[1], env) & M64
    a, b = ev(e[1], env), ev(e[2], env)
    if t == 'add':
        return (a + b) & M64
    if t == 'sub':
        return (a - b) & M64
    if t == 'mul':
        return (a * b) & M64
    if t == 'and':
        return a & b
    if t == 'or':
        return a | b
    if t == 'xor':
        return a ^ b
    if t == 'shl':
        return (a << (b & 63)) & M64
    if t == 'shr':
        return a >> (b & 63)
    raise ValueError(t)


def ev_cond(c, env):
    cc, l, r = c
    return bool(COND_PY[cc](*sub_flags(ev(l, env), ev(r, env))))


def run_ast(prog, args):
    """Concrete result of the program on args (x, y, z, w): the AST semantics."""
    env = dict(zip(ARGS, args))

    def seq(stmts):
        for s in stmts:
            k = s[0]
            if k == 'set':
                env[s[1]] = ev(s[2], env)
            elif k == 'ret':
                return ev(s[1], env)
            elif k == 'if':
                v = seq(s[2] if ev_cond(s[1], env) else s[3])
                if v is not None:
                    return v
            elif k == 'loop':
                for i in range(s[1], 0, -1):
                    env['i'] = i
                    seq(s[2])
        return None
    return seq(prog)


def lit(c):
    return str(c) if c < 10 else hex(c)


def sym(e, env):
    """(text, nodes, depth) of e in the bench expression language (env: name -> triple)."""
    t = e[0]
    if t == 'v':
        return env[e[1]]
    if t == 'k':
        return (lit(e[1]), 1, 0)
    if t in ('not', 'neg'):
        s, n, d = sym(e[1], env)
        return ('(' + ('~' if t == 'not' else '-') + s + ')', n + 1, d + 1)
    a = sym(e[1], env)
    if t in ('shl', 'shr'):
        if e[2][0] == 'k':
            b = (lit(e[2][1] & 63), 1, 0)
        else:
            s, n, d = sym(e[2], env)
            b = ('(' + s + ' & 63)', n + 2, d + 1)
    else:
        b = sym(e[2], env)
    n, d = a[1] + b[1] + 1, max(a[2], b[2]) + 1
    if n > LIMIT_NODES or d > LIMIT_DEPTH:
        raise TooBig()
    return ('(' + a[0] + ' ' + SYM[t] + ' ' + b[0] + ')', n, d)


def sym_cond(c, env, negate=False):
    cc, l, r = c
    if negate:
        cc = NEG_CC[cc]
    a, b = sym(l, env)[0], sym(r, env)[0]
    if cc in ('slt', 'sge'):
        a, b = 's64(' + a + ')', 's64(' + b + ')'
    return '(' + a + ' ' + CMP_SYM[cc] + ' ' + b + ')'


def paths(prog, nargs):
    """[(cond, out)] of every path of the program, in the order then-before-else."""
    out = []

    def walk(stmts, env, conds):
        if not stmts:
            raise ValueError('a path does not end with ret')
        s, rest = stmts[0], stmts[1:]
        k = s[0]
        if k == 'set':
            env = dict(env)
            env[s[1]] = sym(s[2], env)
            walk(rest, env, conds)
        elif k == 'ret':
            out.append((conds, sym(s[1], env)[0]))
        elif k == 'if':
            walk(list(s[2]) + rest, env, conds + [sym_cond(s[1], env)])
            walk(list(s[3]) + rest, env, conds + [sym_cond(s[1], env, True)])
        elif k == 'loop':
            env = dict(env)
            for i in range(s[1], 0, -1):
                env['i'] = (lit(i), 1, 0)
                for st in s[2]:
                    env[st[1]] = sym(st[2], env)
            del env['i']
            walk(rest, env, conds)
        else:
            raise ValueError(k)
    walk(list(prog), {a: (a, 1, 0) for a in ARGS[:nargs]}, [])
    return [(' and '.join(c) if c else 'True', o) for c, o in out]


def count_ops(e):
    if e[0] in ('v', 'k'):
        return 0
    return 1 + sum(count_ops(x) for x in e[1:])


def prog_ops(stmts):
    """Operations in the program's expressions (each counted once, loops not unrolled)."""
    n = 0
    for s in stmts:
        k = s[0]
        if k in ('set', 'ret'):
            n += count_ops(s[-1])
        elif k == 'if':
            n += count_ops(s[1][1]) + count_ops(s[1][2]) + prog_ops(s[2]) + prog_ops(s[3])
        elif k == 'loop':
            n += prog_ops(s[2])
    return n


class RegPressure(Exception):
    """No free virtual register for a temporary (the generator draws again)."""


def _names(stmts, acc):
    for s in stmts:
        if s[0] == 'set':
            acc.add(s[1])
        elif s[0] == 'if':
            _names(s[2], acc)
            _names(s[3], acc)
        elif s[0] == 'loop':
            acc.add('i')
            _names(s[2], acc)
    return acc


class Compiler:
    """AST -> {label: [(handler, operand)]}; label 0 is the entry block. Operands: a vreg
    number, ('cc', name) for JCC, an int or ('L', label) for PUSH_IMM."""

    def __init__(self, V, rng, nargs):
        self.V, self.r, self.nargs = V, rng, nargs
        self.blocks, self.cur, self.reg = {}, None, {}

    def label(self):
        lab = len(self.blocks)
        self.blocks[lab] = []
        return lab

    def start(self, lab):
        self.cur = self.blocks[lab]

    def emit(self, h, arg=None):
        self.cur.append((h, arg))

    def temp(self):
        if not self.free:
            raise RegPressure()
        return self.free.pop()

    def hold(self, e):
        """A handle on e that can be pushed several times: its vreg, its constant, or a temp."""
        if e[0] == 'v':
            return ('r', self.reg[e[1]], False)
        if e[0] == 'k':
            return ('k', e[1], False)
        self.cx(e)
        t = self.temp()
        self.emit('POP_VREG', t)
        return ('r', t, True)

    def push(self, h):
        self.emit('PUSH_VREG' if h[0] == 'r' else 'PUSH_IMM', h[1])

    def release(self, h):
        if h[2]:
            self.free.append(h[1])

    def nots(self, h):
        """push ~h: NOR(h, h) or NAND(h, h)."""
        self.push(h)
        self.push(h)
        self.emit(self.r.choice(('NOR', 'NAND')))

    def not_e(self, e):
        h = self.hold(e)
        self.nots(h)
        self.release(h)

    def not_top(self):
        t = self.temp()
        self.emit('POP_VREG', t)
        h = ('r', t, True)
        self.nots(h)
        self.release(h)

    def cx(self, e):
        """Code leaving the value of e on the virtual stack."""
        t, r = e[0], self.r
        if t == 'v':
            return self.emit('PUSH_VREG', self.reg[e[1]])
        if t == 'k':
            return self.emit('PUSH_IMM', e[1])
        if t == 'not':
            return self.not_e(e[1])
        if t == 'neg':                                  # -a = ~a + 1
            self.not_e(e[1])
            self.emit('PUSH_IMM', 1)
            return self.emit('ADD')
        a, b = e[1], e[2]
        if t in ('add', 'mul', 'shl', 'shr'):
            self.cx(a)
            self.cx(b)
            return self.emit(t.upper())
        if t == 'sub':
            if b[0] == 'k':                             # a + (-k)
                self.cx(a)
                self.emit('PUSH_IMM', -b[1] & M64)
                return self.emit('ADD')
            if r.random() < 0.5:                        # a + ~b + 1
                self.cx(a)
                self.not_e(b)
                self.emit('ADD')
                self.emit('PUSH_IMM', 1)
                return self.emit('ADD')
            self.not_e(a)                               # ~(~a + b)
            self.cx(b)
            self.emit('ADD')
            return self.not_top()
        if t == 'and':
            if r.random() < 0.5:                        # NOR(~a, ~b)
                self.not_e(a)
                self.not_e(b)
                return self.emit('NOR')
            self.cx(a)                                  # ~NAND(a, b)
            self.cx(b)
            self.emit('NAND')
            return self.not_top()
        if t == 'or':
            if r.random() < 0.5:                        # ~NOR(a, b)
                self.cx(a)
                self.cx(b)
                self.emit('NOR')
                return self.not_top()
            self.not_e(a)                               # NAND(~a, ~b)
            self.not_e(b)
            return self.emit('NAND')
        if t == 'xor':
            ha = self.hold(a)
            hb = self.hold(b)
            if r.random() < 0.5:                        # NOR(NOR(a, b), NOR(~a, ~b))
                self.push(ha)
                self.push(hb)
                self.emit('NOR')
                self.nots(ha)
                self.nots(hb)
                self.emit('NOR')
                self.emit('NOR')
            else:                                       # NAND(NAND(a, n), NAND(b, n)), n = NAND(a, b)
                self.push(ha)
                self.push(hb)
                self.emit('NAND')
                hn = ('r', self.temp(), True)
                self.emit('POP_VREG', hn[1])
                self.push(ha)
                self.push(hn)
                self.emit('NAND')
                self.push(hb)
                self.push(hn)
                self.emit('NAND')
                self.emit('NAND')
                self.release(hn)
            self.release(hb)
            return self.release(ha)
        raise ValueError(t)

    def cs(self, s):
        """Compile one statement; True when it ends the block (ret, or an if whose arms both return)."""
        k = s[0]
        if k == 'set':
            self.cx(s[2])
            self.emit('POP_VREG', self.reg[s[1]])
            return False
        if k == 'ret':
            e = s[1]
            if e[0] == 'v':
                self.emit('RET', self.reg[e[1]])
            else:
                self.cx(e)
                t = self.temp()
                self.emit('POP_VREG', t)
                self.emit('RET', t)
                self.free.append(t)
            return True
        if k == 'if':
            cc, l, r = s[1]
            self.cx(l)
            self.cx(r)
            self.emit('CMP')                            # virtual flags of l - r
            lt, lf = self.label(), self.label()
            for tgt in self.V.jcc_targets_pushed(lt, lf):
                self.emit('PUSH_IMM', ('L', tgt))
            self.emit('JCC', cc)
            lj = None
            for lab, arm in ((lt, s[2]), (lf, s[3])):
                self.start(lab)
                if not self.cseq(arm):
                    if lj is None:
                        lj = self.label()
                    self.emit('PUSH_IMM', ('L', lj))
                    self.emit('JMP')
            if lj is None:
                return True
            self.start(lj)
            return False
        if k == 'loop':
            n, body = s[1], s[2]
            ri = self.reg['i']
            self.emit('PUSH_IMM', n)
            self.emit('POP_VREG', ri)
            lh = self.label()
            self.emit('PUSH_IMM', ('L', lh))
            self.emit('JMP')
            self.start(lh)
            self.cseq(body)
            self.emit('PUSH_VREG', ri)                  # i = i - 1
            self.emit('PUSH_IMM', M64)
            self.emit('ADD')
            self.emit('POP_VREG', ri)
            self.emit('PUSH_VREG', ri)                  # i != 0: back to the head
            self.emit('PUSH_IMM', 0)
            self.emit('CMP')
            lx = self.label()
            for tgt in self.V.jcc_targets_pushed(lh, lx):
                self.emit('PUSH_IMM', ('L', tgt))
            self.emit('JCC', 'ne')
            self.start(lx)
            return False
        raise ValueError(k)

    def cseq(self, stmts):
        for s in stmts:
            if self.cs(s):
                return True
        return False

    def compile(self, prog, junk=0.0):
        """Blocks of the program. The entry pops the pushed native arguments into their
        vregs (random vreg numbers per program); junk: probability of a dead
        PUSH_IMM / POP_VREG pair before each instruction (into a vreg nothing reads)."""
        regs = list(range(16))
        self.r.shuffle(regs)
        names = list(ARGS[:self.nargs]) + sorted(_names(prog, set()) - set(ARGS))
        for n in names:
            self.reg[n] = regs.pop()
        self.junk = regs.pop()
        self.free = regs
        self.start(self.label())
        for a in reversed(self.V.args_pushed(self.nargs)):
            self.emit('POP_VREG', self.reg[a])
        if not self.cseq(prog):
            raise ValueError('the program falls off its end')
        if junk:
            for lab, ins in self.blocks.items():
                out = []
                for k, insn in enumerate(ins):
                    if k < len(ins) - 1 and self.r.random() < junk:
                        out.append(('PUSH_IMM', self.r.getrandbits(64)))
                        out.append(('POP_VREG', self.junk))
                    out.append(insn)
                self.blocks[lab] = out
        return self.blocks


def isize(h):
    return {'imm': 9, 'reg': 2, 'cc': 2}.get(OPERAND.get(h), 1)


def assemble(V, blocks, rng):
    """(code, info): the encrypted bytecode (entry block first, the other blocks in random
    order) and info = {offsets, opcodes, same, opc}: block offsets, number of opcode bytes,
    how many of them are stored equal to their plain opcode value, and [(offset, handler,
    plain opcode)] of every instruction."""
    rest = [lab for lab in blocks if lab != 0]
    rng.shuffle(rest)
    order = [0] + rest
    offs, pos = {}, 0
    for lab in order:
        offs[lab] = pos
        pos += sum(isize(h) for h, _ in blocks[lab])
    code = bytearray()
    nop = same = 0
    opc = []
    for lab in order:
        assert len(code) == offs[lab]
        k8, k64 = V.block_keys(offs[lab])          # every block starts with keys f(offset)
        for h, arg in blocks[lab]:
            op = rng.choice(V.ops[h])
            opc.append((len(code), h, op))
            b, k8 = V.enc_op(op, k8)
            code.append(b)
            nop += 1
            same += b == op
            kind = OPERAND.get(h)
            if kind == 'imm':
                v = offs[arg[1]] if isinstance(arg, tuple) else arg
                e, k64 = V.enc_imm(v, k64)
                code += e.to_bytes(8, 'little')
            elif kind == 'reg':                     # high nibble: noise (the handler masks it)
                b, k8 = V.enc_arg(arg | rng.randrange(16) << 4, k8)
                code.append(b)
            elif kind == 'cc':                      # bits 3..7: noise (the handler masks them)
                b, k8 = V.enc_arg(V.cc_bit[arg] | rng.randrange(32) << 3, k8)
                code.append(b)
    return bytes(code), {'offsets': offs, 'opcodes': nop, 'same': same, 'opc': opc}


class VMError(Exception):
    """The emulated bytecode did something the native VM must never do."""


BINOPS = {'ADD': lambda a, b: (a + b) & M64, 'NOR': lambda a, b: ~(a | b) & M64,
          'NAND': lambda a, b: ~(a & b) & M64, 'SHL': lambda a, b: (a << (b & 63)) & M64,
          'SHR': lambda a, b: a >> (b & 63), 'MUL': lambda a, b: (a * b) & M64}


def emulate(V, code, args, nargs, limit=200000):
    """Run the encrypted bytecode like the C interpreter: (result, vinsns, max stack depth,
    handlers used). Raises VMError on anything the native VM must never meet."""
    st = [args[ARGS.index(a)] for a in V.args_pushed(nargs)]
    R = [None] * 16
    flags = (0, 0, 0, 0)
    vip, steps, maxd, used = 0, 0, len(st), set()
    k8, k64 = V.block_keys(0)
    try:
        while True:
            if steps >= limit:
                raise VMError('step limit')
            if not 0 <= vip < len(code):
                raise VMError(f'vip {vip:#x} outside the bytecode')
            op, k8 = V.dec_op(code[vip], k8)
            vip += 1
            steps += 1
            h = V.handler_of(op)
            used.add(h)
            kind = OPERAND.get(h)
            if kind == 'imm':
                v, k64 = V.dec_imm(int.from_bytes(code[vip:vip + 8], 'little'), k64)
                vip += 8
            elif kind:
                v, k8 = V.dec_arg(code[vip], k8)
                vip += 1
            if h == 'PUSH_IMM':
                st.append(v)
            elif h == 'PUSH_VREG':
                if R[v & 15] is None:
                    raise VMError(f'read of vreg {v & 15} before any write')
                st.append(R[v & 15])
            elif h == 'POP_VREG':
                R[v & 15] = st.pop()
            elif h in BINOPS:
                b = st.pop()
                a = st.pop()
                st.append(BINOPS[h](a, b))
            elif h == 'CMP':
                b = st.pop()
                a = st.pop()
                flags = sub_flags(a, b)
            elif h in ('JCC', 'JMP'):
                if h == 'JMP':
                    t = st.pop()
                else:
                    c = V.cond_of_bit(v & 7)
                    idx = COND_PY[c](*flags) if c else 0
                    top, sec = st.pop(), st.pop()
                    t_true, t_false = (top, sec) if V.up else (sec, top)
                    t = t_true if idx else t_false
                vip = t
                k8, k64 = V.block_keys(t)
            elif h == 'RET':
                if R[v & 15] is None:
                    raise VMError(f'return of vreg {v & 15} before any write')
                return R[v & 15], steps, maxd, used
            else:
                raise VMError(f'invalid opcode {op:#x} at {vip - 1:#x}')
            maxd = max(maxd, len(st))
            if maxd > VSTK:
                raise VMError('virtual stack overflow')
    except IndexError:
        raise VMError('virtual stack underflow') from None


# ---------------------------------------------------------------- random programs
OPS = ('add', 'sub', 'mul', 'and', 'or', 'xor', 'shl', 'shr', 'not', 'neg')
OPW = (3, 2, 1.2, 2, 2, 3, 1, 1, 0.7, 0.5)
CCS = ('eq', 'ne', 'ult', 'ule', 'ugt', 'uge', 'slt')
CCW = (1.2, 1.2, 1, 0.8, 1, 0.8, 1.5)


def variables(e, acc=None):
    acc = set() if acc is None else acc
    if e[0] == 'v':
        acc.add(e[1])
    elif e[0] != 'k':
        for x in e[1:]:
            variables(x, acc)
    return acc


class ProgramGen:
    """Draws programs (see the module doc); once: locals that may appear at most once in
    one expression (loop-carried values: keeps the unrolled truth polynomial)."""

    def __init__(self, rng, nargs):
        self.r, self.args = rng, list(ARGS[:nargs])
        self.once, self.used = set(), set()

    def const(self):
        c = self.r.random()
        if c < 0.45:
            return self.r.randrange(2, 256)
        if c < 0.7:
            return self.r.getrandbits(32) | 1
        return self.r.getrandbits(64) | 1

    def leaf(self, pool, kp):
        cand = [(n, w) for n, w in pool if not (n in self.once and n in self.used)]
        if not cand or self.r.random() < kp:
            return ('k', self.const())
        n = self.r.choices([c[0] for c in cand], weights=[c[1] for c in cand])[0]
        self.used.add(n)
        return ('v', n)

    def expr(self, nops, pool, kp=0.2):
        r = self.r
        if nops <= 0:
            return self.leaf(pool, kp)
        op = r.choices(OPS, weights=OPW)[0]
        if op in ('not', 'neg'):
            if nops == 1 or r.random() < 0.5:
                e = self.expr(nops - 1, pool, kp)
                if e[0] == op:                          # ~~e = --e = e: use the other one
                    op = 'neg' if op == 'not' else 'not'
                return (op, e)
            op = 'xor'
        if op in ('shl', 'shr'):
            if nops < 2 or r.random() < 0.85:
                return (op, self.expr(nops - 1, pool, kp), ('k', r.randrange(1, 64)))
            k = r.randint(1, min(2, nops - 1))
            return (op, self.expr(nops - 1 - k, pool, kp), self.expr(k, pool, kp))
        rest = nops - 1
        left = r.randint(rest // 3, rest - rest // 3)
        a = self.expr(left, pool, kp)
        b = self.expr(rest - left, pool, kp)
        if a[0] == 'k' and b[0] == 'k':
            a = self.leaf(pool, 0)
        if a == b and op in ('and', 'or', 'xor', 'sub'):    # a & a = a | a = a, a ^ a = a - a = 0
            b = self.leaf([(n, w) for n, w in pool if ('v', n) != a], 0.25)
        return (op, a, b)

    def fresh(self, nops, pool, kp=0.2, must=()):
        """An expression with nops operations that reads every name in must."""
        self.used = set()
        e = self.expr(nops, pool, kp)
        for n in must:
            if n not in variables(e):
                e = (self.r.choice(('add', 'xor', 'sub')), ('v', n), e)
        self.used = set()
        return e

    def eq_operands(self):
        r, pool = self.r, [(a, 1) for a in self.args]
        kind = r.random()
        if kind < 0.4:                                  # (e & mask) == k
            mask = r.choice((0xf, 0xff, 0xffff, 0xffffffff))
            return ('and', self.fresh(r.randint(0, 2), pool, 0), ('k', mask)), ('k', r.getrandbits(64) & mask)
        if kind < 0.7 or len(self.args) < 2:            # e == e(random point)
            e = self.fresh(r.randint(1, 3), pool, 0.2)
            return e, ('k', ev(e, {a: r.getrandbits(64) for a in self.args}))
        a = r.choice(self.args)                         # x == e(other arguments)
        return ('v', a), self.fresh(r.randint(0, 2), [(n, 1) for n in self.args if n != a], 0.3)

    def cond(self, pool):
        cc = self.r.choices(CCS, weights=CCW)[0]
        if cc in ('eq', 'ne'):
            return (cc,) + self.eq_operands()
        for _ in range(20):
            l, r = self.fresh(self.r.randint(0, 2), pool, 0.05), self.fresh(self.r.randint(0, 2), pool, 0.4)
            if l != r and variables(l) | variables(r):
                return (cc, l, r)
        return (cc, ('v', self.args[0]), ('k', self.const()))

    def split(self, total, k):
        """total operations over k expressions, each at least 1."""
        cuts = sorted(self.r.sample(range(1, total), k - 1)) if k > 1 else []
        return [b - a for a, b in zip([0] + cuts, cuts + [total])]

    def expr_prog(self, ops):
        """Straight line: 0-2 locals, then ret."""
        nloc = self.r.choice((0, 1, 1, 2)) if ops >= 8 else 0
        parts = self.split(ops, nloc + 1)
        pool = [(a, 1.0) for a in self.args]
        stmts = []
        for i in range(nloc):
            stmts.append(('set', LOCALS[i], self.fresh(parts[i], pool)))
            pool.append((LOCALS[i], 2.5))
        stmts.append(('ret', self.fresh(parts[-1], pool, must=LOCALS[:nloc])))
        return stmts

    def prelude(self, locs):
        pool = [(a, 1.0) for a in self.args]
        return [('set', n, self.fresh(self.r.randint(1, 4), pool)) for n in locs]

    def arm(self, nb, pool, locs, ret_ok):
        s = [('set', self.r.choice(locs), self.fresh(self.r.randint(1, 3), pool))
             for _ in range(self.r.choice((1, 1, 2)))]
        return s + (self.branch_seq(nb, pool, locs, ret_ok) if nb else [])

    def branch_seq(self, nb, pool, locs, ret_ok=True):
        """Statements holding exactly nb if statements (sequential and nested); with ret_ok
        one arm of an if may end with an early ret."""
        r, stmts = self.r, []
        while nb > 0:
            inner = r.randint(0, nb - 1) if r.random() < 0.5 else 0
            nb -= 1 + inner
            ti = r.randint(0, inner)
            then, els = self.arm(ti, pool, locs, ret_ok), self.arm(inner - ti, pool, locs, ret_ok)
            if ret_ok and r.random() < 0.25:
                (then if r.random() < 0.5 else els).append(('ret', self.fresh(r.randint(1, 4), pool)))
            stmts.append(('if', self.cond(pool), then, els))
            if r.random() < 0.3:
                stmts.append(('set', r.choice(locs), self.fresh(r.randint(1, 3), pool)))
        return stmts

    def branch_prog(self, nb):
        locs = ['a', 'b'] if self.r.random() < 0.7 else ['a']
        pool = [(a, 1.0) for a in self.args] + [(n, 2.0) for n in locs]
        stmts = self.prelude(locs) + self.branch_seq(nb, pool, locs)
        return stmts + [('ret', self.fresh(self.r.randint(1, 6), pool, must=locs))]

    def loop(self, n, locs):
        """('loop', n, body): each local updated from itself (at most once per expression),
        the arguments, the counter i and, for b, the new a."""
        self.once = set(locs)
        body = []
        for k, c in enumerate(locs):                    # a reads a; b reads b and the new a
            pool = [(a, 1.0) for a in self.args] + [('i', 1.0)] + [(d, 3.0) for d in locs[:k + 1]]
            body.append(('set', c, self.fresh(self.r.randint(2, 5), pool, 0.25, must=(c,))))
        self.once = set()
        return ('loop', n, body)

    def loop_prog(self, n):
        locs = ['a', 'b'] if self.r.random() < 0.6 else ['a']
        stmts = self.prelude(locs) + [self.loop(n, locs)]
        self.once = set(locs)
        ret = self.fresh(self.r.randint(1, 6), [(a, 1.0) for a in self.args] + [(c, 3.0) for c in locs], must=locs)
        self.once = set()
        return stmts + [('ret', ret)]

    def mixed_prog(self, nb, n):
        """A loop and nb branches: the branches before the loop (no early ret) or after it."""
        locs = ['a', 'b']
        pool = [(a, 1.0) for a in self.args] + [(c, 2.0) for c in locs]
        stmts = self.prelude(locs)
        if self.r.random() < 0.5:
            stmts += self.branch_seq(nb, pool, locs, ret_ok=False) + [self.loop(n, locs)]
        else:
            lp = self.loop(n, locs)
            self.once = set(locs)                       # keep the post-loop truth small
            stmts += [lp] + self.branch_seq(nb, pool, locs)
        self.once = set(locs)
        ret = self.fresh(self.r.randint(1, 5), pool, must=locs)
        self.once = set()
        return stmts + [('ret', ret)]
