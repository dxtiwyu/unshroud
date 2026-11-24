"""mut_x86.py: the x86-64 instruction model of the mut suite.

Instructions are Ins(m, *ops, tag=None). Operands are tuples:
  ('r', reg) a 64-bit register, ('r32', reg) its 32-bit view, ('r8', reg) its low byte
  ('i', v)   an immediate (Python int; imm32 operands sign-extend, so keep
             -2**31 <= v < 2**31; only 'mov reg, imm' takes any 64-bit value)
  ('m', base, disp)                 qword ptr [base + disp]
  ('a', base, index, scale, disp)   an lea address (base or index may be None)
  ('l', name)                       a label
A label is Ins('label', ('l', name)).
info(ins): the registers read and written (bit masks, rsp left out) and the flags
behaviour. liveness(code): live registers and flags before / after each instruction,
exact over the control flow (labels, jcc, jmp, ret). emulate(code, args): runs the
code on a model CPU whose undefined flags are poisoned (EmuError when one reaches a
jcc / setcc / cmov / adc / sbb) and checks rsp and the callee-saved registers at ret.
"""
NL = chr(10)
MASK = (1 << 64) - 1
SIGN = 1 << 63

GPR = ('rax', 'rcx', 'rdx', 'rbx', 'rsp', 'rbp', 'rsi', 'rdi',
       'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15')
BIT = {r: 1 << i for i, r in enumerate(GPR)}
CALLEE_SAVED = ('rbx', 'rbp', 'rdi', 'rsi', 'r12', 'r13', 'r14', 'r15')
CS_MASK = sum(BIT[r] for r in CALLEE_SAVED)
USABLE = tuple(r for r in GPR if r not in ('rsp', 'rbp'))
USABLE_MASK = sum(BIT[r] for r in USABLE)
ARGREGS = ('rcx', 'rdx', 'r8', 'r9')
R32 = {'rax': 'eax', 'rcx': 'ecx', 'rdx': 'edx', 'rbx': 'ebx', 'rsp': 'esp', 'rbp': 'ebp',
       'rsi': 'esi', 'rdi': 'edi'}
R8 = {'rax': 'al', 'rcx': 'cl', 'rdx': 'dl', 'rbx': 'bl', 'rsp': 'spl', 'rbp': 'bpl',
      'rsi': 'sil', 'rdi': 'dil'}
for _i in range(8, 16):
    R32[f'r{_i}'] = f'r{_i}d'
    R8[f'r{_i}'] = f'r{_i}b'
CC_INV = {'o': 'no', 'no': 'o', 'b': 'ae', 'ae': 'b', 'e': 'ne', 'ne': 'e', 'be': 'a',
          'a': 'be', 's': 'ns', 'ns': 's', 'p': 'np', 'np': 'p', 'l': 'ge', 'ge': 'l',
          'le': 'g', 'g': 'le'}
NONE, PART, FULL = 0, 1, 2


def simm(v):
    """v as a signed 64-bit value."""
    v &= MASK
    return v - (1 << 64) if v & SIGN else v


def fits32(v):
    return -2**31 <= simm(v) < 2**31


def regs_of(mask):
    """Register names of a bit mask, in GPR order."""
    return [r for r in GPR if mask & BIT[r]]


class Ins:
    __slots__ = ('m', 'ops', 'tag')

    def __init__(self, m, *ops, tag=None):
        self.m = m
        self.ops = ops
        self.tag = tag

    def __repr__(self):
        return fmt(self).strip()


def R(r):
    return ('r', r)


def I(v):
    return ('i', v)


def M(base, disp=0):
    return ('m', base, disp)


def A(base, index=None, scale=1, disp=0):
    return ('a', base, index, scale, disp)


def L(name):
    return ('l', name)


def label(name):
    return Ins('label', ('l', name))


def is_jcc(m):
    return m[0] == 'j' and m != 'jmp'


def _addr(base, index, scale, disp):
    parts = []
    if base:
        parts.append(base)
    if index:
        parts.append(index if scale == 1 else f'{index}*{scale}')
    s = ' + '.join(parts)
    if not s:
        s = str(disp)
    elif disp > 0:
        s += f' + {disp}'
    elif disp < 0:
        s += f' - {-disp}'
    return '[' + s + ']'


def fop(o):
    k = o[0]
    if k == 'r':
        return o[1]
    if k == 'r32':
        return R32[o[1]]
    if k == 'r8':
        return R8[o[1]]
    if k == 'i':
        return str(o[1])
    if k == 'l':
        return o[1]
    if k == 'm':
        return 'qword ptr ' + _addr(o[1], None, 1, o[2])
    if k == 'a':
        return _addr(o[1], o[2], o[3], o[4])
    raise ValueError(f'bad operand {o!r}')


def fmt(ins):
    """One line of Intel-syntax assembly (labels end with a colon)."""
    m, ops = ins.m, ins.ops
    if m == 'label':
        return ops[0][1] + ':'
    if m == 'mov' and ops[1][0] == 'i' and ops[0][0] == 'r' and not fits32(ops[1][1]):
        return f'    movabs {ops[0][1]}, {hex(ops[1][1] & MASK)}'
    if not ops:
        return '    ' + m
    return '    ' + m + ' ' + ', '.join(fop(o) for o in ops)


def check_operands(ins):
    """Raise ValueError when an immediate does not fit its encoding."""
    m, ops = ins.m, ins.ops
    for k, o in enumerate(ops):
        if o[0] != 'i':
            continue
        if m == 'mov' and k == 1 and ops[0][0] == 'r':
            if not -2**63 <= o[1] < 2**63:
                raise ValueError(f'{ins!r}: mov immediate out of range')
        elif m in ('shl', 'shr', 'sar', 'rol', 'ror', 'bt', 'bts', 'btr', 'btc'):
            if not 0 <= o[1] < 64:
                raise ValueError(f'{ins!r}: bad count')
        elif not -2**31 <= o[1] < 2**31:
            raise ValueError(f'{ins!r}: immediate does not fit 32 bits')
    for o in ops:
        if o[0] == 'a' and not -2**31 <= o[4] < 2**31:
            raise ValueError(f'{ins!r}: displacement does not fit 32 bits')


# ---------------------------------------------------------------- def / use, liveness
def _rb(o):
    """Register bits read when o is a source operand (registers of an address too)."""
    k = o[0]
    if k in ('r', 'r32', 'r8', 'm'):
        return BIT[o[1]]
    if k == 'a':
        return (BIT[o[1]] if o[1] else 0) | (BIT[o[2]] if o[2] else 0)
    return 0


def mentioned(ins):
    """Every register an instruction names (rcx too for a shift by cl)."""
    b = 0
    for o in ins.ops:
        b |= _rb(o)
    if ins.m in ('shl', 'shr', 'sar', 'rol', 'ror') and ins.ops[1][0] == 'r8':
        b |= BIT['rcx']
    return b


_ALU = ('add', 'sub', 'and', 'or', 'xor', 'adc', 'sbb')


def info(ins):
    """(use bits, def bits, reads flags, flag write NONE / PART / FULL); rsp left out.
    A partial write (8-bit register, setcc) counts as a use and a def; PART means the
    instruction changes some flags but passes others through (it does not kill)."""
    m, ops = ins.m, ins.ops
    u = d = 0
    fr = False
    fw = NONE
    if m in ('mov', 'movzx', 'lea'):
        dst, src = ops
        u = _rb(src)
        if dst[0] == 'm':
            u |= BIT[dst[1]]
        elif dst[0] == 'r8':
            u |= BIT[dst[1]]
            d = BIT[dst[1]]
        else:
            d = BIT[dst[1]]
    elif m in _ALU:
        dst, src = ops
        if m in ('xor', 'sub') and dst == src and dst[0] in ('r', 'r32'):
            d = BIT[dst[1]]                          # zeroing idiom: no use
        else:
            u = _rb(dst) | _rb(src)
            if dst[0] != 'm':
                d = BIT[dst[1]]
        fw = FULL
        fr = m in ('adc', 'sbb')
    elif m in ('cmp', 'test'):
        u = _rb(ops[0]) | _rb(ops[1])
        fw = FULL
    elif m == 'bt':                                  # ZF passes through: PART
        u = _rb(ops[0]) | _rb(ops[1])
        fw = PART
    elif m in ('bts', 'btr', 'btc'):
        u = _rb(ops[0]) | _rb(ops[1])
        d = BIT[ops[0][1]]
        fw = PART
    elif m == 'neg':
        u = d = BIT[ops[0][1]]
        fw = FULL
    elif m in ('not', 'bswap'):
        u = d = BIT[ops[0][1]]
    elif m in ('inc', 'dec'):
        u = d = BIT[ops[0][1]]
        fw = PART
    elif m == 'imul':
        u = (_rb(ops[0]) | _rb(ops[1])) if len(ops) == 2 else _rb(ops[1])
        d = BIT[ops[0][1]]
        fw = FULL
    elif m in ('shl', 'shr', 'sar', 'rol', 'ror'):
        dst, c = ops
        u = d = BIT[dst[1]]
        if c[0] == 'r8':
            u |= BIT['rcx']
            fw = PART                                # count 0 leaves every flag
        elif c[1] & 63 == 0:
            fw = NONE
        else:
            fw = PART if m in ('rol', 'ror') else FULL
    elif m == 'push':
        u = _rb(ops[0])
    elif m == 'pop':
        if ops[0][0] == 'm':
            u = BIT[ops[0][1]]
        else:
            d = BIT[ops[0][1]]
    elif m == 'pushfq':
        fr = True
    elif m == 'popfq':
        fw = FULL
    elif m == 'xchg':
        u = d = _rb(ops[0]) | _rb(ops[1])
    elif m.startswith('set'):
        u = d = BIT[ops[0][1]]
        fr = True
    elif m.startswith('cmov'):
        u = _rb(ops[0]) | _rb(ops[1])
        d = BIT[ops[0][1]]
        fr = True
    elif m == 'ret':
        u = BIT['rax'] | CS_MASK
    elif m in ('jmp', 'label', 'nop'):
        pass
    elif m[0] == 'j':
        fr = True
    elif m in ('stc', 'clc'):
        fw = PART
    elif m == 'cmc':
        fr = True
        fw = PART
    else:
        raise ValueError(f'unknown mnemonic {m}')
    nsp = ~BIT['rsp']
    return u & nsp, d & nsp, fr, fw


def writes_flags(ins):
    return info(ins)[3] != NONE


def successors(code):
    lab = {ins.ops[0][1]: i for i, ins in enumerate(code) if ins.m == 'label'}
    n = len(code)
    succ = []
    for i, ins in enumerate(code):
        m = ins.m
        if m == 'ret':
            s = ()
        elif m == 'jmp':
            s = (lab[ins.ops[0][1]],)
        elif is_jcc(m):
            s = (i + 1, lab[ins.ops[0][1]]) if i + 1 < n else (lab[ins.ops[0][1]],)
        else:
            s = (i + 1,) if i + 1 < n else ()
        succ.append(s)
    return succ


def liveness(code):
    """(live_in, live_out, flags_in, flags_out) per instruction: register bit masks and
    bools, by a backward fixpoint over the control flow."""
    n = len(code)
    succ = successors(code)
    inf = [info(x) for x in code]
    lin = [0] * n
    lout = [0] * n
    fin = [False] * n
    fout = [False] * n
    changed = True
    while changed:
        changed = False
        for i in range(n - 1, -1, -1):
            o = 0
            fo = False
            for s in succ[i]:
                o |= lin[s]
                fo = fo or fin[s]
            u, d, fr, fw = inf[i]
            li = u | (o & ~d)
            fi = fr or (fo and fw != FULL)
            if li != lin[i] or fi != fin[i] or o != lout[i] or fo != fout[i]:
                lin[i], lout[i], fin[i], fout[i] = li, o, fi, fo
                changed = True
    return lin, lout, fin, fout


# ---------------------------------------------------------------- emulator
class EmuError(Exception):
    """The code did something the mutation must never do (the message says what)."""


FLAGS = ('CF', 'PF', 'ZF', 'SF', 'OF')
_CC = {
    'o': lambda g: g('OF'), 'no': lambda g: 1 - g('OF'),
    'b': lambda g: g('CF'), 'ae': lambda g: 1 - g('CF'),
    'e': lambda g: g('ZF'), 'ne': lambda g: 1 - g('ZF'),
    'be': lambda g: g('CF') | g('ZF'), 'a': lambda g: 1 - (g('CF') | g('ZF')),
    's': lambda g: g('SF'), 'ns': lambda g: 1 - g('SF'),
    'p': lambda g: g('PF'), 'np': lambda g: 1 - g('PF'),
    'l': lambda g: g('SF') ^ g('OF'), 'ge': lambda g: 1 - (g('SF') ^ g('OF')),
    'le': lambda g: g('ZF') | (g('SF') ^ g('OF')),
    'g': lambda g: 1 - (g('ZF') | (g('SF') ^ g('OF'))),
}
_SIZE = {'r': 64, 'm': 64, 'r32': 32, 'r8': 8}
RSP0 = 0x7ff00000


def _par(v):
    return 1 - (bin(v & 0xff).count('1') & 1)


def emulate(code, args, init, max_steps=400000, trace=None, state=None, abi=True):
    """Run code with rcx, rdx, r8, r9 = args (the other registers from init, a dict of
    16 values); return rax at ret. Raises EmuError on an undefined flag read, a read of
    unwritten stack, a flags image used as data, a wrong rsp or a changed callee-saved
    register at ret, or too many steps. trace: a set that receives the index of every
    executed instruction (labels included). state: a dict that receives the final regs,
    flags and mem. abi=False skips the callee-saved check."""
    lab = {ins.ops[0][1]: i for i, ins in enumerate(code) if ins.m == 'label'}
    regs = dict(init)
    for r, v in zip(ARGREGS, args):
        regs[r] = v & MASK
    regs['rsp'] = RSP0
    start = dict(regs)
    mem = {RSP0: 'RET'}
    fl = {k: (init['rax'] >> i) & 1 for i, k in enumerate(FLAGS)}

    def getf(k):
        v = fl[k]
        if v is None:
            raise EmuError(f'undefined flag {k} read at {ins!r} (pc {pc - 1})')
        return v

    def addr(o):
        if o[0] == 'm':
            return (regs[o[1]] + o[2]) & MASK
        a = o[4]
        if o[1]:
            a += regs[o[1]]
        if o[2]:
            a += regs[o[2]] * o[3]
        return a & MASK

    def rd(o):
        k = o[0]
        if k == 'r':
            return regs[o[1]]
        if k == 'i':
            return o[1] & MASK
        if k == 'r32':
            return regs[o[1]] & 0xffffffff
        if k == 'r8':
            return regs[o[1]] & 0xff
        if k == 'm':
            a = addr(o)
            if a not in mem:
                raise EmuError(f'read of unwritten stack {a:#x} at {ins!r}')
            v = mem[a]
            if type(v) is not int:
                raise EmuError(f'{v!r} read as data at {ins!r}')
            return v
        raise EmuError(f'bad operand {o!r}')

    def wr(o, v):
        k = o[0]
        if k == 'r':
            regs[o[1]] = v & MASK
        elif k == 'r32':
            regs[o[1]] = v & 0xffffffff
        elif k == 'r8':
            regs[o[1]] = (regs[o[1]] & ~0xff) | (v & 0xff)
        elif k == 'm':
            a = addr(o)
            if a % 8:
                raise EmuError(f'unaligned store at {ins!r}')
            mem[a] = v & MASK
        else:
            raise EmuError(f'bad destination {o!r}')

    def push(v):
        regs['rsp'] = (regs['rsp'] - 8) & MASK
        mem[regs['rsp']] = v

    def pop():
        a = regs['rsp']
        if a not in mem:
            raise EmuError(f'pop of unwritten stack at {ins!r}')
        regs['rsp'] = (a + 8) & MASK
        return mem[a]

    def szf(res, n):
        fl['ZF'] = 1 if res == 0 else 0
        fl['SF'] = (res >> (n - 1)) & 1
        fl['PF'] = _par(res)

    pc = 0
    steps = 0
    n_code = len(code)
    while True:
        if pc >= n_code:
            raise EmuError('ran past the end of the code')
        ins = code[pc]
        if trace is not None:
            trace.add(pc)
        pc += 1
        steps += 1
        if steps > max_steps:
            raise EmuError('too many steps')
        m, ops = ins.m, ins.ops
        if m == 'label' or m == 'nop':
            continue
        if m in ('mov', 'movzx'):
            wr(ops[0], rd(ops[1]))
        elif m == 'lea':
            wr(ops[0], addr(ops[1]))
        elif m in ('add', 'adc', 'sub', 'sbb', 'cmp'):
            n = _SIZE[ops[0][0]]
            mk = (1 << n) - 1
            a = rd(ops[0]) & mk
            b = rd(ops[1]) & mk
            c = getf('CF') if m in ('adc', 'sbb') else 0
            if m in ('add', 'adc'):
                full = a + b + c
                res = full & mk
                fl['CF'] = full >> n
                fl['OF'] = (((a ^ res) & (b ^ res)) >> (n - 1)) & 1
            else:
                full = a - b - c
                res = full & mk
                fl['CF'] = 1 if full < 0 else 0
                fl['OF'] = (((a ^ b) & (a ^ res)) >> (n - 1)) & 1
            szf(res, n)
            if m != 'cmp':
                wr(ops[0], res)
        elif m in ('and', 'or', 'xor', 'test'):
            n = _SIZE[ops[0][0]]
            mk = (1 << n) - 1
            a = rd(ops[0]) & mk
            b = rd(ops[1]) & mk
            res = a & b if m in ('and', 'test') else (a | b if m == 'or' else a ^ b)
            fl['CF'] = fl['OF'] = 0
            szf(res, n)
            if m != 'test':
                wr(ops[0], res)
        elif m == 'neg':
            a = rd(ops[0])
            res = (-a) & MASK
            fl['CF'] = 1 if a else 0
            fl['OF'] = 1 if a == SIGN else 0
            szf(res, 64)
            wr(ops[0], res)
        elif m == 'not':
            wr(ops[0], ~rd(ops[0]))
        elif m in ('inc', 'dec'):
            a = rd(ops[0])
            res = (a + (1 if m == 'inc' else -1)) & MASK
            fl['OF'] = 1 if (m == 'inc' and a == SIGN - 1) or (m == 'dec' and a == SIGN) else 0
            szf(res, 64)
            wr(ops[0], res)
        else:
            r = _emu_more(ins, m, ops, regs, fl, rd, wr, push, pop, getf, szf, lab)
            if r is not None:
                if r[0] == 'jump':
                    pc = r[1]
                else:
                    if regs['rsp'] != RSP0 + 8:
                        raise EmuError(f'rsp {regs["rsp"]:#x} at ret, expected {RSP0 + 8:#x}')
                    for c in CALLEE_SAVED if abi else ():
                        if regs[c] != start[c]:
                            raise EmuError(f'callee-saved {c} changed')
                    if state is not None:
                        state.update(regs=dict(regs), flags=dict(fl), mem=dict(mem))
                    return regs['rax']


def _emu_more(ins, m, ops, regs, fl, rd, wr, push, pop, getf, szf, lab):
    """The less common instructions; returns ('jump', index), ('ret',) or None."""
    if m == 'imul':
        a, b = (rd(ops[0]), rd(ops[1])) if len(ops) == 2 else (rd(ops[1]), rd(ops[2]))
        prod = simm(a) * simm(b)
        res = prod & MASK
        fl['CF'] = fl['OF'] = 0 if simm(res) == prod else 1
        fl['ZF'] = fl['SF'] = fl['PF'] = None
        wr(ops[0], res)
    elif m in ('shl', 'shr', 'sar', 'rol', 'ror'):
        c = (regs['rcx'] if ops[1][0] == 'r8' else ops[1][1]) & 63
        if c == 0:
            return None
        a = rd(ops[0])
        if m == 'shl':
            res = (a << c) & MASK
            fl['CF'] = (a >> (64 - c)) & 1
            fl['OF'] = ((res >> 63) ^ fl['CF']) if c == 1 else None
            szf(res, 64)
        elif m == 'shr':
            res = a >> c
            fl['CF'] = (a >> (c - 1)) & 1
            fl['OF'] = (a >> 63) if c == 1 else None
            szf(res, 64)
        elif m == 'sar':
            sa = simm(a)
            res = (sa >> c) & MASK
            fl['CF'] = (sa >> (c - 1)) & 1
            fl['OF'] = 0 if c == 1 else None
            szf(res, 64)
        elif m == 'rol':
            res = ((a << c) | (a >> (64 - c))) & MASK
            fl['CF'] = res & 1
            fl['OF'] = ((res >> 63) ^ (res & 1)) if c == 1 else None
        else:
            res = ((a >> c) | (a << (64 - c))) & MASK
            fl['CF'] = res >> 63
            fl['OF'] = ((res >> 63) ^ ((res >> 62) & 1)) if c == 1 else None
        wr(ops[0], res)
    elif m == 'push':
        push(rd(ops[0]))
    elif m == 'pop':
        v = pop()
        if type(v) is not int:
            raise EmuError(f'pop of {v!r} at {ins!r}')
        wr(ops[0], v)
    elif m == 'pushfq':
        push(tuple(fl[k] for k in FLAGS))
    elif m == 'popfq':
        v = pop()
        if type(v) is not tuple:
            raise EmuError(f'popfq of {v!r}')
        fl.update(zip(FLAGS, v))
    elif m == 'xchg':
        a, b = rd(ops[0]), rd(ops[1])
        wr(ops[0], b)
        wr(ops[1], a)
    elif m == 'bswap':
        wr(ops[0], int.from_bytes(rd(ops[0]).to_bytes(8, 'little'), 'big'))
    elif m.startswith('set'):
        wr(ops[0], _CC[m[3:]](getf))
    elif m.startswith('cmov'):
        if _CC[m[4:]](getf):
            wr(ops[0], rd(ops[1]))
    elif m in ('bt', 'bts', 'btr', 'btc'):
        a = rd(ops[0])
        k = rd(ops[1]) & 63
        fl['CF'] = (a >> k) & 1
        fl['OF'] = fl['SF'] = fl['PF'] = None
        if m == 'bts':
            wr(ops[0], a | (1 << k))
        elif m == 'btr':
            wr(ops[0], a & ~(1 << k))
        elif m == 'btc':
            wr(ops[0], a ^ (1 << k))
    elif m == 'jmp':
        return ('jump', lab[ops[0][1]])
    elif m[0] == 'j':
        if _CC[m[1:]](getf):
            return ('jump', lab[ops[0][1]])
    elif m == 'ret':
        v = pop()
        if v != 'RET':
            raise EmuError(f'ret to {v!r}')
        return ('ret',)
    elif m == 'stc':
        fl['CF'] = 1
    elif m == 'clc':
        fl['CF'] = 0
    elif m == 'cmc':
        fl['CF'] = 1 - getf('CF')
    else:
        raise EmuError(f'unknown mnemonic {m}')
    return None
