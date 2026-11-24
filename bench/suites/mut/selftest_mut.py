"""selftest_mut.py: adversarial checks of the mut suite's machinery (not of the DLL:
gen/validate.py does that).

usage: python -I suites/mut/selftest_mut.py [--programs 40] [--trials 40]
  rules     every substitution candidate of mut_pass, on instruction instances covering
            every rule, against the original instruction on random / edge machine states
            (emulated): all registers but the temporary equal, flags equal for 'exact'
            (where the original defines them), untouched for 'free'; memory slots equal
  opaque    each opaque predicate kind: its instruction sequence makes its jcc condition
            hold on edge / random operands (emulated), and the identity itself is proved
            (z3, or exhaustively over the residues it depends on)
  sabotage  a wrong opaque condition code must be caught by gen_mut.check_emulation
  deadjunk  junk inserted in dead code (the bug of an earlier version: opaque predicates
            and junk in unreachable blocks) must be caught by gen_mut.check_emulation
  programs  random programs mutated at the three strengths, emulated against the
            interpreter with the dead-code check (gen_mut.check_emulation)
Exit code 1 when anything fails.
"""
import argparse
import os
import random
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), 'gen'))
import gen_mut as G                             # noqa: E402
import mut_emit as E                            # noqa: E402
import mut_pass as MP                           # noqa: E402
import mut_prog as P                            # noqa: E402
import mut_x86 as X                             # noqa: E402

REGS = ('rax', 'rcx', 'rdx', 'rbx', 'rsi', 'rdi', 'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15')
RBP0 = 0x7fe00000
SLOT = X.M('rbp', -8)


def rand_state(r):
    st = {}
    for g in X.GPR:
        c = r.random()
        st[g] = r.choice(P.EDGE) if c < 0.35 else (r.randrange(-8, 33) & X.MASK if c < 0.5 else r.getrandbits(64))
    st['rbp'] = RBP0
    return st


def run(code, init):
    """Final state of code + ret (memory slot [rbp - 8] filled first from r15)."""
    full = [X.Ins('mov', SLOT, X.R('r15'))] + list(code) + [X.Ins('ret')]
    st = {}
    X.emulate(full, [init[g] for g in X.ARGREGS], init, state=st, abi=False)
    st['mem'] = {a: v for a, v in st['mem'].items() if a < RBP0 + 0x1000}
    return st


def instances(r):
    """Instruction instances that reach every substitution rule (random registers)."""
    a, b, c = r.sample(REGS, 3)
    Ra, Rb, I, M_ = X.R(a), X.R(b), X.I, SLOT
    k = r.choice([1, -1, 0, 2, -2, 5, 0x7fffffff, -2**31, r.randrange(-2**31, 2**31), r.randrange(-300, 300)])
    v = r.choice([0, X.MASK, 7, 1 << 63, r.getrandbits(64), k & X.MASK])
    out = [X.Ins('mov', Ra, I(X.simm(v))), X.Ins('mov', Ra, Rb), X.Ins('mov', Ra, M_),
           X.Ins('mov', M_, Ra), X.Ins('mov', M_, I(k)),
           X.Ins('lea', Ra, X.A(b, None, 1, k)), X.Ins('lea', Ra, X.A(a, None, 1, k)),
           X.Ins('lea', Ra, X.A(a, b)), X.Ins('lea', Ra, X.A(b, a)), X.Ins('lea', Ra, X.A(b, c)),
           X.Ins('lea', Ra, X.A(b, c, r.choice((2, 4, 8)), k))]
    for m in ('add', 'sub', 'xor', 'and', 'or'):
        out += [X.Ins(m, Ra, I(k)), X.Ins(m, Ra, Rb), X.Ins(m, Ra, Ra), X.Ins(m, Ra, M_)]
    out += [X.Ins('cmp', Ra, I(k)), X.Ins('cmp', Ra, Rb), X.Ins('cmp', M_, I(k)), X.Ins('cmp', Ra, M_),
            X.Ins('cmp', M_, Ra), X.Ins('test', Ra, I(k)), X.Ins('test', M_, I(k))]
    out += [X.Ins(m, Ra) for m in ('not', 'neg', 'inc', 'dec')]
    out += [X.Ins(m, Ra, I(r.choice((1, 2, 3, 5, 30, 31, 63)))) for m in ('shl', 'shr', 'sar', 'rol', 'ror')]
    out += [X.Ins('imul', Ra, Rb, I(k)), X.Ins('imul', Ra, Ra, I(k)), X.Ins('imul', Ra, M_, I(k)),
            X.Ins('imul', Ra, M_), X.Ins('imul', Ra, Rb)]
    return out


def check_rule(ins, rep, cls, t, pf, init):
    """None, or what differs between ins and its replacement rep on state init."""
    s1, s2 = run([ins], init), run(rep, init)
    for g in X.GPR:
        if g != t and s1['regs'][g] != s2['regs'][g]:
            return f'{g}: {s1["regs"][g]:#x} != {s2["regs"][g]:#x}'
    if s1['mem'] != s2['mem']:
        return 'memory differs'
    if X.info(ins)[3] == X.NONE and pf:
        return None
    f0 = {k: (init['rax'] >> i) & 1 for i, k in enumerate(X.FLAGS)}
    want = s1['flags'] if cls == 'exact' else f0 if cls == 'free' else {}
    bad = [k for k, v in want.items() if v is not None and s2['flags'][k] != v]
    return f'flags {bad}' if bad else None


def test_rules(trials, seed=1):
    r = random.Random(seed)
    seen, fails = Counter(), []
    for _ in range(trials):
        for ins in instances(r):
            used = X.mentioned(ins)
            t = r.choice([g for g in REGS if not used & X.BIT[g]])
            pf = r.random() < 0.5
            ctx = MP.Ctx('t', r, [], '.Lt_epi', [])
            for name, cls, fn in MP.subst_cands(ctx, ins, [t], pf):
                rep = fn()
                for _ in range(6):
                    msg = check_rule(ins, rep, cls, t, pf, rand_state(r))
                    if msg:
                        fails.append(f'{X.fmt(ins).strip()} -> {name} '
                                     f'{[X.fmt(x).strip() for x in rep]}: {msg}')
                        break
                seen[(ins.m, name)] += 1
    for _ in range(trials * 4):
        a, b = r.sample(REGS, 2)
        ctx = MP.Ctx('t', r, [], '.Lt_epi', [])
        push, pop = X.Ins('push', X.R(a)), X.Ins('pop', X.R(b))
        (_, _, fpush), = MP.subst_cands(ctx, push, [], False)
        (_, _, fpop), = MP.subst_cands(ctx, pop, [], False)
        init = rand_state(r)
        ref = run([push, pop], init)
        for alt in ([*fpush(), pop], [push, *fpop()], [*fpush(), *fpop()]):
            s = run(alt, init)
            if s['regs'] != ref['regs'] or s['flags'] != ref['flags']:
                fails.append(f'push / pop as lea + mov: {[X.fmt(x).strip() for x in alt]}')
        seen[('push', 'push')] += 1
        seen[('pop', 'pop')] += 1
        cc = r.choice(sorted(X.CC_INV))
        jcc = X.Ins('j' + cc, X.L('.Lt_y'))
        (_, _, fj), = MP.subst_cands(ctx, jcc, [], False)

        def prog(js):
            return [X.Ins('cmp', X.R(a), X.R(b))] + js + [
                X.Ins('mov', X.R('rax'), X.I(1)), X.Ins('jmp', X.L('.Lt_e')), X.label('.Lt_y'),
                X.Ins('mov', X.R('rax'), X.I(2)), X.label('.Lt_e')]
        if r.random() < 0.3:
            init[b] = init[a]
        if run(prog([jcc]), init)['regs']['rax'] != run(prog(fj()), init)['regs']['rax']:
            fails.append(f'jcc inversion of j{cc}')
        seen[('j' + cc, 'jcc')] += 1
    return seen, fails


def test_opaque(n, seed=2):
    """Each kind's sequence makes its condition hold (emulated on edge / random values)."""
    r = random.Random(seed)
    seen, fails = Counter(), []
    regs = [g for g in REGS if g != 'rax']
    for _ in range(n):
        t, u, v1, v2 = r.sample(regs, 4)
        if r.random() < 0.2:
            v2 = v1
        kind, seq, cc = MP.opaque_pred(MP.Ctx('o', r, [], '.Lo_epi', []), t, u, v1, v2)
        st = run(seq + [X.Ins('set' + cc, ('r8', 'rax'))], rand_state(r))
        if st['regs']['rax'] & 0xff != 1:
            fails.append(f'{kind}: condition {cc} false after {[X.fmt(x).strip() for x in seq]}')
        seen[kind] += 1
    return seen, fails


def prove_opaque():
    """{kind: how its identity is proved} (for every 64-bit x, y)."""
    import z3
    x, y = z3.BitVecs('x y', 64)
    claims = {'(x|y)-(x&y) == x^y': (x | y) - (x & y) == x ^ y,
              '(x&y)+(x|y) == x+y': (x & y) + (x | y) == x + y,
              '2*x even': (x + x) & 1 == 0, 'x^~x == -1': (x ^ ~x) + 1 == 0, '(x|1) != 0': (x | 1) != 0}
    out = {}
    for k, c in claims.items():
        s = z3.Solver()
        s.set('rlimit', 10_000_000)
        s.add(z3.Not(c))
        out[k] = 'proved by z3' if s.check() == z3.unsat else 'NOT PROVED'
    # the low bits of a product depend only on the low bits of its factors
    ok = all(a * (a + 1) % 2 == 0 for a in range(2))
    out['x*(x+1) even'] = 'proved over x mod 2' if ok else 'FALSE'
    ok = all(a * a % 4 < 2 for a in range(4))
    out['x*x mod 4 < 2'] = 'proved over x mod 4' if ok else 'FALSE'
    ok = all((7 * b * b - 1) % 8 != a * a % 8 for a in range(8) for b in range(8))
    out['7*y*y-1 != x*x'] = 'proved over x, y mod 8' if ok else 'FALSE'
    return out


def test_sabotage():
    """With the opposite condition code in every opaque predicate, the generator's
    emulation check must refuse every function that got an opaque predicate."""
    orig = MP.opaque_pred
    calls = [0]

    def wrong(ctx, t, u, v1, v2):
        calls[0] += 1
        kind, seq, cc = orig(ctx, t, u, v1, v2)
        return kind, seq, X.CC_INV[cc]
    MP.opaque_pred = wrong
    caught = tried = 0
    try:
        for k in (0, 5, 9, 15):
            body, paths, _ = G.draw_program(k, G.SPECS[k])
            for s in G.STRENGTHS:
                before = calls[0]
                try:
                    G.build_function(k, s, G.SPECS[k], body, paths)
                    refused = False
                except (RuntimeError, X.EmuError):
                    refused = True
                if calls[0] > before:
                    tried += 1
                    caught += refused
    finally:
        MP.opaque_pred = orig
    return caught, tried


def test_dead_junk():
    """With one more junk instruction put before a dead instruction in every junk pass
    (as an earlier pass_junk did), the generator's check (every live instruction runs)
    must refuse every function that got one."""
    orig = MP.pass_junk
    added = [0]

    def leaky(ctx, code, density, size):
        out = orig(ctx, code, density, size)
        at = [i for i, x in enumerate(out) if x.tag == 'dead' and out[i - 1].m != 'label']
        if at:
            out.insert(ctx.r.choice(at), MP.dead_op(ctx, ['rax', 'rcx'], False))
            added[0] += 1
        return out
    MP.pass_junk = leaky
    caught = tried = 0
    try:
        for k in (0, 5, 9, 15):
            body, paths, _ = G.draw_program(k, G.SPECS[k])
            for s in G.STRENGTHS:
                before = added[0]
                try:
                    G.build_function(k, s, G.SPECS[k], body, paths)
                    refused = False
                except RuntimeError as e:
                    refused = 'never executed' in str(e)
                if added[0] > before:
                    tried += 1
                    caught += refused
    finally:
        MP.pass_junk = orig
    return caught, tried


def test_programs(n, seed=4):
    """Random programs (z3 witnesses allowed) at the three strengths through the
    generator's own mutation and emulation check."""
    r = random.Random(seed)
    runs, funcs, fails = 0, 0, []
    for k in range(n):
        nargs, nif = r.randint(1, 4), r.randint(0, 3)
        spec = ('test', nargs, r.randint(8, 36), nif, nif >= 2 and r.random() < 0.5, r.random() < 0.3)
        body = P.Gen(r, nargs, spec[5]).program(*spec[2:5])
        paths, _ = P.analyze(body, nargs, r)
        if paths is None:
            continue
        for s in G.STRENGTHS:
            try:
                runs += G.build_function(900 + k, s, spec, body, paths)[2]
                funcs += 1
            except Exception as e:                  # noqa: BLE001
                fails.append(f'program {k} {s}: {type(e).__name__}: {e}')
    return runs, funcs, fails


def rule_names():
    """Rule names written literally in mut_pass (plus the ones built from a mnemonic)."""
    import re
    src = open(os.path.join(HERE, 'mut_pass.py'), encoding='utf-8').read()
    names = set(re.findall("[(][(]'([a-z0-9_]+)', '(?:exact|free|clob)'", src))
    return names | {'mov_sub', 'mov_and', 'push_sub', 'push_and', 'not_sub', 'not_add'}


def main():
    ap = argparse.ArgumentParser(description='Self-test of the mut suite machinery (see the module doc).')
    ap.add_argument('--programs', type=int, default=40, help='random programs (x3 strengths)')
    ap.add_argument('--trials', type=int, default=40, help='rounds of rule instances')
    a = ap.parse_args()
    bad = 0
    seen, fails = test_rules(a.trials)
    names = {n for _, n in seen}
    missing = sorted(rule_names() - names)
    print(f'rules: {len(names)} rule names over {len(seen)} (mnemonic, rule) pairs, {sum(seen.values())} '
          f'replacements checked on 6 states each, {len(fails)} failures; never reached: {missing or "none"}')
    for f in fails[:15]:
        print('  FAIL', f)
    bad += len(fails) + len(missing)
    seen, fails = test_opaque(3000)
    print(f'opaque sequences: {sum(seen.values())} emulated over {len(seen)} kinds, {len(fails)} failures')
    for f in fails[:10]:
        print('  FAIL', f)
    bad += len(fails) + (len(seen) != len(set(MP.OPQ_KINDS)))
    for kind, how in prove_opaque().items():
        print(f'  {kind}: {how}')
        bad += not how.startswith('proved')
    caught, tried = test_sabotage()
    print(f'sabotage (opposite opaque condition): {caught} of {tried} functions refused')
    bad += caught != tried or tried == 0
    caught, tried = test_dead_junk()
    print(f'dead junk (junk put in dead code): {caught} of {tried} functions refused')
    bad += caught != tried or tried == 0
    runs, funcs, fails = test_programs(a.programs)
    print(f'programs: {funcs} mutated functions, {runs} emulated runs, {len(fails)} failures')
    for f in fails[:10]:
        print('  FAIL', f)
    bad += len(fails)
    print('SELFTEST', 'OK' if not bad else 'FAILED')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
