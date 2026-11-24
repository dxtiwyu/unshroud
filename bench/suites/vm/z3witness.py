"""z3witness.py: one z3 witness query, in a process of its own (used by gen_vm.witnesses).

usage: python -I z3witness.py NARGS RLIMIT MEMORY_MB < condition
The condition (bench expression language) comes on stdin; stdout is the json
[status, [x, y, z, w] or null, rlimit used]. Why a process of its own: z3's model depends
on the history of the process that asks (its memory layout): in the generator process the
witnesses changed with unrelated code (an extra import, a garbage-collector threshold), even
with a fresh z3 context per query. Here the history is fixed (gen_vm starts it with a fixed
command line, environment and directory), so the witness depends on the condition only.
The search is bounded by RLIMIT (z3's deterministic operation count, not a wall clock) and
MEMORY_MB, with a 60 s wall-clock timeout as a last resort.
"""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), 'gen'))
import truth                                    # noqa: E402
import z3                                       # noqa: E402


def main():
    nargs, rlimit, mb = (int(a) for a in sys.argv[1:4])
    cond = sys.stdin.read()
    z3.set_param('memory_max_size', mb)
    xs = [z3.BitVec(v, 64) for v in truth.VARS]
    s = z3.Solver()
    s.set('rlimit', rlimit)
    s.set('timeout', 60000)
    s.add(truth.to_z3(cond, xs))
    s.add(*[v == 0 for v in xs[nargs:]])
    a = None
    try:
        res = s.check()
        status = str(res)
        if res == z3.sat:
            m = s.model()
            a = [m.eval(v, model_completion=True).as_long() for v in xs]
    except z3.Z3Exception as e:                 # memory limit
        status = f'unknown ({e})'
    used = next((int(v) for k, v in s.statistics() if k == 'rlimit count'), -1)
    print(json.dumps([status, a, used]))


if __name__ == '__main__':
    main()
