#!/bin/sh
# unshroud self-checks (Git Bash on Windows). Every check uses only files of this repository.
#   ./test.sh [quick]      quick: unit tests and the CPU comparisons only (about a minute)
cd "$(dirname "$0")" || exit 1
B=build
export UNSHROUD_MEM_MB=${UNSHROUD_MEM_MB:-3000}
fails=0
ok() { if [ "$1" = 0 ]; then echo "ok    $2"; else echo "FAIL  $2"; fails=$((fails + 1)); fi; }
# expression rules, simplifier, modular reasoning, self-modifying code, native execution
o=$($B/t_expr.exe 2>&1 | tail -1); echo "$o" | grep -q "^ok"; ok $? "t_expr: $o"
o=$($B/t_simp.exe 150 2>&1 | tail -1); echo "$o" | grep -q "^ok: 0 wrong"; ok $? "t_simp: $o"
o=$($B/t_mod.exe 300 2>&1 | tail -1); echo "$o" | grep -q "^ok: 0 wrong"; ok $? "t_mod: $o"
o=$($B/t_smc.exe 2>&1 | tail -1); echo "$o" | grep -q "^ok: .* 0 failed"; ok $? "t_smc: $o"
o=$($B/t_native.exe 2>&1 | tail -1); echo "$o" | grep -q "^ok: .* 0 failed"; ok $? "t_native: $o"
# every instruction form of these PEs: unshroud against this CPU, concrete and symbolic
for d in bench/suites/mba/mba.dll bench/suites/vm/vm.dll bench/suites/mut/mut.dll bench/suites/opaque/opaque.dll bench/exc/exc_msvc.dll; do
  o=$($B/t_diff.exe $d --trials 40 2>&1 | tail -1); echo "$o" | grep -q ": 0 forms differ from the CPU, 0 forms with symbolic"; ok $? "t_diff $(basename $d): $o"
done
[ "$1" = quick ] && { echo "$fails failed"; exit $fails; }
# Windows exception dispatch and trap / anti-debug instructions against the native run of the same DLL
for d in bench/exc/exc_clang.dll bench/exc/exc_msvc.dll; do
  o=$(python -I py/exc_check.py $d --explore 0 2>&1 | grep "results compared" | tail -1); echo "$o" | grep -q ", 0 differ"; ok $? "exc_check: $o"
done
# a few trap results are machine values (smsw, lsl of selector 0x53): up to 2 may differ
o=$(python -I py/trap_check.py bench/exc/trap_clang.dll 2>&1 | grep "results compared" | tail -1)
n=$(echo "$o" | sed -n 's/.*, \([0-9]*\) differ.*/\1/p'); [ -n "$n" ] && [ "$n" -le 2 ]; ok $? "trap_check: $o"
# the four benchmark suites against their ground truth
for s in mba opaque vm mut; do
  if [ $s = mba ]; then ex="--no-addr"; else ex="--paths"; fi
  l=$(python -I py/bench_unshroud.py bench/suites/$s/$s.json --jobs 4 --exe $B/unshroud_explore.exe "--extra=$ex" 2>&1 | grep -E "^suite|^all " | paste - - | tail -1)
  echo "$l" | grep -q "all paths reached 100.0%  all outputs resolved 100.0%.*wrong 0 "; ok $? "suite $s: $(echo "$l" | sed -e 's/.*functions *[0-9]* *//' | cut -c1-160)"
done
echo "$fails failed"; exit $fails
