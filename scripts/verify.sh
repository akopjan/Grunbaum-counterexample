#!/bin/sh
# No installation is performed. Every failure is reported, never suppressed.
set -u
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$ROOT" || exit 1
mkdir -p validation
python3 scripts/audit_source.py --strict > validation/source_audit.log 2>&1
audit_rc=$?

lake build > validation/lake_build.log 2>&1
build_rc=$?

grep -RInE '\bsorry\b|\baxiom\b|\badmit\b' SoberonConvexBody Solution.lean > validation/gaps.log 2>&1
grep_rc=$?

core_rc=125
centered_rc=125
tensor_rc=125
analytic_rc=125
main_rc=125
grunbaum_rc=125
axioms_rc=125
if [ "$build_rc" -eq 0 ]; then
  lake env lean checks/Core.lean > validation/core_axioms.log 2>&1
  core_rc=$?
  lake env lean checks/Centered.lean > validation/centered_axioms.log 2>&1
  centered_rc=$?
  lake env lean checks/Main.lean > validation/main_axioms.log 2>&1
  main_rc=$?
  lake env lean checks/Grunbaum.lean > validation/grunbaum_axioms.log 2>&1
  grunbaum_rc=$?
  lake env lean checks/Tensor.lean > validation/tensor_axioms.log 2>&1
  tensor_rc=$?
  lake env lean checks/Analytic.lean > validation/analytic_axioms.log 2>&1
  analytic_rc=$?
  if [ "$tensor_rc" -eq 0 ] && [ "$analytic_rc" -eq 0 ] && [ "$core_rc" -eq 0 ] && [ "$centered_rc" -eq 0 ] && [ "$main_rc" -eq 0 ] && [ "$grunbaum_rc" -eq 0 ]; then
    cat validation/core_axioms.log validation/centered_axioms.log validation/main_axioms.log validation/grunbaum_axioms.log validation/tensor_axioms.log validation/analytic_axioms.log > validation/all_axioms.log
    python3 scripts/check_axiom_log.py validation/all_axioms.log > validation/axiom_gate.log 2>&1
    axioms_rc=$?
  fi
else
  for target in core centered tensor analytic main grunbaum; do
    printf 'NOT RUN: lake build failed; there is no axiom report.\n' > "validation/${target}_axioms.log"
  done
fi

export audit_rc build_rc grep_rc core_rc centered_rc tensor_rc analytic_rc main_rc grunbaum_rc axioms_rc
python3 - <<'PY'
import json
import os
from pathlib import Path
keys = ['audit_rc', 'build_rc', 'grep_rc', 'core_rc', 'centered_rc', 'tensor_rc', 'analytic_rc', 'main_rc', 'grunbaum_rc', 'axioms_rc']
result = {k: int(os.environ[k]) for k in keys}
result['fully_verified'] = all(result[k] == 0 for k in keys if k != 'grep_rc') and result['grep_rc'] == 1
result['exit_125_means'] = 'not run because a prerequisite failed'
Path('validation/verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
PY

if [ "$audit_rc" -eq 0 ] && [ "$build_rc" -eq 0 ] && [ "$grep_rc" -eq 1 ] && [ "$core_rc" -eq 0 ] && [ "$centered_rc" -eq 0 ] && [ "$tensor_rc" -eq 0 ] && [ "$analytic_rc" -eq 0 ] && [ "$main_rc" -eq 0 ] && [ "$grunbaum_rc" -eq 0 ] && [ "$axioms_rc" -eq 0 ]; then
  printf 'PASS: build, gap scan, and standard-axiom gate.\n'
  exit 0
fi
printf 'FAIL: this snapshot is not fully verified. See validation/.\n'
exit 1
