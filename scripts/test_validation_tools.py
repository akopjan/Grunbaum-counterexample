#!/usr/bin/env python3
"""Regression-test audit scripts. Test fixtures are not Lean output."""
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


audit = load('audit_source')
gate = load('check_axiom_log')
source = 'def a := "sorry" -- admit\n/- axiom /- sorry -/ -/\ntheorem t : True := by sorry\n'
masked = audit.mask_noncode(source)
assert len(masked) == len(source)
assert masked.count('\n') == source.count('\n')
assert masked.count('sorry') == 1
assert 'axiom' not in masked and 'admit' not in masked
try:
    audit.mask_noncode('/- unterminated')
    raise AssertionError('Unterminated comment accepted')
except ValueError:
    pass
fixture = '\n'.join("'" + n + "' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in gate.EXPECTED)
assert gate.check(fixture) == []
assert gate.check('')
assert gate.check(fixture.replace('Quot.sound', 'sorryAx', 1))
assert gate.check(fixture.replace('Quot.sound', 'inventedAssumption', 1))
no_axiom_fixture = '\n'.join("'" + n + "' does not depend on any axioms" for n in gate.EXPECTED)
assert gate.check(no_axiom_fixture) == []
print('Validation-script regression tests passed using synthetic fixtures.')
print('These tests are not Lean execution or theorem verification.')
