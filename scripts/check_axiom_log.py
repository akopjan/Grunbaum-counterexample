#!/usr/bin/env python3
"""Check actual #print axioms output for the named declarations; fail closed."""
from __future__ import annotations
import argparse
import re
from pathlib import Path

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED = {
    'SoberonConvexBody.Tensors.zero_can_be_reframed_to_standard',
    'SoberonConvexBody.Tensors.obstruction_ne_zero_near_standard',
    'SoberonConvexBody.Tensors.exists_tau_obstruction_nonzero',
    'SoberonConvexBody.low_walsh_localization_robust',
    'SoberonConvexBody.ball_high_quadratic_flatness',
    'SoberonConvexBody.radial_shell_stability',
    'SoberonConvexBody.Tensors.signAverage4_high123',
    'SoberonConvexBody.Tensors.signAverage4_high0123',
    'SoberonConvexBody.SphereGeometry.coordinateMoment_pos',
    'SoberonConvexBody.SphereGeometry.sphereMap_measurePreserving',
    'SoberonConvexBody.SphereGeometry.integral_centered_polynomial_high123',
    'SoberonConvexBody.SphereGeometry.integral_centered_polynomial_high0123',
    'SoberonConvexBody.radial_integral_formula',
    'SoberonConvexBody.highScale_pos',
    'SoberonConvexBody.highWalsh_centered_onFrame',
    'SoberonConvexBody.exists_convex_body_counterexample',
}


def check(text: str) -> list[str]:
    pattern = re.compile(
        r"['`]?([A-Za-z_][A-Za-z0-9_.]*)['`]?\s+"
        r"(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        re.S,
    )
    reports: dict[str, set[str]] = {}
    for name, axioms in pattern.findall(text):
        reports.setdefault(name, set()).update(
            x.strip() for x in axioms.replace('\n', ' ').split(',') if x.strip()
        )
    problems = []
    for name in sorted(EXPECTED - reports.keys()):
        problems.append('missing axiom report: ' + name)
    for name, axioms in sorted(reports.items()):
        bad = axioms - ALLOWED
        if bad:
            problems.append(name + ': nonstandard axioms: ' + ', '.join(sorted(bad)))
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    args = parser.parse_args()
    problems = check(args.log.read_text(encoding='utf-8'))
    if problems:
        for problem in problems:
            print('FAIL:', problem)
        return 1
    print(f'All {len(EXPECTED)} requested axiom reports contain only standard axioms.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
