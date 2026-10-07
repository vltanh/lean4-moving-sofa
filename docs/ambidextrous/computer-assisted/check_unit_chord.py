"""Brief exact checks for UC; finite regressions, not continuum verification.

The hand proof is in full-turn-unit-chord-obstruction.md. This program checks
its rational identity and the strict-flank boundary control. Standard library.
"""
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
from time import perf_counter
import argparse
import json
import platform


def run():
    start = perf_counter()
    pairs = bad_right = 0
    for i in range(1, 40):
        for j in range(1, 40):
            r, s = Q(i, 40), Q(j, 40)
            difference = (1-r)/(1+r)+(1-s)/(1+s)-1
            numerator = 1-r-s-3*r*s
            if difference != numerator/((1+r)*(1+s)):
                raise AssertionError('Switching identity')
            if r+s > 1:
                if difference >= 0:
                    raise AssertionError('Incompatible switching conditions')
                bad_right += 1
            pairs += 1
    points = [(Q(-1),Q(0)),(Q(0),Q(0)),(Q(0),Q(1)),(Q(1),Q(1))]
    tests = 0
    for i in range(41):
        r = Q(i,40)
        c, s = (1-r*r)/(1+r*r), 2*r/(1+r*r)
        for sign in (1,-1):
            u, v = (c,sign*s),(-s,sign*c)
            dot = lambda p,n: p[0]*n[0]+p[1]*n[1]
            A, B = max(dot(p,u) for p in points), max(dot(p,v) for p in points)
            if not all(dot(p,u)>=A-1 or dot(p,v)>=B-1 for p in points):
                raise AssertionError('Unit-length flank boundary control')
            tests += 1
    return dict(status='exact_checks_passed', rational_angle_pairs=pairs,
                incompatible_right_conditions=bad_right, boundary_frame_tests=tests,
                arithmetic='Python integers and Fraction',
                internal_seconds=perf_counter()-start, python_version=platform.python_version(),
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                continuum_geometry_verified=False, unrestricted_optimality_proved=False,
                ci_or_lean_used=False)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    text = json.dumps(run(),indent=2)+'\n'
    if args.output: args.output.write_text(text,encoding='utf-8')
    print(text,end='')
