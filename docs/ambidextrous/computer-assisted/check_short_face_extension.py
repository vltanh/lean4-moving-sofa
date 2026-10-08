"""Short exact regressions for SCG/CSF/SW/FAS/FD, not global optimality.

The polynomial identity is checked coefficient by coefficient. Other finite
cases are regressions, not coverage of continuous geometric hypotheses.
Standard library only. Run under an external five-second wall-clock limit.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import itertools
import json
from pathlib import Path
import platform
from time import perf_counter


def add(a: list[Q], b: list[Q]) -> list[Q]:
    out = [Q(0)] * max(len(a), len(b))
    for i, v in enumerate(a): out[i] += v
    for i, v in enumerate(b): out[i] += v
    while len(out) > 1 and not out[-1]: out.pop()
    return out


def mul(a: list[Q], b: list[Q]) -> list[Q]:
    out = [Q(0)] * (len(a)+len(b)-1)
    for i, v in enumerate(a):
        for j, w in enumerate(b): out[i+j] += v*w
    while len(out) > 1 and not out[-1]: out.pop()
    return out


def scaled(a: list[Q], k: Q) -> list[Q]:
    return [k*x for x in a]


def run() -> dict:
    start = perf_counter()
    checks: list[str] = []
    def check(name: str, condition: bool) -> None:
        if not condition: raise AssertionError(name)
        checks.append(name)

    z = Q(149, 500)
    lower_M = 1+4*z*z+z-z**3/3
    width = Q(1001, 500)
    area = Q(41, 25)*(width/2)**2
    check('candidate root lower bracket', 4*z**3+3*z-1 < 0)
    check('scaled width area', area == Q(41082041, 25000000))
    check('strict candidate comparison', lower_M-area == Q(104359, 93750000) > 0)

    x = [-Q(3, 10), Q(1)]
    shift = add(x, [Q(11, 1070)])
    rhs = add(add(scaled(mul(shift, shift), Q(107)),
                  scaled(mul([Q(1), -Q(1)], mul(x, x)), Q(200))),
              [Q(2, 107)])
    expected = list(map(Q, (27, -200, 427, -200)))
    check('FAS sum of squares: all coefficients', rhs == expected)
    check('square root rational bound', Q(169,225)-Q(3,4) == Q(1,900) > 0)
    check('failed clipping width bound', Q(227,200)+Q(13,15) == Q(1201,600))
    check('width gap covers failed clipping', width-Q(1201,600) == Q(1,3000) > 0)

    phase_cases = 0
    witness_cases = 0
    for T in (Q(i,10) for i in range(1,10)):
        c1, s1 = (1-T*T)/(1+T*T), 2*T/(1+T*T)
        if T+2*(1-s1/2)/c1-2 != T*(4*T-T*T-1)/(1-T*T):
            raise AssertionError('FAS flank-width identity')
        for R, m in itertools.product((Q(21,20), Q(6,5), Q(8,5), Q(2), Q(5,2)),
                                      (Q(0),Q(1,4),Q(1,2))):
            if 2*T*R+m*(1-T*T) <= 1+T*T: continue
            for r in (Q(j,20) for j in range(1,20)):
                c, s = (1-r*r)/(1+r*r), 2*r/(1+r*r)
                if max(T*c+s, R*c+m*s) <= 1:
                    raise AssertionError('SCG strip-lemma regression')
                witness_cases += 1
        for k, Y in itertools.product((Q(i,20) for i in range(21)),
                                      (Q(j,20) for j in range(10,21))):
            if k*c1+Y*s1 <= 1 and k*s1 <= Y*c1:
                if k > c1: raise AssertionError('Failed SCG implies short flank')
                phase_cases += 1
    check('rational strip and flank regressions', witness_cases > 0 and phase_cases > 0)

    family_cases = 0
    for m, W, T in itertools.product((Q(0),Q(1,4),Q(1,2)),
                                     (Q(21,10),Q(23,10),Q(12,5)),
                                     (Q(1,3),Q(1,2),Q(9,10))):
        xx = W-2
        H = lambda t: 2*t*(W-1)+m*(1-t*t)-(1+t*t)
        if H(xx) != (1-m)*xx*xx+2*xx-(1-m) or H(Q(1)) != 2*xx:
            raise AssertionError('CSF endpoint polynomial')
        family_cases += 1
    check('central-face polynomial regressions', family_cases == 27)
    check('quarter-height exact threshold', Q(3,4)*Q(1,3)**2+2*Q(1,3)-Q(3,4) == 0)

    # All nondegenerate interval pairs on a quarter-unit grid in [0,3].
    # Integers represent four times each endpoint: u=4 and v=8.
    intervals = list(itertools.combinations(range(13),2))
    categories = {'aligned':0,'top_left':0,'bottom_left':0}
    def inside(x: int, a: int, b: int) -> bool: return a < x < b
    for (a,b),(c,d) in itertools.product(intervals, repeat=2):
        allowed = (not any(inside(x,a,8) or inside(x,4,b) for x in (c,d))
                   and not any(inside(x,c,8) or inside(x,4,d) for x in (a,b)))
        if not allowed: continue
        labels = []
        if a==c and b==d and a<=4 and b>=8: labels.append('aligned')
        if b<=4 and c>=8: labels.append('top_left')
        if d<=4 and a>=8: labels.append('bottom_left')
        if len(labels)!=1: raise AssertionError('Full-turn interval classification')
        categories[labels[0]] += 1
    check('face interval classification', all(categories.values()))
    check('actual short-face example certificate',
          2*Q(9,10)*Q(8,5)+Q(1,2)*(1-Q(9,10)**2)-(1+Q(9,10)**2) == Q(233,200))
    check('actual example width exceeds sqrt five', Q(23,10)**2 > 5)
    check('example elliptic intercept bound', 2*Q(7,10)**2 < 1)
    check('example niche-height bounds', Q(74,100)<Q(87,100)**2 and Q(7,5)**2<2
          and Q(19,20)+Q(87,100)-Q(7,5)<Q(1,2))

    controls = []
    wrong = expected.copy(); wrong[-1] *= -1
    check('wrong polynomial rejected', wrong != rhs)
    controls.append('reversed cubic sign')
    # Using y rather than min(y,1-y) licenses one turn but not the other.
    T,R,y = Q(1,2),Q(11,10),Q(9,10)
    check('one-sided height substitution rejected',
          2*T*R+y*(1-T*T) > 1+T*T and 2*T*R+(1-y)*(1-T*T) < 1+T*T)
    controls.append('unreflected extreme height')
    W, eps = Q(12,5),Q(1,100)
    check('point-face thickening fails floor condition', eps < W+eps-2)
    controls.append('fixed-height point-face horizontal thickening')
    # Replacing retained points by mere convex-hull points is unsound.
    # Stadium h = .5 + .5 sin(t) + .6 cos(t) on the first quarter.
    c,s,k,b = Q(20,101),Q(99,101),Q(3,5),Q(9,20)
    f,g = Q(1,2)+s/2+k*c, Q(1,2)+c/2+k*s
    check('hull-only floor witness is actually forbidden',
          f-1-b*c == Q(2,101)>0 and g-1+b*s == Q(1269,2020)>0)
    controls.append('hull membership substituted for retained material')

    return dict(status='exact_checks_passed', named_checks=len(checks), checks=checks,
                strip_witness_cases=witness_cases, failed_clipping_implication_cases=phase_cases,
                central_polynomial_cases=family_cases,
                interval_pairs_examined=len(intervals)**2,
                classified_interval_pairs=categories, negative_controls=controls,
                scaled_width=str(width), scaled_area_upper=str(area), candidate_lower_bound=str(lower_M),
                arithmetic='Python unbounded integers and Fraction',
                python_version=platform.python_version(), internal_seconds=perf_counter()-start,
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                continuum_proof_verified=False, weighted_value_chain_independently_verified=False,
                unrestricted_optimality_proved=False, ci_or_lean_used=False)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if args.output: args.output.write_text(text,encoding='utf-8')
    print(text,end='')
