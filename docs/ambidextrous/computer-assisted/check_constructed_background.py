"""Bounded rational regressions for PV/RT/CB/FS; not a proof certificate.

The continuum convex-envelope, flux, and motion results are written arguments.
This script checks only displayed algebra and finite instances. Standard library
only; use an external five-second wall-clock limit.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import platform
from time import perf_counter


def bridge_test(a: Q, b: Q, c: Q, s: Q) -> bool:
    if not (0 <= a <= 1 and 0 <= b <= 1 and s > 0 and c*c+s*s == 1):
        raise ValueError('Not normalized two-strip data')
    return b <= a*c or a <= b*c or a*a+b*b-2*c*a*b <= s*s


def run() -> dict:
    start=perf_counter(); checks=[]; rejected=[]
    def check(name: str, value: bool) -> None:
        if not value: raise AssertionError(name)
        checks.append(name)
    depth_cases=0
    for t in (Q(0),Q(1,20),Q(1,2),Q(1),Q(5)):
        for d in (Q(0),Q(1,3),Q(1)):
            for c in (Q(0),Q(2,5),Q(1)):
                if (d+t*c)/(1+t)>1: raise AssertionError('PV depth failed')
                depth_cases+=1
    check('finite rounding depth budgets',depth_cases==45)
    for r in (Q(1,100),Q(1,10),Q(1,2)):
        check('parallel-volume expansion',(1+2*r)**2 == 1+4*r+4*r*r)
    # Exact determinant identity used by the finite-perimeter argument.
    determinant_cases=0
    for a in (-2,0,1):
        for b in (-1,2):
            for c in (0,3):
                for d in (-2,1):
                    r=Q(1,13)
                    if (1+r*a)*(1+r*d)-r*r*b*c != 1+r*(a+d)+r*r*(a*d-b*c):
                        raise AssertionError('Flow determinant')
                    determinant_cases+=1
    check('two-dimensional flow determinant',determinant_cases==24)
    check('reference lower root',4*Q(149,500)**3+3*Q(149,500)-1 < 0)
    check('reference upper root',4*Q(3,10)**3+3*Q(3,10)-1 > 0)
    check('beta lower bound',Q(149,500)-Q(3,10)**3/3==Q(289,1000))
    margin=(4-Q(11,7)+2*Q(289,1000))/Q(3,10)-8+4*Q(289,1000)-Q(22,7)
    check('strict all-template first-order margin',margin==Q(92,2625)>0)
    check('template margin halves',margin/2==Q(46,2625))

    guard_cases=0
    for w in (Q(1001,500),Q(21,10),Q(7,3),Q(3),Q(10)):
        eta=min(Q(1,2),w-2)/(4*(w+1))
        check('guard preserves endpoint signs',(w+1)*eta<min(Q(1,2),w-2))
        check('guard separates inner tails',2*eta<w-2)
        check('guard keeps new corner below half',w*eta<Q(1,4))
        guard_cases+=1
    complement_cases=0
    for density in (Q(0),Q(1,4),Q(1,2)):
        for e in (Q(0),Q(1,10),Q(2)):
            if e>0 and density != Q(1,2): continue
            check('complementary surplus vanishes',e*density-e*(1-density)==0)
            complement_cases+=1

    bridge_cases=sample_cases=accepted=0
    for r in (Q(1,20),Q(1,5),Q(2,5),Q(3,5),Q(4,5)):
        c,s=(1-r*r)/(1+r*r),2*r/(1+r*r)
        for a in (Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)):
            for b in (Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)):
                ok=bridge_test(a,b,c,s);bridge_cases+=1
                if ok: accepted+=1
                for j in range(13):
                    u=r*Q(j,12);ct,st=(1-u*u)/(1+u*u),2*u/(1+u*u)
                    value=a*ct+(b-a*c)*st/s
                    if ok and value>1: raise AssertionError('Bridge upper envelope violated')
                    sample_cases+=1
        check('one thin middle strip: left half',bridge_test(Q(1),c,c,s))
        check('one thin middle strip: right half',bridge_test(c,Q(1),c,s))
        if bridge_test(Q(1),Q(1),c,s):
            raise AssertionError('Two unit widths falsely certify bridge')
    check('finite strip criterion instances',bridge_cases==125 and sample_cases==1625)
    check('strict failure example',not bridge_test(Q(1),Q(1),Q(3,5),Q(4,5)))
    check('boundary tangency accepted',bridge_test(Q(1),Q(3,5),Q(3,5),Q(4,5)))
    check('hypotenuse condition insufficiently applied control',bridge_test(Q(1),Q(0),Q(99,101),Q(20,101)))
    rejected.append('two endpoint widths equal to one are not a safe interval')
    if Q(1,10)*(2*Q(1,4)-1)>=0:raise AssertionError('Wrong CT sign')
    rejected.append('positive defect at density one quarter has adverse surplus')
    if (1+Q(1,10)*Q(11,10))/(1+Q(1,10))<=1:raise AssertionError('Oversized template accepted')
    rejected.append('diameter above one fails the uniform depth budget')
    return dict(status='exact_regressions_passed',named_checks=len(checks),checks=checks,
                depth_cases=depth_cases,determinant_cases=determinant_cases,
                guard_cases=guard_cases,complement_cases=complement_cases,
                two_strip_cases=bridge_cases,accepted_strip_cases=accepted,
                sampled_intermediate_angles=sample_cases,negative_controls=rejected,
                perimeter_margin=str(margin),arithmetic='unbounded integers and Fraction',
                python_version=platform.python_version(),internal_seconds=perf_counter()-start,
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                continuum_background_admission_verified=False,
                arbitrary_partial_turn_completion_verified=False,
                unrestricted_optimality_proved=False,ci_or_lean_used=False)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=json.dumps(run(),indent=2)+'\n'
    if args.output:args.output.write_text(result,encoding='utf-8')
    print(result,end='')
