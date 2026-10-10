"""Short exact checks for TC/RB/STW, not a global optimality certificate.

All acceptance comparisons use unbounded integers and Fraction. Local line
samples are not asserted to be complete cap realizations. The reference-envelope
coverage and continuum area comparison are supplied by the written proofs.
Run under an external five-second cap. No CI, Lean, network or solver is used.
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


def run() -> dict:
    start = perf_counter()
    checks = []
    def check(name: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(name)
        checks.append(name)

    s_eta, c_eta = Q(20,101), Q(99,101)
    check('rational direction has unit length', s_eta*s_eta+c_eta*c_eta == 1)
    check('window lies below reference beta lower bound', s_eta/c_eta < Q(2,7))
    check('belt thickness', (1-c_eta)/2 == Q(1,101))
    check('paired horizontal tail width', s_eta/2 == Q(10,101))
    check('two inner tail strips are disjoint for m greater than one', 2*Q(10,101)<1)
    check('half-height rectangle retained by belt', Q(1,2)<Q(100,101))
    check('reference companion gap lower bound', (Q(3,2)*c_eta-1)/s_eta == Q(19,8))
    check('maximum outward wall displacement', (1-c_eta)/(2*c_eta) == Q(1,99)<Q(19,8))
    check('modified corner below half height', s_eta+s_eta*s_eta/2 == Q(2220,10201)<Q(1,2))
    check('independent affine-cut slope threshold', Q(3,2)*Q(2,303)==Q(1,101))

    line_cases = 0
    for m,r in itertools.product((Q(1),Q(7,6),Q(4,3)),(Q(1,100),Q(1,50),Q(1,25),Q(1,10))):
        # Here t=pi/2-z and r=tan(z/2); no trigonometric approximation.
        s=(1-r*r)/(1+r*r); c=2*r/(1+r*r); b=m/2; d=c/2
        f=Q(1,2)+b*c+s/2; g=m*s+c/2
        xi,xo=b-d,b+d
        A0=(1+s)/2; n0=(1-s)/2
        if (f-xo*c)/s != A0 or (f-1-xi*c)/s != n0:
            raise AssertionError('Reference circle/line identity')
        companion=(g-1+xi*s)/c
        if companion-n0 != (Q(3,2)*m*s-1)/c:
            raise AssertionError('Reference companion gap identity')
        for u in (Q(0),Q(1,10000),Q(1,1000),Q(1,100),-(1-s)/4,-(1-s)/2):
            first=(f-u-1-xi*c)/s
            outer_line=(f-u-xo*c)/s
            if not first<=companion:
                raise AssertionError('Allowed signed defect lost companion clearance')
            n_test=max(Q(0),first)
            cap_upper=min(Q(1),outer_line)
            if not n0-n_test <= u/s <= A0-cap_upper:
                raise AssertionError('Signed paired-tail comparison')
            line_cases+=1
    check('all signed line comparisons passed',line_cases==72)

    fiber_cases=0
    # Four paired-cell configurations, including outward gains (negative
    # cap losses and niche savings). These check bookkeeping, not cap geometry.
    patterns=[(Q(1,100),Q(1,200)),(Q(0),Q(0)),
              (-Q(1,100),-Q(1,50)),(Q(1,50),Q(1,50))]
    A0,n0=Q(9,10),Q(1,10)
    for (cu,gu),(cv,gv),fu,fv in itertools.product(patterns,patterns,(Q(0),Q(1,20),Q(1,4)),(Q(0),Q(1,20),Q(1,4))):
        # cu,cv: outer cap losses; gu,gv: paired inner niche savings.
        au,av=A0-cu,A0-cv
        nu,nv=n0-gu,n0-gv
        Ai,Vi=1-fu,1-fv
        if not (au>=Q(1,2) and av>=Q(1,2) and Ai>=Q(1,2) and Vi>=Q(1,2)
                and 0<=nu<=Q(1,2) and 0<=nv<=Q(1,2)):
            raise AssertionError('Fixture outside nonempty-fiber hypotheses')
        clipping=min(nu,fv)+min(nv,fu)
        delta_u=fu+cu-gu;delta_v=fv+cv-gv
        actual=(au+av-1)+(min(Ai,1-nv)-max(nu,1-Vi))
        reference=(2*A0-1)+(1-2*n0)
        if reference-actual != delta_u+delta_v-clipping or not clipping<=delta_u+delta_v:
            raise AssertionError('Clipping-budget identity')
        fiber_cases+=1
    check('all paired-fiber identities passed',fiber_cases==144)

    controls=[]
    # A support decrease lowers the first inner-wall height, not raises it.
    if Q(1,10)-(Q(1,10)-Q(1,100)) <= -Q(1,100):
        raise AssertionError('Reversed support-defect sign accepted')
    controls.append('reversed support-defect sign rejected')
    # Inequalities alone with an unpaired niche saving do not pay clipping.
    if Q(1,20) <= Q(1,20)-Q(1,10):
        raise AssertionError('Unpaid niche saving accepted')
    controls.append('unpaid niche saving rejected')
    au=av=Q(1,4);nu=nv=Q(0)
    raw=min(au,1-nv)-max(nu,1-av)
    if max(Q(0),raw)==raw:
        raise AssertionError('Empty-fiber positive-part correction omitted')
    controls.append('empty-fiber identity without its hypothesis rejected')

    return dict(status='exact_regressions_passed',named_checks=len(checks),checks=checks,
                signed_line_cases=line_cases,paired_fiber_cases=fiber_cases,negative_controls=controls,
                arithmetic='Python unbounded integers and Fraction',python_version=platform.python_version(),
                internal_seconds=perf_counter()-start,source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                continuum_proof_verified_by_script=False,local_lines_claimed_as_cap_realizations=False,
                unrestricted_optimality_proved=False,ci_or_lean_used=False)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
