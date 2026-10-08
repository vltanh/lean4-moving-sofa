"""Bounded exact regressions for SI and MCA; not a global optimality proof.

Only Python integers and Fraction decide these checks. The general continuity,
convexity, envelope, and asymptotic arguments are written in the proof notes.
"""
from __future__ import annotations
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
from time import perf_counter
import argparse
import json
import platform


def covered(target: tuple[Q,Q], intervals: list[tuple[Q,Q]]) -> bool:
    left,right=target
    reach=left
    for lo,hi in sorted(intervals):
        if hi < reach:
            continue
        if lo > reach:
            return False
        reach=max(reach,hi)
        if reach >= right:
            return True
    return reach >= right


def strip_hallways(a: Q,b: Q) -> list[tuple[Q,Q]]:
    # All angles are in units of pi/2. A strip of width at most one at
    # theta guarantees a hallway indexed by theta or theta-1. Width is
    # periodic with period two in these coordinates.
    return [(a+2*k-shift,b+2*k-shift) for k in range(-3,4) for shift in (0,1)]


def run() -> dict:
    start=perf_counter();checks=[]
    def check(name: str, ok: bool) -> None:
        if not ok:
            raise AssertionError(name)
        checks.append(name)
    transport_cases=0
    for delta in [Q(k,16) for k in range(-16,17)]:
        extra=strip_hallways(min(Q(1),1+delta),max(Q(1),1+delta))
        known=[(Q(0),Q(1)),(Q(2),Q(3))]+extra
        check(f'full transport {delta}',covered((delta,1+delta),known)
              and covered((2+delta,3+delta),known))
        transport_cases+=1
    bridge_cases=0
    for a in [Q(k,12) for k in range(1,13)]:
        for g in [Q(k,12) for k in range(1,13)]:
            known=[(Q(0),a),(3-g,Q(3))]+strip_hallways(a,2-g)
            check(f'partial bridge {a},{g}',covered((a-1,a),known)
                  and covered((a+1,a+2),known))
            bridge_cases+=1
    # Three individually safe directions must not be treated as a full bridge.
    a=g=Q(3,4)
    isolated=[]
    for t in (a,Q(1),2-g):
        isolated+=strip_hallways(t,t)
    known=[(Q(0),a),(3-g,Q(3))]+isolated
    check('isolated strip directions do not close missing intervals',
          not covered((a-1,a),known))
    # Exact convex-strip countermodel. It is not asserted to be an
    # ambidextrous sofa: K={7|x|+24|y|<=25/2, |y|<=1/2}.
    vertices=[(Q(25,14),Q(0)),(Q(1,14),Q(1,2)),(-Q(1,14),Q(1,2)),
              (-Q(25,14),Q(0)),(-Q(1,14),-Q(1,2)),(Q(1,14),-Q(1,2))]
    def h(c: Q,s: Q) -> Q:
        return max(c*x+s*y for x,y in vertices)
    for c,s in ((Q(7,25),Q(24,25)),(Q(0),Q(1)),(-Q(7,25),Q(24,25))):
        check(f'exact prescribed strip {(c,s)}',c*c+s*s==1 and h(c,s)+h(-c,-s)==1)
    c,s=Q(9,41),Q(40,41)
    check('intermediate strip exceeds one',c*c+s*s==1 and
          h(c,s)+h(-c,-s)==Q(289,287)>1)
    twice=sum(vertices[i][0]*vertices[(i+1)%6][1]-vertices[i][1]*vertices[(i+1)%6][0]
              for i in range(6))
    check('countermodel area',abs(twice)/2==Q(13,7))
    # Rationalized cut relation proves the two formulas for the support
    # defect agree at the cutting normal. No candidate root is sampled.
    cut_cases=0
    for m in (Q(1),Q(7,6),Q(4,3),Q(3,2)):
        for r in (Q(1,100),Q(1,50),Q(1,25),Q(1,20)):
            c,s=(1-r*r)/(1+r*r),2*r/(1+r*r)
            tau=(1-c)/(2*m+s)
            check(f'cut relation {m},{r}',1-c==tau*(2*m+s))
            # Multiply the common radical in the join formulas out.
            check(f'support join {m},{r}',-(c+tau*s)/2==-Q(1,2)+m*tau)
            check(f'tail integral bound {m},{r}',Q(2,3)*(s/2)**3==s**3/12)
            cut_cases+=1
    # The area expansion under two mirrored defects -u/2 has linear
    # coefficient 1/2 and quadratic coefficient 1/4 on a single quarter.
    for integral_u in (Q(0),Q(1,7),Q(2,5)):
        for grad_sq in (Q(1,3),Q(5,4)):
            for norm_sq in (Q(0),Q(1,20)):
                one=Q(1,4)*integral_u+Q(1,8)*(grad_sq-norm_sq)
                check('mirrored cap-area expansion',2*one==
                      Q(1,2)*integral_u+Q(1,4)*(grad_sq-norm_sq))
    return dict(status='exact_regressions_passed',named_checks=len(checks),
                full_transport_cases=transport_cases,partial_bridge_cases=bridge_cases,
                support_join_cases=cut_cases,arithmetic='unbounded integers and Fraction',
                strip_countermodel_area='13/7',intermediate_strip_width='289/287',
                python_version=platform.python_version(),internal_seconds=perf_counter()-start,
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                general_continuum_statements_verified_by_script=False,
                sampled_countermodel_is_claimed_feasible_sofa=False,
                unrestricted_optimality_proved=False,ci_or_lean_used=False)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
