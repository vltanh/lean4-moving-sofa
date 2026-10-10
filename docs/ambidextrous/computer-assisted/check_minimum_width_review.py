"""Exact regressions for the minimum-width slack identity and SM.4.

These checks do not verify continuum feasibility or full-turn optimality.
The supplied package replay, if provided, is diagnostic floating-point data.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from math import atan, sqrt
from pathlib import Path
import platform
from time import perf_counter


def run(replay: Path | None = None) -> dict:
    start = perf_counter()
    fibers = positive = negative = 0
    for s in (Q(0), Q(1, 100), Q(1, 4), Q(3, 4)):
        for i in range(7):
            A = s + (1-s)*Q(i, 6)
            for j in range(7):
                B = s + (A-s)*Q(j, 6)
                for p in range(5):
                    nU = A*Q(p, 4)
                    low = max(B, nU)
                    for q in range(5):
                        nV = (1+s-low)*Q(q, 4)
                        ell = min(A, 1+s-nV)-low
                        psi_sum = A+(1+s-B)-nU-nV-1
                        correction = min(nU,B)+min(nV,1+s-A)-s
                        subs = min(nU,s)+min(nV,s)
                        clip = max(min(nU,B)-s,0)+max(min(nV,1+s-A)-s,0)
                        assert ell >= 0
                        assert ell == psi_sum+correction
                        assert correction == subs+clip-s
                        fibers += 1
                        positive += correction > 0
                        negative += correction < 0
    assert fibers == 4900 and positive > 0 and negative > 0

    circles = 0
    for i in range(33):
        x=Q(i,256)  # 0 <= sqrt(s) <= 1/8
        s=x*x; k=1-s; R=(1+s)/2
        assert s <= Q(1,64)
        assert R*R-s == k*k/4
        sn,cs=2*x/(1+x*x),(1-x*x)/(1+x*x)
        assert sn*sn+cs*cs==1 and cs>0
        assert R*sn==x and R*cs==k/2
        lower=(1+x*x)**2*(x-x**3/3)-(1-x*x)*x
        expected=Q(8,3)*x**3+Q(1,3)*x**5*(1-x*x)
        assert lower==expected and lower>=Q(8,3)*x**3
        circles+=1
    assert Q(4,53)>Q(1,16)  # 2/sqrt(53) > 1/4
    assert Q(63,64)*Q(10,9)==Q(35,32)>Q(1,4)

    # Wrongly charging two slabs after summing the cap penalties is rejected.
    s=Q(1,4); A=Q(1); B=s; nU=nV=Q(0)
    ell=min(A,1+s-nV)-max(B,nU)
    psi_sum=A+1+s-B-nU-nV-1
    assert ell != psi_sum+min(nU,B)+min(nV,1+s-A)-2*s

    rows=[]
    if replay is not None:
        rec=json.loads(replay.read_text())
        for item in rec['part_b']['hard_family']:
            s=item['s']
            if not 0<s<=1/64:
                continue
            gamma=(1+s)**2*atan(sqrt(s))-(1-s)*sqrt(s)
            rows.append({'s':s,'Gamma':gamma,'eight_thirds_s_3_2':8*s**1.5/3,
                         'replayed_minus_G_s':-item['G_s'],
                         'replayed_area_deficit':item['M_minus_E'],
                         'minus_G_minus_Gamma':-item['G_s']-gamma,
                         'scope':'floating-point diagnostic; no certified error sign'})
    return {'status':'exact_arithmetic_regressions_passed','fiber_cases':fibers,
            'positive_correction_cases':positive,'negative_correction_cases':negative,
            'circle_and_series_cases':circles,
            'negative_controls':['wrong double-slab subtraction rejected',
                                 'G_s is not sign-definite on compatible scalar fibers'],
            'floating_point_replay_comparison':rows,
            'python':platform.python_version(),'internal_seconds':perf_counter()-start,
            'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'continuum_geometry_verified_by_script':False,
            'unrestricted_optimality_proved':False,'ci_or_lean_used':False}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--replay',type=Path)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    text=json.dumps(run(args.replay),indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')
