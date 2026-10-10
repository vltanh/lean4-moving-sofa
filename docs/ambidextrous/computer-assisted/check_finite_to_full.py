"""Exact finite regressions of FR's rational normal-distance and strip bounds.
Not a global optimum solver and not a continuum-motion certificate.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from hashlib import sha256,sha1
from time import perf_counter
import json

def normal(r):
    return ((1-r*r)/(1+r*r),2*r/(1+r*r))

def run():
    st=perf_counter();normal_checks=0;point_checks=0
    for n in (2,4,8,16):
        for k in range(4*n+1):
            r=Q(k,4*n)
            j=min(range(n+1), key=lambda j:abs(r-Q(j,n)))
            q=Q(j,n);a,b=normal(r),normal(q)
            distance2=sum((a[i]-b[i])**2 for i in (0,1))
            assert distance2==4*(r-q)**2/((1+r*r)*(1+q*q))
            assert distance2<=Q(1,n*n)
            assert (1+Q(6,n))*Q(n,n+6)==1
            normal_checks+=1
    for H in (Q(1,4),Q(1,2),Q(3,4),Q(1)):
        # Rational one-frame extreme-point projection bounds.
        right=(1+Q(4,5)*H)/Q(3,5)
        left=(1+Q(3,5)*H)/Q(4,5)
        assert right<=3 and left<=2 and right+left<=5
        for dx,dy in product([Q(-5),Q(-2),Q(0),Q(2),Q(5)],[-H,Q(0),H]):
            assert dx*dx+dy*dy<=26<36
            point_checks+=1
    # The finite-to-continuous estimate has a positive allowance; it is not zero.
    # This checks only the displayed bound, not a violating geometric example.
    assert (1+Q(6,4))>1
    src=Path(__file__).read_bytes()
    return dict(status='exact_regressions_passed',normal_checks=normal_checks,
                diameter_point_checks=point_checks,finite_optimum_computed=False,
                continuum_verified_by_code=False,full_turn_optimality_proved=False,
                source_sha256=sha256(src).hexdigest(),
                source_git_blob_sha=sha1(b'blob '+str(len(src)).encode()+b'\0'+src).hexdigest(),
                internal_seconds=perf_counter()-st)
if __name__=='__main__':print(json.dumps(run(),indent=2))
