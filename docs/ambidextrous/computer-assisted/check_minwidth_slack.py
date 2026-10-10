"""Bounded rational regressions for MS6, FO and NR11.

Finite arithmetic only. The strict continuum motion, roof-contact, convexity
and asymptotic arguments are hand proofs in companion notes. Run with timeout 5s.
"""
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
from time import perf_counter
import json


def run():
    start = perf_counter()
    checks = 0
    def check(cond, label):
        nonlocal checks
        if not cond:
            raise AssertionError(label)
        checks += 1

    for d in [256, 257, 320, 512, 1024, 10000]:
        s = Q(1, d)
        k = 1-s
        r = Q(3, 4) + s / 4
        b = Q(4, 5) * k
        # D_s^2=2Rs and D_s<1/8, D_s<R/sqrt(2).
        check(2*r*s < Q(1, 64), f'D<1/8 {d}')
        check(2*r*s < r*r/2, f'D<R/sqrt2 {d}')
        # p(t) is negative for t>=pi/4 using sin t>2/3.
        check(1-Q(79,60)*k<0, f'p tail negative {d}')
        # Central 45-degree roof exceeds slab, with rational sqrt2 brackets.
        check(Q(3,4)*Q(5,3)-Q(3,2)*(1-k/4)>s,
              f'middle niche lower {d}')
        # G_s/s > 11k/10 -8D/3 > 3/4 using D<1/8.
        check(Q(11,10)*k-Q(8,3)*Q(1,8)>Q(3,4),
              f'positive correction {d}')
        check(2*Q(8,5)-Q(21,10)==Q(11,10),
              f'stadium face excess {d}')
    # Check directional horizontal thickening core quadratic in AF A.1.
    for c, z in [(Q(3,5),Q(4,5)),(Q(5,13),Q(12,13)),
                 (Q(7,25),Q(24,25)),(Q(8,17),Q(15,17))]:
        check(c*c+z*z==1,'unit circle')
        # v=a*cos; w=a*sin; v'=-a*sin; w'=a*cos.
        a=Q(3,17)
        v,w=a*c,a*z
        vd,wd=-a*z,a*c
        integrand=Q(1,2)*(2*(v*v+w*w)-vd*vd-wd*wd+v*wd-w*vd)
        check(integrand==a*a, 'unpenalized quadratic AF')
        check((vd-w)==-2*a*z and wd+v==2*a*c,
              'contact increment')
    # FO3 algebra, including positive overhang classification.
    for s in [Q(0), Q(1,100), Q(1,8), Q(1,3)]:
        for n_u in [Q(0), Q(1,10), Q(1,4), Q(3,4)]:
            for n_v in [Q(0), Q(1,15), Q(1,3)]:
                for B in [s, (1+s)/2, Q(1)]:
                    for A in [Q(1), (1+s)/2]:
                        if B>A: continue
                        W=Q(5,2)
                        base=min(n_u,B)+min(n_v,1+s-A)-s
                        t=min(n_u,s)+min(n_v,s)-s
                        c=max(Q(0),min(n_u,B)-s)+max(Q(0),min(n_v,1+s-A)-s)
                        check(base==t+c, 'MF2 slab decomposition')
                        check(c>=0, 'nonnegative above-slab')
    return dict(status='rational_regressions_passed',checks=checks,
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                internal_seconds=perf_counter()-start,
                continuum_verified=False,full_turn_optimality_proved=False,
                used_ci_or_lean=False)

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
