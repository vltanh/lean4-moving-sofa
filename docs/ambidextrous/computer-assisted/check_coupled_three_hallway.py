"""Exact finite arithmetic regressions for JH's computer-free 1/90 gap.

The continuum proof is in coupled-three-hallway-hand-bound.md.
This checks rational constants and polynomial identities only.
"""
from fractions import Fraction as Q
from hashlib import sha256, sha1
from pathlib import Path
import json
import time

EPS = Q(1, 90)
tests = {}

def check(name, value):
    tests[name] = bool(value)
    if not value:
        raise AssertionError(name)

def run():
    start = time.perf_counter()
    sqrtlo, sqrthi = Q(7071,5000), Q(99,70)
    check("sqrt2_lower", sqrtlo**2 < 2)
    check("sqrt2_upper", sqrthi**2 > 2)
    check("sqrt_eps_upper", Q(53,500)**2 > EPS)
    check("min_width_localization", Q(3,20)**2 > 2*EPS)
    check("initial_square_loss", EPS + 2*Q(53,500) < Q(9,40))
    check("k_lower", (1-Q(29,100))**2 > Q(1,2))
    check("k_upper", (1-Q(3,10))**2 < Q(1,2))
    check("k2_positive", Q(3,2) - sqrthi == Q(3,35))
    check("square_deficit_at_half", Q(1,8)+Q(29,200)-Q(9,200) >= Q(9,40))
    check("square_deficit_parabola_end", -Q(1,10)+Q(29,200)-Q(9,200) >= 0)
    check("excess_curvature_bootstrap", Q(611,25000) > EPS)
    check("c_minus_P_proximity", Q(2,15)**2 > 3*EPS/2)
    check("tip_triangle_area", Q(2,175) > EPS)
    check("positive_wedge", Q(38,7)-Q(53,50)-Q(16,5)>0)
    check("wedge_radius", (Q(6)+Q(53,50))/50<Q(3,20))
    check("wedge_under_unit_y", (Q(13)+Q(53,50)-5*sqrtlo)/7<1)
    check("band_upper", -Q(2,15)+Q(7,10)>Q(1,2))
    check("clipping_budget", Q(3,10)+Q(2,15)-Q(71,1000)<Q(11,30))
    check("dual_weights",sum([700,2,98,686,14])==1500)
    check("final_hand_gap", Q(38,7)**2/1500-Q(11,30)**2/16>EPS)
    check("strict_rational_margin",
          Q(38,7)**2/1500-Q(11,30)**2/16-EPS==Q(467,3528000))

    identities=0
    for x in [Q(-1,11),Q(0),Q(1,13)]:
        for y in [Q(-1,14),Q(0),Q(1,10)]:
            for h in [Q(-1,17),Q(0),Q(1,19)]:
                loss=(h-x)**2+(h-y)**2+x*y
                positive=(x*x+y*y)/2+2*(h-(x+y)/2)**2
                a,b=h-x,h-y
                norm_bound=Q(2,3)*a*a+Q(3,4)*(b+a/3)**2 +(h-(a+b)/2)**2
                assert loss==positive==norm_bound
                identities+=1
    raw=Path(__file__).read_bytes()
    return {
       "status":"exact_rational_checks_passed",
       "inequality_checks":len(tests),
       "polynomial_identity_cases":identities,
       "total_checks":len(tests)+identities,
       "source_sha256":sha256(raw).hexdigest(),
       "source_git_blob_sha":sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest(),
       "seconds":time.perf_counter()-start,
       "finite_tests_prove_continuum":False,
       "global_Romik_optimality_proved":False,
       "ci_or_lean_used":False
    }

if __name__=="__main__":
    print(json.dumps(run(),indent=2))
