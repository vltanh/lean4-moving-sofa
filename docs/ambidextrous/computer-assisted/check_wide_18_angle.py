"""Exact-rational extension of the anchor-area upper sum to eighteen rational angles.

For W exactly 2sqrt2 the geometric envelope is derived in EXW.
For W >= 2sqrt2 - 1e-7, the uniform perturbation allowance
is derived from the two-handed switching estimate EW.
This script certifies only the finite rational arithmetic: the
geometric reduction is the mathematical content of the accompanying note.
"""
from fractions import Fraction as F
import json

ROOT_LO = F(1414213562, 10**9)
ROOT_HI = F(1414213563, 10**9)
assert ROOT_LO * ROOT_LO < 2 < ROOT_HI * ROOT_HI
WIDTH_LO = 2 * ROOT_LO
TRIPLES = ((3,4,5),(5,12,13),(8,15,17),(20,21,29),
           (28,45,53),(33,56,65),(48,55,73),(65,72,97),
           (60,91,109))
N = 1024
LIP = F(12,5)
GAP = F(1,10**7)
PAD = F(31,3000)
assert GAP < F(1,3000)**2
assert 30*F(1,3000) + LIP*GAP < PAD
angles=[]
for a,b,h in TRIPLES:
    assert a*a+b*b==h*h
    for c,s in ((F(a,h),F(b,h)),(F(b,h),F(a,h))):
        assert c*c+s*s==1
        assert max(c/s,s/c)<=LIP
        angles.append((c,s))
assert len(angles)==18

def rplus(x):
    branches=[F(1,2),x,ROOT_HI-x]
    for c,s in angles:
        branches.append(max((1-(WIDTH_LO-x)*c)/s,(1-x*s)/c))
    return max(F(0),min(branches))

def check():
    dx=ROOT_HI/N
    middle_sum=sum((rplus(dx*F(2*i+1,2)) for i in range(N)),F(0))
    checked_midpoint=4*dx*middle_sum
    lipschitz_error=2*LIP*ROOT_HI*dx
    maxwidth_upper=checked_midpoint+lipschitz_error
    wide_upper=maxwidth_upper+4*ROOT_HI*PAD
    assert maxwidth_upper < F(8,5)
    assert wide_upper < F(41,25)
    print(json.dumps({
        'status':'exact_18_angle_area_upper_passed',
        'triples':TRIPLES, 'direction_count':len(angles),
        'cells':N, 'root_lower':str(ROOT_LO),'root_upper':str(ROOT_HI),
        'slope_upper':str(LIP),
        'certified_midpoint_sum':str(checked_midpoint),
        'lipschitz_error':str(lipschitz_error),
        'extreme_width_area_bound_exact':str(maxwidth_upper),
        'extreme_width_area_bound_decimal':float(maxwidth_upper),
        'exclusion_window_width':str(GAP),
        'robust_radial_pad':str(PAD),
        'max_area_on_window_exact':str(wide_upper),
        'max_area_on_window_decimal':float(wide_upper),
        'gap_below_41_25_exact':str(F(41,25)-wide_upper),
        'global_sharp_optimality_proved':False,
        'lean_or_ci_run':False,
        },indent=2))
if __name__=='__main__':check()
