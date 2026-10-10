"""Short, exact rational arithmetic checks for JD1's computer-free 1/51 gap.

The all-body geometry, motion-angle reach and disjoint missing-area arguments
are hand proofs in two-sided-clipping-dual-hand-bound.md, not consequences
of the finite tests in this file.
"""
from fractions import Fraction as Q
from hashlib import sha1, sha256
from pathlib import Path
from time import perf_counter
import json

def run():
    t0=perf_counter()
    E=Q(1,51)
    low,up=Q(7071,5000),Q(99,70)
    tests={}
    def test(label,cond):
        assert cond,label
        tests[label]=True
    test("lower_sqrt2",low*low<2)
    test("upper_sqrt2",up*up>2)
    test("upper_sqrt_epsilon",Q(141,1000)**2>E)
    test("min_width_loss",Q(2)-up > Q(1,2))
    test("t_smaller_than_one_fifth",2*E<Q(1,5)**2)
    test("outer_square_deficit",Q(49,200)+Q(7,10)*Q(29,100)-Q(9,200)==Q(403,1000))
    test("alpha_below_outer_deficit",E+2*Q(141,1000)<Q(403,1000))
    test("square_deficit_parabola_first",Q(1,5)*Q(29,100)**2>0)
    test("square_deficit_parabola_last",-Q(3,10)*Q(7,10)**2+Q(29,100)*Q(7,10)-Q(1,2)*Q(3,10)**2>0)
    test("k_squared_above_epsilon",Q(29,100)**2>E)
    test("large_center_loss",Q(4,5)*Q(29,100)**2-Q(3,10)*Q(1,5)+Q(11,16)*Q(1,5)**2==Q(1739,50000))
    test("large_center_loss_gt_epsilon",Q(1739,50000)>E)
    test("normal_center_bound",Q(43,250)**2>Q(3,2)*E)
    test("tips_inside_strip",Q(21,40)+Q(43,250)<low/2)
    test("two_tip_area",Q(21,40)**2/14==Q(63,3200))
    test("tip_area_strict",Q(63,3200)>E)
    test("N_upper_r_bound", (Q(6)+Q(141,100))/50 < Q(3,20))
    test("lower_wedge_inside_square",Q(2)-Q(1,5)-1>Q(21,40))
    test("upper_band_covers_wedge",-Q(43,250)+low/2 > Q(3,20))
    test("C_greater_38_7",Q(62)-40*up>=Q(38,7))
    test("eta_positive",5*low-7==Q(71,1000))
    test("quadratic_dual_denominator",sum([700,2,98,686,14])==1500)
    test("Delta_dual_norm", Q(1,2)+Q(1,2)+14+Q(1,2)==Q(31,2)<16)
    test("Theta_dual_norm",2+98+14==114)
    test("Delta_at_dual_point_negative",53*Q(38,7)/750>Q(3,10))
    test("Theta_at_dual_point_below_negative_29_20",19*Q(38,7)/250+(5*low-6)>Q(29,20))
    test("Delta_positive_part_bound",Q(293,1000)+Q(43,250)-Q(71,1000)<Q(2,5))
    test("Theta_positive_part_bound",Q(141,100)-(5*low-6)<Q(17,50))
    test("N_nonpositive_case",Q(38,7)**2/800>E)
    test("Theta_nonpositive_case",Q(38,7)**2/1500>E)
    severe=Q(38,7)**2/1500+Q(841,45600)-Q(2,5)**2/16-Q(17,50)**2/14
    test("Theta_positive_case_exact",severe==Q(1107821,55860000))
    test("Theta_positive_case_margin_exact",severe-E==Q(212957,949620000))
    test("Theta_positive_case_gt_epsilon",severe>E)
    tests_n=len(tests)
    identities=0
    C=Q(109,20) # arbitrary rational parameter for testing the variance identity
    zstar=(Q(7,15)*C,C/750,-Q(7,750)*C,Q(49,750)*C,Q(7,750)*C,Q(0))
    for N in (Q(1),Q(2),Q(3)):
      for x in (Q(-1,7),Q(1,11)):
       for y in (Q(-1,5),Q(1,13)):
        for sa in (Q(0),Q(1,3)):
         sd=C-N-x+7*y-7*sa
         for omega in (Q(0),Q(1,9)):
          z=(N,x,y,sa,sd,omega)
          Q0=N*N/700+(x*x+y*y)/2+(sa*sa+sd*sd)/14+2*omega*omega
          excess=((z[0]-zstar[0])**2/700+
                  ((z[1]-zstar[1])**2+(z[2]-zstar[2])**2)/2+
                  ((z[3]-zstar[3])**2+(z[4]-zstar[4])**2)/14+
                  2*(z[5]-zstar[5])**2)
          assert Q0==C*C/1500+excess
          # Area stability: B-|F| is the same quadratic under both parameterizations.
          h=Q(1,15)
          lhs=(h-x)**2+(h-y)**2+x*y
          rhs=(x*x+y*y)/2+2*(h-(x+y)/2)**2
          assert lhs==rhs
          identities+=2
    raw=Path(__file__).read_bytes()
    return dict(status="exact_rational_checks_passed",
                inequality_checks=tests_n,
                polynomial_identity_checks=identities,
                total_checks=tests_n+identities,
                final_computer_free_bound="2*sqrt(2)-1-1/51",
                rational_severe_margin=str(severe-E),
                seconds=round(perf_counter()-t0,6),
                source_sha256=sha256(raw).hexdigest(),
                source_git_blob_sha=sha1(b"blob "+str(len(raw)).encode()+b"\x00"+raw).hexdigest(),
                continuum_proof_verified_by_script=False,
                Romik_sharp_optimality_proved=False,
                used_CI_Lean_or_large_optimization=False)

if __name__=="__main__":
    print(json.dumps(run(),indent=2))
