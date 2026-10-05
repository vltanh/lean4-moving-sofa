"""Exact scalar certificates for branch comparisons, NOT a global transition.

All proof operations use integers and rational/dyadic intervals. The roots
compare an explicit forward lower bound or a forward upper bound with V;
neither root is asserted to be the true forward/reverse crossing.
"""
from __future__ import annotations
from fractions import Fraction
from math import factorial
import json
import argparse
from parameter_certificate import BITS, SCALE, Interval, pi_interval, sin_cos
from width_certificate import sinc
from extended_width_certificate import stable_parameters


def sinc_derivative(e: Interval) -> Interval:
    if max(abs(e.lo),abs(e.hi))>4*SCALE:
        raise ValueError("sinc derivative argument outside [-4,4]")
    if Fraction(74*4**73,factorial(75))>=Fraction(1,SCALE):
        raise ArithmeticError("sinc derivative remainder too large")
    n=36
    ee=e.square()
    p=Interval.rational((-1)**n*2*n,factorial(2*n+1))
    for j in range(n-1,0,-1):
        p=p*ee+Interval.rational((-1)**j*2*j,factorial(2*j+1))
    return e*p+Interval(-1,1)


def derivative_numerator(e: Interval) -> Interval:
    """sin(e)^2 V'(e), continuously extended at e=0."""
    q,d,m,R,S=stable_parameters(e)
    p=sinc(e)
    pp=sinc_derivative(e)
    K=(e.square()+3/p.square()).sqrt()/2
    Kp=(e-3*pp/(p.square()*p))/(4*K)
    sk,ck=sin_cos(K)
    eta=((2-d)/(2+d)).sqrt()
    etap=2*q*eta/(4-d.square())
    den=ck+eta*sk
    Rp=(etap*sk*ck+eta*Kp)/den.square()
    Sp=(q+e*d)/m-e*q.square()/m.square()-q/2 \
       +Interval.rational(3,2)*(-2*d*q*R/m.square()+d.square()*Rp/m.square()
                               -2*d.square()*R*q/(m.square()*m))
    return q*Sp-d*S


def angle_cell(pi: Interval, left: Fraction, right: Fraction) -> Interval:
    return pi*Interval(Interval.rational(left).lo,Interval.rational(right).hi)


def prove_monotonicity(cells: int=512) -> dict:
    if not isinstance(cells,int) or isinstance(cells,bool) or cells<1:
        raise ValueError("cells must be a positive integer")
    pi=pi_interval()
    upper=[]
    for j in range(cells):
        value=derivative_numerator(angle_cell(pi,Fraction(j,2*cells),Fraction(j+1,2*cells)))
        if value.hi>=0:
            raise ArithmeticError(f"inconclusive monotonicity cell {j}: {value.hi}")
        upper.append(value.hi)
    return {"format":"reverse-monotonicity-proof-v1","cells":cells,
            "epsilon_over_pi_interval":["0","1/2"],"denominator":SCALE,
            "maximum_upper_numerator":max(upper),"cell_upper_numerators":upper,
            "status":"V'(e)<0 for all 0<e<pi/2"}


def comparison_at_degrees(beta: Fraction, kind: str) -> Interval:
    if not Fraction(90)<beta<Fraction(180):
        raise ValueError("root comparison is restricted to obtuse bends")
    pi=pi_interval()
    e=pi*Interval.rational((180-beta)/180)
    q,d,m,R,qV=stable_parameters(e)
    if kind=="lower":
        b=pi-e
        H=pi/2+q.square()/(b+q*d)
        return q*H-qV
    if kind=="upper":
        se,_=sin_cos(e/2)
        return 4*se-qV
    raise ValueError("kind must be lower or upper")


def certify_root(kind: str, left: Fraction, right: Fraction) -> dict:
    if left>=right:
        raise ValueError("reversed root bracket")
    l=comparison_at_degrees(left,kind)
    r=comparison_at_degrees(right,kind)
    if l.lo<=0 or r.hi>=0:
        raise ArithmeticError("bracket does not have the required strict signs")
    return {"kind":kind,"bend_degrees":[str(left),str(right)],
            "left_positive_lower_numerator":l.lo,
            "right_negative_upper_numerator":r.hi,"denominator":SCALE,
            "interpretation":"root of an explicit bound comparison, NOT beta_c"}


def prove_early_reverse_exclusion(cells: int=256) -> dict:
    """pi/2 > V(e)/(983/1000)^2 throughout e/pi in [1/3,1/2]."""
    if not isinstance(cells,int) or isinstance(cells,bool) or cells<1:
        raise ValueError("cells must be a positive integer")
    pi=pi_interval()
    r=Interval.rational(983,1000)
    if 27*(1000**2-983**2)*1000**4<=983**6:
        raise ArithmeticError("rational crossing constant failed")
    lower=[]
    for j in range(cells):
        e=angle_cell(pi,Fraction(1,3)+Fraction(j,6*cells),
                     Fraction(1,3)+Fraction(j+1,6*cells))
        q,_,_,_,qV=stable_parameters(e)
        gap=pi*q*r.square()/2-qV
        if gap.lo<=0:
            raise ArithmeticError(f"inconclusive early exclusion cell {j}")
        lower.append(gap.lo)
    return {"format":"reverse-early-exclusion-proof-v1","cells":cells,
            "epsilon_over_pi_interval":["1/3","1/2"],"scale":"983/1000",
            "minimum_lower_numerator":min(lower),"denominator":SCALE,
            "cell_lower_numerators":lower,"status":"scaled reverse bound below semicircle"}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cells",type=int,default=512)
    parser.add_argument("--output")
    args=parser.parse_args()
    report={"monotonicity":prove_monotonicity(args.cells),
            "early_exclusion":prove_early_reverse_exclusion(args.cells),
            "lower_comparison_root":certify_root("lower",Fraction("133.644346372"),Fraction("133.644346373")),
            "upper_comparison_root":certify_root("upper",Fraction("142.098382576"),Fraction("142.098382577"))}
    text=json.dumps(report,indent=2)+"\n"
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text)
    else:print(text,end="")
