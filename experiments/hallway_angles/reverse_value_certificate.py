"""Exact-rational displays and a continuum forward-class exclusion.

The expressions evaluated here depend on the mathematical optimality and
alignment theorems; this module certifies their scalar evaluations only.
"""
from __future__ import annotations
from fractions import Fraction
import json
from parameter_certificate import Interval, SCALE, pi_interval, sin_cos
from width_certificate import sinc


def scaled_value(e: Interval) -> Interval:
    """sin(e)*V(e), extended continuously to e=0."""
    q, d = sin_cos(e)
    K = (e.square()+3/sinc(e).square()).sqrt()/2
    sk, ck = sin_cos(K)
    m = 2-d
    eta = (m/(2+d)).sqrt()
    ratio = eta*sk/(ck+eta*sk)
    return e*q/m+(1+2*d)/4+3*d.square()*ratio/(2*m.square())


def prove_forward_exclusion(cells: int = 256) -> dict:
    """Prove V(e)>2 sec(e/2) for 0<e<=37*pi/180 (beta>=143 deg)."""
    if not isinstance(cells,int) or isinstance(cells,bool) or cells<1:
        raise ValueError("cells must be a positive integer")
    pi=pi_interval()
    bounds=[]
    for j in range(cells):
        left=Fraction(37*j,180*cells)
        right=Fraction(37*(j+1),180*cells)
        e=pi*Interval(Interval.rational(left).lo,Interval.rational(right).hi)
        sn,_=sin_cos(e/2)
        gap=scaled_value(e)-4*sn
        if gap.lo<=0:
            raise ArithmeticError(f"inconclusive forward-exclusion cell {j}")
        bounds.append(gap.lo)
    return {"format":"reverse-forward-exclusion-v1", "cells":cells,
            "epsilon_over_pi_interval":["0","37/180"],
            "positive_expression":"sin(e)*V(e)-4*sin(e/2)",
            "denominator":SCALE, "minimum_lower_numerator":min(bounds),
            "cell_lower_numerators":bounds, "status":"all cells strictly positive"}


def decimal_outward(x: Interval, digits: int=6) -> dict:
    if not isinstance(digits,int) or isinstance(digits,bool) or not 0<=digits<=20:
        raise ValueError("digits must be an integer in [0,20]")
    factor=10**digits
    lo=x.lo*factor//SCALE
    hi=-((-x.hi*factor)//SCALE)
    def text(n):
        sign='-' if n<0 else ''
        n=abs(n)
        return sign+str(n//factor)+(('.'+str(n%factor).zfill(digits)) if digits else '')
    return {"lower":text(lo),"upper":text(hi)}


def value_bounds(bend_degrees: int) -> dict:
    if not isinstance(bend_degrees,int) or isinstance(bend_degrees,bool) or not 120<=bend_degrees<180:
        raise ValueError("integer bend must be in [120,180)")
    e=pi_interval()*Interval.rational(180-bend_degrees,180)
    q,_=sin_cos(e)
    _,c=sin_cos(e/2)
    V=scaled_value(e)/q
    forward=2/c
    U=Interval(max(V.lo,forward.lo),max(V.hi,forward.hi))
    upper=U+1/(4*U)
    return {"bend_degrees":bend_degrees,
            "reverse_optimum":decimal_outward(V,9),
            "unrestricted_lower":decimal_outward(V,6)['lower'],
            "unrestricted_upper":decimal_outward(upper,6)['upper']}


if __name__=='__main__':
    report={"forward_exclusion":prove_forward_exclusion(),
            "asymptotic_constant":decimal_outward(scaled_value(Interval.rational(0)),12),
            "values":[value_bounds(b) for b in (120,135,137,143,150,170,179)]}
    print(json.dumps(report,indent=2))
