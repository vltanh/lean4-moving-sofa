"""Exact width comparisons on ALL obtuse bends, including endpoint limits.

Uses the branch's existing exact-integer dyadic arithmetic. These scalar
lemmas do not by themselves supply a geometric majorant for wide sofas.
"""
from __future__ import annotations
from fractions import Fraction
import argparse
import json
from parameter_certificate import BITS, SCALE, Interval, pi_interval, sin_cos
from width_certificate import sinc


def stable_parameters(e: Interval) -> tuple[Interval, ...]:
    """Return q,d,m,R,qV with no tan(K) or division by sin(e)."""
    q,d=sin_cos(e)
    K=(e.square()+3/sinc(e).square()).sqrt()/2
    sk,ck=sin_cos(K)
    eta=((2-d)/(2+d)).sqrt()
    den=ck+eta*sk
    if den.lo<=0:
        raise ArithmeticError("inconclusive positivity of candidate denominator")
    R=eta*sk/den
    m=2-d
    qV=e*q/m+(1+2*d)/4+3*d.square()*R/(2*m.square())
    return q,d,m,R,qV


def extended_width_inequalities(e: Interval) -> tuple[Interval, ...]:
    q,d,m,R,qV=stable_parameters(e)
    _,c=sin_cos(e/2)
    narrow=qV-c
    half_gap=(1-R)*m*(6*d+7)-R*(6*d.square()+13*d-2)
    derivative=(1-R)*m*(2*d+1)-R*(2*d-1)*(d+2)
    return narrow,half_gap,derivative


def prove_extended_width(cells: int=256) -> dict:
    if not isinstance(cells,int) or isinstance(cells,bool) or cells<1:
        raise ValueError("cells must be a positive integer")
    pi=pi_interval()
    bounds=[]
    for j in range(cells):
        l=Interval.rational(j,2*cells)
        r=Interval.rational(j+1,2*cells)
        values=extended_width_inequalities(pi*Interval(l.lo,r.hi))
        row=[x.lo for x in values]
        if min(row)<=0:
            raise ArithmeticError(f"inconclusive width cell {j}: {row}")
        bounds.append(row)
    return {"format":"reverse-extended-width-proof-v1",
            "status":"all cells strictly positive",
            "precision_bits":BITS,"denominator":SCALE,"cells":cells,
            "epsilon_over_pi_interval":["0","1/2"],
            "inequalities":["qV-cos(e/2)>0","(1-R)m(6d+7)-R(6d^2+13d-2)>0",
                            "(1-R)m(2d+1)-R(2d-1)(d+2)>0"],
            "minimum_lower_numerators":[min(row[k] for row in bounds) for k in range(3)],
            "cell_lower_numerators":bounds,
            "trust":"Python exact integer/rational arithmetic and isqrt; no floating-point proof"}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cells",type=int,default=256)
    parser.add_argument("--output")
    args=parser.parse_args()
    text=json.dumps(prove_extended_width(args.cells),indent=2)+"\n"
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text)
    else:
        print(text,end="")
