"""Exact-integer certificate removing the actual-width restriction.

Covers every epsilon in [0, pi/3], including the removable singularity at 0.
The two comparisons combine the corrected quadratic bound with midpoint
slicing, as detailed in REVERSE_GENERAL_MAJORANT.md. No sampled optimizer,
floating-point trigonometry, or third-party arithmetic library is used.
"""
from __future__ import annotations
from fractions import Fraction
from math import factorial
import argparse
import json

from parameter_certificate import BITS, SCALE, Interval, pi_interval, sin_cos


def sinc(x: Interval) -> Interval:
    """sin(x)/x with its continuous value 1 at zero, on [-4,4]."""
    if max(abs(x.lo), abs(x.hi)) > 4*SCALE:
        raise ValueError("sinc argument outside [-4,4]")
    n = 36
    # Integrate the degree-72 Taylor formula for cos(tx), 0 <= t <= 1.
    if Fraction(4**74, factorial(75)) >= Fraction(1, SCALE):
        raise ArithmeticError("sinc remainder exceeds one dyadic unit")
    xx = x.square()
    p = Interval.rational((-1)**n, factorial(2*n+1))
    for j in range(n-1, -1, -1):
        p = p*xx + Interval.rational((-1)**j, factorial(2*j+1))
    return p + Interval(-1, 1)


def width_inequalities(e: Interval) -> tuple[Interval, Interval, Interval]:
    q, d = sin_cos(e)
    sc = sinc(e)
    K = (e.square()+3/sc.square()).sqrt()/2
    sk, ck = sin_cos(K)
    eta = ((2-d)/(2+d)).sqrt()
    T = eta*sk/ck
    m = 2-d
    d2, d3 = d.square(), d.square()*d
    # q*V(e) extends continuously to e=0.
    qV = e*q/m + (2*T*d3-T*d2+4*T*d+4*T+2*d3-7*d2+4*d+4)/(4*(1+T)*m.square())
    _, c = sin_cos(e/2)
    narrow = qV-c
    # Positive iff F_e(1)-F_e(1/2)>0; its denominator is positive.
    half_width_gap = m*(6*d+7)-T*(6*d2+13*d-2)
    # Positive iff derivative in endpoint half-height l at l=1/2 is negative.
    endpoint_derivative = m*(2*d+1)-T*(2*d-1)*(d+2)
    return narrow, half_width_gap, endpoint_derivative


def prove_width(cells: int = 512) -> dict:
    if not isinstance(cells, int) or isinstance(cells, bool) or cells < 1:
        raise ValueError("cells must be a positive integer")
    pi = pi_interval()
    minima = [None, None, None]
    bounds = []
    for j in range(cells):
        left, right = Fraction(j, 3*cells), Fraction(j+1, 3*cells)
        e = pi*Interval(Interval.rational(left).lo, Interval.rational(right).hi)
        values = width_inequalities(e)
        row = [v.lo for v in values]
        if min(row) <= 0:
            raise ArithmeticError(f"inconclusive width cell {j}: {row}")
        for k, value in enumerate(row):
            minima[k] = value if minima[k] is None else min(minima[k], value)
        bounds.append(row)
    return {
        "format": "reverse-width-proof-v1", "status": "all cells strictly positive",
        "precision_bits": BITS, "denominator": SCALE, "cells": cells,
        "epsilon_over_pi_interval": ["0", "1/3"],
        "inequalities": ["sin(e)*V(e)-cos(e/2)>0", "F_e(1)-F_e(1/2)>0 (positive scaling)",
                         "negative half-height derivative at l=1/2 (positive scaling)"],
        "minimum_lower_numerators": minima, "cell_lower_numerators": bounds,
        "trust": "Python exact integer arithmetic, Fraction and isqrt; no floating-point arithmetic",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cells", type=int, default=512)
    parser.add_argument("--output", help="JSON certificate log; default is stdout")
    args = parser.parse_args()
    result = json.dumps(prove_width(args.cells), indent=2) + "\n"
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(result)
    else:
        print(result, end="")
