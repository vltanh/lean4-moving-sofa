"""Exact-integer interval proof of two reverse-sofa parameter inequalities.

No floating-point operations, third-party libraries, networking, or optimizer
are used in the proof. Intervals are dyadic with fixed denominator 2**96.
The only numerical trust is Python's integer arithmetic and isqrt.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import factorial, isqrt
import argparse
import json

BITS = 96
SCALE = 1 << BITS


def ceil_div(a: int, b: int) -> int:
    if b == 0:
        raise ZeroDivisionError("zero interval divisor")
    return -((-a) // b)


@dataclass(frozen=True)
class Interval:
    """Closed [lo/2**BITS, hi/2**BITS] with exact integer endpoints."""
    lo: int
    hi: int

    def __post_init__(self) -> None:
        if not isinstance(self.lo, int) or not isinstance(self.hi, int):
            raise TypeError("interval endpoints must be integers")
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @classmethod
    def rational(cls, a: int | Fraction, b: int = 1) -> Interval:
        q = Fraction(a, b)
        return cls((q.numerator * SCALE) // q.denominator,
                   ceil_div(q.numerator * SCALE, q.denominator))

    @staticmethod
    def coerce(value: Interval | int) -> Interval:
        if isinstance(value, Interval):
            return value
        if isinstance(value, int):
            return Interval.rational(value)
        raise TypeError("use Interval.rational for noninteger constants")

    def __add__(self, other: Interval | int) -> Interval:
        b = self.coerce(other)
        return Interval(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self) -> Interval:
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: Interval | int) -> Interval:
        return self + (-self.coerce(other))

    def __rsub__(self, other: Interval | int) -> Interval:
        return self.coerce(other) + (-self)

    def __mul__(self, other: Interval | int) -> Interval:
        b = self.coerce(other)
        products = (self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi)
        return Interval(min(products) // SCALE, ceil_div(max(products), SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other: Interval | int) -> Interval:
        b = self.coerce(other)
        if b.lo <= 0 <= b.hi:
            raise ZeroDivisionError("interval divisor contains zero")
        numerators = (self.lo*SCALE, self.hi*SCALE)
        floors = [n // d for n in numerators for d in (b.lo, b.hi)]
        ceilings = [ceil_div(n, d) for n in numerators for d in (b.lo, b.hi)]
        return Interval(min(floors), max(ceilings))

    def __rtruediv__(self, other: Interval | int) -> Interval:
        return self.coerce(other) / self

    def square(self) -> Interval:
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo*self.lo, self.hi*self.hi)
        high = max(self.lo*self.lo, self.hi*self.hi)
        return Interval(low // SCALE, ceil_div(high, SCALE))

    def sqrt(self) -> Interval:
        if self.lo < 0:
            raise ValueError("negative square-root interval")
        low, high = isqrt(self.lo*SCALE), isqrt(self.hi*SCALE)
        if high*high < self.hi*SCALE:
            high += 1
        return Interval(low, high)

    def contains(self, q: Fraction) -> bool:
        return self.lo*q.denominator <= q.numerator*SCALE <= self.hi*q.denominator


def atan_reciprocal_bounds(n: int, terms: int = 100) -> tuple[Fraction, Fraction]:
    """Alternating-series enclosure for atan(1/n), n >= 2."""
    if n < 2 or terms < 1:
        raise ValueError("invalid atan series input")
    total = sum((Fraction((-1)**j, (2*j+1)*n**(2*j+1))
                 for j in range(terms)), Fraction(0))
    next_term = Fraction((-1)**terms, (2*terms+1)*n**(2*terms+1))
    return min(total, total+next_term), max(total, total+next_term)


def pi_interval() -> Interval:
    a0, a1 = atan_reciprocal_bounds(5)
    b0, b1 = atan_reciprocal_bounds(239)
    lower, upper = 16*a0-4*b1, 16*a1-4*b0
    return Interval(Interval.rational(lower).lo, Interval.rational(upper).hi)


def sin_cos(x: Interval) -> tuple[Interval, Interval]:
    """Taylor enclosure on |x| <= 4; remainders proved by exact inequalities."""
    if max(abs(x.lo), abs(x.hi)) > 4*SCALE:
        raise ValueError("Taylor argument outside [-4,4]")
    # Degree 73 sine and degree 72 cosine. Taylor's theorem applied through
    # degrees 74 and 73 respectively yields the stated remainder bounds.
    n = 36
    if not (Fraction(4**75, factorial(75)) < Fraction(1, SCALE)
            and Fraction(4**74, factorial(74)) < Fraction(1, SCALE)):
        raise ArithmeticError("Taylor remainder does not fit the interval precision")
    xx = x.square()
    ps = Interval.rational((-1)**n, factorial(2*n+1))
    pc = Interval.rational((-1)**n, factorial(2*n))
    for j in range(n-1, -1, -1):
        ps = ps*xx + Interval.rational((-1)**j, factorial(2*j+1))
        pc = pc*xx + Interval.rational((-1)**j, factorial(2*j))
    return x*ps + Interval(-1, 1), pc + Interval(-1, 1)


def geometric_inequalities(e: Interval) -> tuple[Interval, Interval]:
    """R and denominator-cleared X controlling rho(e)>0 and x''(L)>0."""
    q, d = sin_cos(e)
    q2 = q.square()
    k = (1+3/q2).sqrt()
    K = e*k/2
    sk, ck = sin_cos(K)
    eta = ((2-d)/(2+d)).sqrt()
    curvature = (2*q2+3*d)*ck + eta*(2*q2-3*d)*sk
    plus2 = (1+d).square()
    convexity = ((2*(1-d)*q2+3*d*(3-2*d))*plus2)*ck \
                 + eta*((2*(1-d)*plus2-3*d*(2*d+3))*q2)*sk
    return curvature, convexity


def prove(cells: int = 512) -> dict:
    """Cover e/pi in [1/6,4/9] with exact parameter intervals."""
    if not isinstance(cells, int) or isinstance(cells, bool) or cells < 1:
        raise ValueError("cells must be a positive integer")
    pi = pi_interval()
    start, finish = Fraction(1, 6), Fraction(4, 9)
    minimum_r = minimum_x = None
    all_bounds = []
    for j in range(cells):
        left = start + (finish-start)*j/cells
        right = start + (finish-start)*(j+1)/cells
        angle_fraction = Interval(Interval.rational(left).lo, Interval.rational(right).hi)
        R, X = geometric_inequalities(pi*angle_fraction)
        if R.lo <= 0 or X.lo <= 0:
            raise ArithmeticError(f"inconclusive cell {j}: lower endpoints R={R.lo}, X={X.lo}")
        minimum_r = R.lo if minimum_r is None else min(minimum_r, R.lo)
        minimum_x = X.lo if minimum_x is None else min(minimum_x, X.lo)
        all_bounds.append([R.lo, X.lo])
    return {
        "format": "reverse-parameter-proof-v1", "status": "all cells strictly positive",
        "precision_bits": BITS, "denominator": SCALE, "cells": cells,
        "epsilon_over_pi_interval": ["1/6", "4/9"],
        "pi_lower_numerator": pi.lo, "pi_upper_numerator": pi.hi,
        "minimum_R_lower_numerator": minimum_r,
        "minimum_X_lower_numerator": minimum_x,
        "cell_lower_numerators": all_bounds,
        "trust": "Python exact integer arithmetic, Fraction and isqrt; no floating-point arithmetic",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cells", type=int, default=512)
    parser.add_argument("--output", help="JSON certificate log; default is stdout")
    args = parser.parse_args()
    result = json.dumps(prove(args.cells), indent=2) + "\n"
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(result)
    else:
        print(result, end="")
