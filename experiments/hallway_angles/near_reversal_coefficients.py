"""Exact-integer enclosures for the near-reversal Laurent coefficients.

These evaluate the analytic formulas. Their interpretation as unrestricted
optimum coefficients depends on the theorem draft, not on this calculation.
"""
from parameter_certificate import Interval, SCALE, sin_cos
import json


def coefficients() -> dict:
    r = Interval.rational(3).sqrt()
    sine, cosine = sin_cos(r/2)
    t = sine/(r*cosine)
    c = 3*(1+3*t)/(4*(1+t))
    c1 = (9-4*t-9*t.square())/(8*(1+t).square())
    flat = 3*(1-t)/(2*(1+t))
    return {
        "format": "near-reversal-coefficients-v1", "denominator": SCALE,
        "T0": [t.lo,t.hi], "leading_area": [c.lo,c.hi],
        "next_area": [c1.lo,c1.hi], "limit_contact_length": [flat.lo,flat.hi],
        "trust": "Python exact integer arithmetic and isqrt; no floating arithmetic",
    }


if __name__ == "__main__":
    print(json.dumps(coefficients(),indent=2))
