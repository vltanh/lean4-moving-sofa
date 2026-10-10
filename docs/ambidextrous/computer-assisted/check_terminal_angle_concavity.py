#!/usr/bin/env python3
"""Exact Fraction audit of niche-free terminal-angle concavity failure.

All-angle niche absence is proved analytically by the corner-height
factorization in terminal-angle-concavity-obstruction.md. This checker
only independently verifies the algebraic rational second derivative.
No floating-point integration, CI, or Lean.
"""
from fractions import Fraction as F


def main():
    W = F(3, 4)
    s, c = F(4, 5), F(3, 5)
    d = c / (1 + s)
    r = W - d
    C = c / s
    Cp = -1 / (s * s)
    Cpp = 2 * c / (s * s * s)
    rp = 1 / (1 + s)
    rpp = -c / (1 + s)**2
    f = W - C * r*r/2
    fpp = -(Cpp*r*r + 4*Cp*r*rp +
            2*C*(rp*rp + r*rpp))/2
    assert d == F(1, 3)
    assert r == F(5, 12)
    assert f == F(263, 384)
    assert fpp == F(9575, 27648) > 0
    # sqrt(2)<5/3 by squaring. Therefore 3/8*(1+sqrt(2))<1.
    assert F(5, 3)**2 > 2
    assert F(3, 8)*(1+F(5, 3)) == 1
    print("PASS: niche-free width 3/4, exact midpoint-angle curvature", fpp)
    print("PASS: exact signed area at rational frame", f)
    print("PASS: universal corner-height nonpositivity reduced to sqrt(2)<5/3")


if __name__ == "__main__":
    main()
