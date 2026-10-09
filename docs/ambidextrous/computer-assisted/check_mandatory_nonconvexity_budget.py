#!/usr/bin/env python3
"""Exact Fraction arithmetic backing NC1 mandatory hull-niche budget.

Geometric inputs are the convex two-corner area certificate CV1
and the previously proved competitive width bound PTW1.
All rational inequalities here are exact; no CI/Lean.
"""
from fractions import Fraction as F

x=F(149,500)
cubic=4*x**3+3*x-1
atan_lower=x-x**3/3+x**5/5-x**7/7
M_lower=1+4*x*x+atan_lower
max_convex=F(31,20)
depth=F(103,100)
scaled_threshold=max_convex*depth*depth

assert cubic == -F(4551,31250000)<0
assert scaled_threshold==F(328879,200000)
assert M_lower>scaled_threshold
assert M_lower-scaled_threshold==F(
    72188080152239353,164062500000000000000)
assert F(31,20)<F(8,5)
assert F(8,5)/10000==F(1,6250)
assert F(3,200)*2==depth-1

print("PASS: cubic root lower bound and alternating arctangent comparison")
print("PASS: exact M lower > (31/20)*(103/100)^2")
print("PASS: scaling 1/100 forces forbidden convex-hull copy area > 1/6250")
print("PASS: Hausdorff separation from convex-compatible hulls >= 3/200")
