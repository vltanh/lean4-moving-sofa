#!/usr/bin/env python3
"""Exact rational audit plus optional high-precision diagnostic for CF1–CF33.

The analytic proof is in complete-corner-fronts-and-ray-payment.md.
Fraction checks verify the strict, rationally stated ray-payment margins.
If mpmath is installed, elementary *closed primitives* F1/F2 are
evaluated as a diagnostic; their numerical values are NOT proof premises.
No CI, Lean, optimization, sampled-angle feasibility or interval
root search is used for the mathematical conclusions.
"""
from fractions import Fraction as F

# RH3's reference-support enclosures are independently reduced to
# elementary inequalities on the positive cubic root.
lo, hi = F(298,1000), F(2981,10000)
p = lambda y: 4*y**3 + 3*y-1
assert p(lo) < 0 < p(hi)
# m^2=(1+Y^2)/(9Y^2); it decreases strictly for Y>0.
assert (1+hi*hi)/(9*hi*hi) > F(29,25)**2
assert (1+lo*lo)/(9*lo*lo) < F(117,100)**2
assert hi < F(3,10)

assert F(3,2)*F(29,25)-F(20,39)>F(6,5)
assert F(17,100)+F(5,96)==F(533,2400)<F(9,40)
assert F(71,50)**2 > 2
assert F(32,25)+F(1,2)-F(71,50)==F(9,25)
assert F(9,25)-F(9,40)==F(27,200)
assert F(27,200)**2==F(729,40000)
assert 2*F(729,40000)==F(729,20000)

print("PASS: exact cubic bracket and first-phase corner-x coefficient")
print("PASS: entire reference corner projection within |x|<9/40")
print("PASS: full-turn 45-degree inner-ray surcharge >729/40000 per handed turn")
print("PASS: two disjoint ray surcharges >729/20000 ordinary area")

try:
    import mpmath as mp
except ImportError:
    print("Optional closed-form high-precision diagnostic skipped (mpmath absent)")
else:
    mp.mp.dps = 60
    Y = mp.findroot(lambda y: 4*y**3+3*y-1,mp.mpf(".298"))
    beta = mp.atan(Y)
    m = 1/(3*mp.sin(beta))
    A = 3*m/2
    R = mp.cos(beta)/mp.sin(3*beta/2+mp.pi/8)
    def f1(t):
        s,c=mp.sin(t),mp.cos(t)
        return (A*A*(t/4-mp.sin(4*t)/16)-A*s**3+A*c**3/2
                +5*t/8-3*mp.sin(2*t)/16-mp.cos(2*t)/4
                -A*mp.cos(2*t)/4+c/2-s/4)
    def f2(t):
        s,c=mp.sin(t),mp.cos(t)
        return ((3*R*R/4+1)*t-R*R/4*mp.sin(3*t+mp.pi/4)
                +mp.sqrt(2)*R/2*mp.cos(5*t/2-mp.pi/8)
                +5*mp.sqrt(2)*R/2*mp.cos(t/2+3*mp.pi/8)
                -mp.cos(2*t)/2-R/2*mp.cos(3*t/2+mp.pi/8)
                +(c-s)/2)
    tau = mp.findroot(
        lambda t: -3*m*mp.sin(t)*mp.cos(t)+mp.sin(t)+mp.cos(t)/2,
        (mp.mpf(".1"),beta))
    shadow = 2*(f1(beta)-f1(tau)+f2(mp.pi/4)-f2(beta))
    def support_terms(t):
        s,c=mp.sin(t),mp.cos(t);phi=t/2+mp.pi/8
        if t<=beta:
            f,df=m*c+s/2,-m*s+c/2
            g,dg=m*s/2+c/2+mp.mpf(".5"),m*c/2-s/2
        elif t<=mp.pi/2-beta:
            f,df=R*mp.cos(phi)+s/2,-R/2*mp.sin(phi)+c/2
            g,dg=R*mp.sin(phi)+c/2,R/2*mp.cos(phi)-s/2
        else:
            f,df=m*c/2+s/2+mp.mpf(".5"),-m*s/2+c/2
            g,dg=m*s+c/2,m*c-s/2
        return f*f-df*df+g*g-dg*dg
    cap=mp.quad(support_terms,[0,beta,mp.pi/2-beta,mp.pi/2])/2
    hull=2*cap-2*m
    M=1+4*Y*Y+mp.atan(Y)
    niche=(hull-M)/2
    print("Diagnostic reference corner shadow:",mp.nstr(shadow,22))
    print("Diagnostic reference complete niche per turn:",mp.nstr(niche,22))
    print("Diagnostic ray surcharge per turn:",mp.nstr(niche-shadow,22))
    print("Diagnostic fraction shadow/full niche:",mp.nstr(shadow/niche,14))
    assert niche-shadow>mp.mpf(729)/40000
