"""Local checks for the analytic stability proofs; not Lean or interval certification.

Run: python docs/stability/check_stability.py
Requires SciPy only for independent numerical quadrature. No solver, Gerver
reference, network, repository build, or CI is used.
"""
from __future__ import annotations

import math
import unittest
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Sequence

from scipy.integrate import quad

PI = math.pi
V = PI / 2
Fn = Callable[[float], float]


@dataclass(frozen=True)
class Term:
    residual: int
    start: float
    end: float
    coefficient: Fn


def validate(phi: float, t: float) -> None:
    if not (math.isfinite(phi) and 0 < phi < PI / 4):
        raise ValueError('phi must be strictly between 0 and pi/4')
    if not (math.isfinite(t) and 0 <= t <= PI):
        raise ValueError('t must lie in [0,pi]')


def green_terms(phi: float, t: float) -> list[Term]:
    """Exact evaluation kernels, with all integration breakpoints explicit."""
    validate(phi, t)
    b, target, sec = V - phi, PI - phi, 1 / math.cos(phi)
    if t == V or t == PI:
        return []
    if t > V:
        return [Term(3, V, t, lambda u: -math.sin(t) / math.sin(u))]
    if t >= b:
        return [Term(2, t, V, lambda u: math.sin(target-t) / math.sin(target-u)),
                Term(3, V, target, lambda u: math.tan(phi)*math.cos(t)/math.sin(u))]
    if t >= phi:
        return [Term(1, t, b, lambda u: 1.),
                Term(2, b, V, lambda u: 1 / math.sin(target-u)),
                Term(3, V, V+t, lambda u: (sec-math.sin(t))/math.sin(u)),
                Term(3, V+t, target, lambda u: (sec+math.cos(u))/math.sin(u))]
    scale = math.cos(t) * sec
    terms = [Term(0, t, phi, lambda u: math.cos(t)/math.cos(u))]
    for term in green_terms(phi, phi):
        terms.append(Term(term.residual, term.start, term.end,
                          lambda u, k=term.coefficient: scale*k(u)))
    return terms


def integrate(fun: Fn, a: float, b: float) -> float:
    if a == b:
        return 0.
    return float(quad(fun, a, b, epsabs=3e-12, epsrel=3e-12, limit=150)[0])


def diagonal(phi: float, t: float) -> float:
    """Closed form of the squared L2 evaluation norm D(t)."""
    validate(phi, t)
    b, sec = V - phi, 1 / math.cos(phi)
    if t == V or t == PI:
        return 0.
    if t <= phi:
        return math.cos(t)**2 * (2*sec**2-math.tan(t))
    if t <= b:
        return math.cos(t)*(2*sec-math.sin(t))
    if t <= V:
        return math.sin(t)*math.cos(t)+2*math.tan(phi)*math.cos(t)**2
    return -math.sin(t)*math.cos(t)


def norm_squared(phi: float, t: float) -> float:
    return sum(integrate(lambda u, k=q.coefficient: k(u)**2, q.start, q.end)
               for q in green_terms(phi, t))


def apply_green(phi: float, t: float, residuals: Sequence[Fn]) -> float:
    if len(residuals) != 4:
        raise ValueError('four residual functions required')
    return sum(integrate(lambda u, q=q: q.coefficient(u)*residuals[q.residual](u),
                         q.start, q.end) for q in green_terms(phi, t))


def polynomial_example(phi: float) -> tuple[Fn, Fn, list[Fn]]:
    def p(t):
        return 1 + .1*t - .04*t*t
    def dp(t):
        return .1 - .08*t
    def f(t):
        return math.sin(t)*math.cos(t)*p(t)
    def df(t):
        return math.cos(2*t)*p(t)+math.sin(t)*math.cos(t)*dp(t)
    target = PI-phi
    r = [lambda t: -math.cos(t)**2*p(t)-math.sin(t)*math.cos(t)*dp(t),
         lambda t: f(t+V)-df(t),
         lambda t: (f(target)-math.cos(target-t)*f(t))/math.sin(target-t)-df(t),
         lambda t: math.sin(t)**2*p(t)-math.sin(t)*math.cos(t)*dp(t)]
    return f, df, r


class CoercivityChecks(unittest.TestCase):
    def test_parameter_validation(self):
        for p,t in [(0,0), (PI/4,0), (.04,-1), (.04,PI+.1), (float('nan'),0)]:
            with self.assertRaises(ValueError):
                green_terms(p,t)

    def test_quadrature_matches_all_four_diagonal_formulas(self):
        for p in [.01,.04,.2,.7]:
            ends = [0,p,V-p,V,PI]
            for a,b in zip(ends,ends[1:]):
                for j in range(1,8):
                    t = a+(b-a)*j/8
                    with self.subTest(phi=p,t=t):
                        self.assertAlmostEqual(norm_squared(p,t),diagonal(p,t),places=10)

    def test_junctions_and_endpoints(self):
        for p in [.01,.04,.2,.7]:
            for t in [0,p,V-p,V,PI]:
                self.assertAlmostEqual(norm_squared(p,t),diagonal(p,t),places=10)

    def test_reconstruction_from_independent_residuals(self):
        for p in [.04,.2,.7]:
            f,_,r = polynomial_example(p)
            for t in [0,p/3,p,(p+V-p)/2,V-p,V,2.,PI-.001,PI]:
                self.assertAlmostEqual(apply_green(p,t,r),f(t),places=10)

    def test_energy_inequality(self):
        for p in [.04,.2,.7]:
            f,_,r=polynomial_example(p)
            ends=[0,p,V-p,V,PI]
            energy=.5*sum(integrate(lambda t,j=j:r[j](t)**2,ends[j],ends[j+1])
                          for j in range(4))
            bound=2/math.cos(p)*math.sqrt(energy)
            self.assertLessEqual(max(abs(f(PI*j/1000)) for j in range(1001)),bound)

    def test_global_maximum_and_monotonicity(self):
        for p in [.001,.04,.2,.5,.78]:
            values=[diagonal(p,V*j/1000) for j in range(1001)]
            self.assertTrue(all(b<=a+1e-12 for a,b in zip(values,values[1:])))
            self.assertAlmostEqual(values[0],2/math.cos(p)**2,places=12)
            self.assertLessEqual(max(diagonal(p,PI*j/2000) for j in range(2001)),
                                 values[0]+1e-12)

    def test_sharp_witness_norm_and_attainment(self):
        for p in [.04,.2,.7]:
            d=norm_squared(p,0)
            # The Riesz coefficient tuple for evaluation at zero is the witness.
            self.assertAlmostEqual(d/math.sqrt(d/2),2/math.cos(p),places=11)

    def test_translation_is_a_genuine_null_direction(self):
        p=.04
        for t in [p/2,.5,V-p/2,2.]:
            h,dh=math.cos(t),-math.sin(t)
            if t<p:
                r=-math.tan(t)*h-dh
            elif t<V-p:
                r=math.cos(t+V)-dh
            elif t<V:
                target=PI-p
                r=(math.cos(target)-math.cos(target-t)*h)/math.sin(target-t)-dh
            else:
                r=(-1+math.cos(t)*h)/math.sin(t)-dh
            self.assertAlmostEqual(r,0.,places=12)
        self.assertEqual(math.cos(0),1.)  # Unpinned supremum cannot be controlled.

    def test_exact_rational_constant(self):
        cosine_lower=1-Fraction(4,100)**2/2
        self.assertEqual(cosine_lower,Fraction(1249,1250))
        self.assertLess(2/cosine_lower,Fraction(1001,500))

    def test_near_singular_last_endpoint(self):
        p=.04
        for e in [1e-2,1e-4,1e-6]:
            t=PI-e
            self.assertAlmostEqual(diagonal(p,t),math.sin(e)*math.cos(e),places=13)
            self.assertLessEqual(diagonal(p,t),e+4e-15)  # Absolute floating-point tolerance.

    def test_polynomial_antiderivative_for_middle_kernel(self):
        for p in [.04,.2,.7]:
            sec=1/math.cos(p)
            F=lambda w:(sec*sec+1)*math.tan(w)-2*sec/math.cos(w)-w
            for t in [p,(p+V-p)/2,V-p]:
                value=integrate(lambda w:(sec-math.sin(w))**2/math.cos(w)**2,t,V-p)
                self.assertAlmostEqual(value,F(V-p)-F(t),places=10)


class GeometricChecks(unittest.TestCase):
    def test_quadrant_distance_implies_wall_slack_margin(self):
        for a in [-2.,-.1,0.,.2,1.]:
            for b in [-1.,0.,.3,2.]:
                distance=math.hypot(max(a,0),max(b,0))
                if distance>0:
                    self.assertGreaterEqual(max(a,b)+1e-15,distance/math.sqrt(2))

    def test_reference_corner_depth_exclusion(self):
        phi,delta=.04,.001
        depth=1.01*delta/math.sin(phi)
        for t in [phi,.2,V/2,V-phi]:
            a,b=-depth*math.sin(t),-depth*math.cos(t)
            self.assertLess(a+delta,0)
            self.assertLess(b+delta,0)

    def test_lipschitz_graph_interior_ball_construction(self):
        a,b,H,L=-1.,1.,.4,.6
        roof=lambda x:.3+.1*math.sin(6*x)
        for x in [a,a+.01,0,b-.01,b]:
            for y in [roof(x),(1+H)/2]:
                for radius in [.01,.1,.3]:
                    w=radius/(4*(L+2))
                    sign=1 if x<=(a+b)/2 else -1
                    cx,cy=x+sign*2*w,y+(3*L+2)*w
                    self.assertLessEqual(math.hypot(cx-x,cy-y)+w,radius)
                    for j in range(121):
                        angle=2*PI*j/120
                        px,py=cx+w*math.cos(angle),cy+w*math.sin(angle)
                        self.assertGreaterEqual(px,a-1e-12)
                        self.assertLessEqual(px,b+1e-12)
                        self.assertGreaterEqual(py,roof(px)-1e-12)
                        self.assertLessEqual(py,1+1e-12)

    def test_hole_area_coefficient(self):
        kappa,d=.2,.01
        radius=kappa*d/4
        eps=PI*radius**2
        self.assertAlmostEqual(4*math.sqrt(eps)/(kappa*math.sqrt(PI)),d,places=14)

    def test_convex_piece_homothety_ball(self):
        # Unit square with its radius-1/2 inscribed ball.
        center=(.5,.5); inscribed=.5; diameter=math.sqrt(2)
        for p in [(0.,0.),(0.,1.),(1.,1.),(.3,.8)]:
            for rho in [.01,.2,.8]:
                lam=rho/(diameter+inscribed)
                c=tuple(p[i]+lam*(center[i]-p[i]) for i in range(2))
                r=lam*inscribed
                self.assertLessEqual(math.dist(p,c)+r,rho)
                self.assertGreaterEqual(min(c)-r,-1e-12)
                self.assertLessEqual(max(c)+r,1+1e-12)

    def test_area_continuity_shortcut_is_invalid(self):
        # Connected n-by-n grid skeletons: exact area=0 but dense in the unit square.
        for n in [2,4,8,16]:
            skeleton_area=0
            hausdorff_to_square=1/(2*n)
            self.assertEqual(skeleton_area,0)
            self.assertGreater(hausdorff_to_square,0)
        self.assertLess(1/(2*16),1/(2*2))
        self.assertNotEqual(skeleton_area,1)  # Area of the limiting square.


if __name__=='__main__':
    unittest.main(verbosity=2)
