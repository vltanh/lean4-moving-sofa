"""Local diagnostics for notes 05--09; not Lean or interval certification.

Run: python docs/stability/check_completion.py
Only NumPy and mpmath are needed. No optimizer, network, or CI is invoked.
The reference equations are those in scripts/figures/gerver.py; their
analytic support derivatives and the independent curve-area calculation
below test the nonsmooth extension, not numerical optimality.
"""
from __future__ import annotations

from functools import lru_cache
import json
from pathlib import Path
import unittest

import mpmath as mp
import numpy as np
from numpy.polynomial.legendre import leggauss

PI = np.pi
V = PI / 2


def unit(t):
    return np.array([np.cos(t), np.sin(t)])


def tangent(t):
    return np.array([-np.sin(t), np.cos(t)])


def cross(p, q):
    return float(p[0]*q[1]-p[1]*q[0])


@lru_cache(maxsize=None)
def gauss(order):
    return leggauss(order)


def integral(fun, lo, hi, breaks=(), order=64):
    cuts = np.unique([lo, *[x for x in breaks if lo < x < hi], hi])
    nodes, weights = gauss(order)
    result = 0.
    for a, b in zip(cuts[:-1], cuts[1:]):
        for t, w in zip((a+b)/2+(b-a)*nodes/2, weights*(b-a)/2):
            result += w*fun(float(t))
    return float(result)


class PolygonSupport:
    """CCW polygon, or a two-point segment; curvature atoms are retained."""
    def __init__(self, vertices):
        self.vertices = np.asarray(vertices, dtype=float)
        self.atoms = []
        for p, q in zip(self.vertices, np.roll(self.vertices, -1, axis=0)):
            e = q-p
            length = float(np.linalg.norm(e))
            if length > 1e-10:
                normal = np.array([e[1], -e[0]])/length
                angle = float(np.arctan2(normal[1], normal[0]) % (2*PI))
                self.atoms.append((angle, length, float(p@normal)))
        self.breaks = [a for a, _, _ in self.atoms]

    def support(self, t):
        values = self.vertices@unit(t)
        i = int(np.argmax(values))
        return float(values[i]), float(self.vertices[i]@tangent(t))

    def face(self, t, plus):
        values = self.vertices@unit(t)
        points = self.vertices[values >= max(values)-1e-10]
        k = np.argmax(points@tangent(t)) if plus else np.argmin(points@tangent(t))
        return points[int(k)]

    def area(self):
        return sum(cross(p, q) for p, q in zip(
            self.vertices, np.roll(self.vertices, -1, axis=0)))/2

    def arc_area(self, lo, hi):
        return sum(length*h/2 for a, length, h in self.atoms
                   if lo+1e-10 < a < hi-1e-10)


class GerverReference:
    """Analytic reference, including one-sided phase derivatives."""
    def __init__(self):
        with mp.workdps(40):
            def system(A, B, f, t):
                c, s = mp.cos, mp.sin
                return [A*(c(t)-c(f))-2*B*s(f)+(t-f-1)*c(t)-s(t)+c(f)+s(f),
                        A*(3*s(t)+s(f))-2*B*c(f)+3*(t-f-1)*s(t)+3*c(t)-s(f)+c(f),
                        A*c(f)-(s(f)+mp.mpf(1)/2-c(f)/2+B*s(f)),
                        A+mp.pi/2-f-t-(B-(t-f)*(1+A)/2-(t-f)**2/4)]
            A, B, f, th = map(float, mp.findroot(system, (.0944, 1.3992, .0392, .6813)))
        self.phi, self.theta = f, th
        self.a1 = ((A+.5)*np.sin(f)+(B+1)*np.cos(f))/2
        self.b1 = (f-1-A)/2
        self.b2 = B-.5-self.b1*f+f*f/4
        self.c1, self.c2 = V+A-f-1, A-f-1
        self.d1 = PI/4-self.b1
        self.d2 = self.b2+PI/4*(2*self.b1-PI/4)
        def rot(t, p):
            return p[0]*unit(t)+p[1]*tangent(t)
        k1 = np.array([1-self.a1, .25])
        k2 = k1+rot(f, [-B/2, .25])
        k3 = k2+rot(th, [.5, (1-A-(th-f))/2])
        k4 = np.array([2*k3[0]-k2[0], k2[1]])
        k5 = np.array([2*k3[0]-1+self.a1, .25])
        self.ks = [k1, k2, k3, k4, k5]
        self.phase = [0., f, th, V-th, V-f, V]
        self.breaks = self.phase+[t+V for t in self.phase]+[3*V, 2*PI]
        self.xr = self.path(f)
        self.xl = self.path(V-f)
        self.left = self.path(V)[0]-1
        self.a = 1-2*self.a1
        self.b = self.left+2*self.a1

    def frame(self, t):
        c, s = np.cos(t), np.sin(t)
        if t < self.phi:
            return np.array([self.a1*c-.25*s-1, .25*c+self.a1*s-.5]), np.array([-self.a1*s-.25*c, -.25*s+self.a1*c]), self.ks[0]
        if t < self.theta:
            return np.array([-t*t/4+self.b1*t+self.b2, t/2-self.b1-1]), np.array([-t/2+self.b1, .5]), self.ks[1]
        if t <= V-self.theta:
            return np.array([self.c1-t, self.c2+t]), np.array([-1., 1.]), self.ks[2]
        if t <= V-self.phi:
            return np.array([-t/2+self.d1-1, -t*t/4+self.d1*t+self.d2]), np.array([-.5, -t/2+self.d1]), self.ks[3]
        return np.array([self.a1*c+.25*s-.5, -.25*c+self.a1*s-1]), np.array([-self.a1*s+.25*c, .25*s+self.a1*c]), self.ks[4]

    def path(self, t):
        q, _, k = self.frame(t)
        return q[0]*unit(t)+q[1]*tangent(t)+k

    def support(self, t):
        t = float(t % (2*PI))
        if t <= PI:
            first = t <= V
            s = t if first else t-V
            q, qp, k = self.frame(s)
            if first:
                return float(1+q[0]+k@unit(s)), float(qp[0]+k@tangent(s))
            return float(1+q[1]+k@tangent(s)), float(qp[1]-k@unit(s))
        x = self.left if t < 3*V else 1.
        return float(x*np.cos(t)), float(-x*np.sin(t))

    def tail(self, body, t):
        a = t-PI
        active = (body == 1 and a >= V-self.theta) or (body == 2 and a <= V+self.theta)
        if active:
            h, hp = self.support(a)
            return 1-h, -hp
        x = self.xr if body == 1 else self.xl
        return float(-x@unit(a)), float(-x@tangent(a))

    def measure(self, body, t):
        if body == 1:
            return 1-self.d1+t/2 if t < V-self.phi else .5
        s = t-V
        return .5 if s < self.phi else 1+self.b1-s/2


class Triple:
    def __init__(self, bodies, phi, reference=False):
        self.bodies, self.phi, self.reference = bodies, phi, reference
        self.breaks = []
        for body in bodies:
            self.breaks.extend(body.breaks)
        if reference:
            g = bodies[0]
            self.breaks.extend([PI+V-g.theta, PI+V-g.phi, 3*V+g.phi, 3*V+g.theta])
        self.breaks += [(t-V) % (2*PI) for t in self.breaks.copy()]

    def support(self, body, t):
        if self.reference and body:
            return self.bodies[0].tail(body, t)
        return self.bodies[body].support(t)

    def corner(self, t):
        h, hp = self.support(0, t)
        k, kp = self.support(0, t+V)
        return (h-1)*unit(t)+(k-1)*tangent(t), (hp-k+1)*unit(t)+(h-1+kp)*tangent(t)

    def affine(self):
        f = self.phi
        h = lambda t: self.support(0, t)[0]
        return h(0)+h(PI)+(1+np.tan(f)-1/np.cos(f))*(h(f)+h(PI-f))+integral(lambda t: h(t)+h(t+V), f, V-f, self.breaks)-(1+V-2*f)

    def terms(self):
        f = self.phi
        return [(0, 0., f, V), (0, f, V-f, None),
                (0, V-f, V, PI-f), (0, V, PI, PI),
                (1, PI+f, 3*V, 3*V), (2, 3*V, 2*PI-f, 2*PI-f)]

    def rho(self, body, target, t):
        h, hp = self.support(body, t)
        if target is None:
            return self.support(body, t+V)[0]-hp
        return (self.support(body, target)[0]-np.cos(target-t)*h)/np.sin(target-t)-hp

    def square_sum(self):
        return sum(integral(lambda t: self.rho(body, target, t)**2/2,
                            lo, hi, self.breaks) for body, lo, hi, target in self.terms())

    def q(self):
        return self.affine()-self.square_sum()

    def q_curve(self):
        K, B, D = self.bodies
        f = self.phi
        xr, _ = self.corner(f)
        xl, _ = self.corner(V-f)
        xb, yd = B.face(PI+f, True), D.face(2*PI-f, False)
        core = integral(lambda t: cross(*self.corner(t))/2, f, V-f, self.breaks)
        return K.area()+D.arc_area(3*V, 2*PI-f)+cross(yd, xl)/2-core+cross(xr, xb)/2+B.arc_area(PI+f, 3*V)


def polygon_triple(K, phi):
    h = lambda t: K.support(t)[0]
    W = (h(phi)-1)/np.cos(phi)
    Z = (1-h(PI-phi))/np.cos(phi)
    B = PolygonSupport([[W-np.tan(phi), 1.], [h(0), 0.]])
    D = PolygonSupport([[-h(PI), 0.], [Z+np.tan(phi), 1.]])
    return Triple([K, B, D], phi)


def reference_polygon(g, n=32):
    angles = np.unique(np.r_[np.linspace(0, PI, 2*n+1), g.phi, V-g.phi, V+g.phi, PI-g.phi, 3*V])
    vertices = []
    for a, b in zip(angles, np.r_[angles[1:], 2*PI]):
        vertices.append(np.linalg.solve(np.stack([unit(a), unit(b)]),
                                        [g.support(a)[0], g.support(b)[0]]))
    return PolygonSupport(vertices)


def certificate_check(base, competitor):
    breaks = base.breaks+competitor.breaks
    cross_term, energy = 0., 0.
    for body, lo, hi, target in base.terms():
        delta = lambda t: competitor.rho(body, target, t)-base.rho(body, target, t)
        cross_term += integral(lambda t: base.rho(body, target, t)*delta(t), lo, hi, breaks)
        energy += integral(lambda t: delta(t)**2/2, lo, hi, breaks)
    derivative = competitor.affine()-base.affine()-cross_term
    g = base.bodies[0]
    dual = 0.
    for body, lo, hi in [(1, V-g.theta, V), (2, V, V+g.theta)]:
        dual += integral(lambda t: (competitor.support(0, t)[0]+competitor.support(body, t+PI)[0]-1)*g.measure(body, t), lo, hi, breaks)
    return {'derivative_identity_error': derivative-dual,
            'deficit_identity_error': base.q()-competitor.q()+dual-energy,
            'q': competitor.q(), 'dual_derivative': dual, 'energy': energy}


class CompletionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.g = GerverReference()
        cls.base = Triple([cls.g]*3, cls.g.phi, reference=True)
        cls.rectangle = PolygonSupport([[-1.6, 0.], [1.6, 0.], [1.6, 1.], [-1.6, 1.]])
        cls.poly = reference_polygon(cls.g)
        cls.triples = [polygon_triple(cls.rectangle, cls.g.phi), polygon_triple(cls.poly, cls.g.phi)]
        cls.reports = [certificate_check(cls.base, tr) for tr in cls.triples]

    def test_reference_value(self):
        self.assertAlmostEqual(self.base.q(), 2.21953166887197, places=10)

    def test_analytic_reference_derivatives(self):
        for t in [.02, .3, .72, 1.1, 1.55, 1.8, 2.3, 2.9]:
            e = 1e-6
            diff = (self.g.support(t+e)[0]-self.g.support(t-e)[0])/(2*e)
            self.assertAlmostEqual(self.g.support(t)[1], diff, places=8)

    def test_nonsmooth_cap_area_identity(self):
        for K in [self.rectangle, self.poly]:
            a = integral(lambda t: (K.support(t)[0]**2-K.support(t)[1]**2)/2, 0., PI, K.breaks)
            self.assertAlmostEqual(a, K.area(), places=10)

    def test_independent_curve_area_and_squares(self):
        for tr in self.triples:
            self.assertAlmostEqual(tr.q(), tr.q_curve(), places=9)

    def test_first_variation_certificate(self):
        for report in self.reports:
            self.assertLess(abs(report['derivative_identity_error']), 2e-9)
            self.assertLess(report['dual_derivative'], 1e-10)

    def test_exact_deficit_identity(self):
        for report in self.reports:
            self.assertLess(abs(report['deficit_identity_error']), 2e-9)
            self.assertLess(report['q'], self.base.q()+1e-10)

    def test_curvature_atoms_not_discarded(self):
        normals = [a for a, _, _ in self.rectangle.atoms]
        self.assertTrue(any(abs(a) < 1e-12 for a in normals))
        self.assertTrue(any(abs(a-PI) < 1e-12 for a in normals))
        self.assertTrue(any(abs(a-self.g.phi) < 1e-8 for a, length, _ in self.poly.atoms if length > 1e-8))

    def test_core_monotonicity_for_nonsmooth_nearby_cap(self):
        tr = self.triples[1]
        velocities = [tr.corner(t)[1][0] for t in np.linspace(self.g.phi, V-self.g.phi, 401)]
        self.assertLess(max(velocities), -.01)

    def test_rectangle_not_automatically_in_local_geometric_class(self):
        h, hp = self.rectangle.support(self.g.phi)
        f = self.rectangle.support(self.g.phi+V)[0]-hp
        self.assertLess(f, 1.)

    def test_missing_wedge_height_bound(self):
        for K in [self.rectangle, self.poly]:
            R = max(np.linalg.norm(K.vertices, axis=1))
            tr = polygon_triple(K, self.g.phi)
            for alpha in [.001, .01, .04]:
                for t in np.linspace(V-alpha, V, 41):
                    self.assertLessEqual(tr.corner(t)[0][1], (2*R+1)*alpha+1e-12)

    def test_terminal_rectangle_exclusion(self):
        I = (self.g.left+.15, self.g.a-.15)
        d = self.g.a-I[1]
        for K in [self.poly]:
            for alpha in [.0001, .001, .01]:
                t = V-alpha
                lower = K.support(t)[0]-1
                for x in np.linspace(*I, 11):
                    self.assertLess(np.array([x, alpha*d/4])@unit(t), lower)

    def test_reference_endpoint_height_positivity(self):
        for t in np.r_[np.linspace(1e-6, self.g.phi, 101), np.linspace(V-self.g.phi, V-1e-6, 101)]:
            self.assertGreater(self.g.path(t)[1], 0.)

    def test_endpoint_strip_shortcut_is_false(self):
        alpha = .1
        p = np.array([.5/np.cos(alpha/2), 0.])
        self.assertAlmostEqual(p@unit(alpha/2), .5)
        self.assertAlmostEqual(p@unit(-alpha/2), .5)
        self.assertGreater(2*p@unit(0), 1.)


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(CompletionTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    summary = {'tests_run': result.testsRun, 'failures': len(result.failures),
               'errors': len(result.errors), 'reference_q': CompletionTests.base.q(),
               'nonsmooth_certificates': CompletionTests.reports,
               'arithmetic_certified': False, 'lean_checked': False}
    print(json.dumps(summary, indent=2))
    raise SystemExit(not result.wasSuccessful())
