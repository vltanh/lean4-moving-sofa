#!/usr/bin/env python3
r"""The figures of Chapters 4 and 5, in docs/proof/figures/04-balanced/ and 05-rotation-angle/.

    python3 scripts/figures/fig_balanced.py

A polygon cap and its niche are computed from support values h on the angle domain Θ^◇, as in
Definition 3.3.3 of the paper (`capH`, `nicheH`): the cap 𝓒_Θ(h) is the part of the fan F_ω under
the lines l(s, h(s)), s ∈ Θ^◇, and the niche 𝒩_Θ(h) is the part of F_ω under the union of the
quadrants Q⁻(t) = H₋°(t, h(t) - 1) ∩ H₋°(t + π/2, h(t + π/2) - 1), t ∈ Θ. Every line with a normal
angle s ∈ (0, π) is a graph y = (c - x cos s)/sin s, so the cap, the niche and the polygon sofa
𝓒_Θ(h) \ 𝒩_Θ(h) are regions between piecewise linear functions of x, whose breakpoints are
crossings of the lines; their areas and side lengths are computed exactly from the breakpoints.
Maximum polygon caps are found by numerical optimization of 𝒜_Θ, and checked to be balanced.
"""
import math

import numpy as np
from scipy.optimize import minimize, root

import gerver
from sofa_figures import Figure, OUT, INK, FAINT, WALL, FLOOR, COLORS, FILLS, GREY, sb, sp

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
CH4, CH5 = '04-balanced', '05-rotation-angle'
ORANGE_MID = '#fdba74'   # between FILLS[1] and ORANGE, for a second shade of orange


# ---------------------------------------------------------------------------------------------
# Plane geometry


def uvec(t):
    return (math.cos(t), math.sin(t))


def vvec(t):
    return (-math.sin(t), math.cos(t))


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def add(*ps):
    return (sum(p[0] for p in ps), sum(p[1] for p in ps))


def mul(a, p):
    return (a * p[0], a * p[1])


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def rot(t, p):
    c, s = math.cos(t), math.sin(t)
    return (c * p[0] - s * p[1], s * p[0] + c * p[1])


def clip_halfplane(poly, n, c):
    """The convex polygon `poly` cut by the half-plane p · n ≤ c (Sutherland–Hodgman)."""
    out = []
    for i, p in enumerate(poly):
        q = poly[(i + 1) % len(poly)]
        fp, fq = dot(p, n) - c, dot(q, n) - c
        if fp <= 0:
            out.append(p)
        if fp * fq < 0:
            lam = fp / (fp - fq)
            out.append(add(p, mul(lam, sub(q, p))))
    return out


def polygon_area(poly):
    return 0.5 * sum(p[0] * q[1] - q[0] * p[1] for p, q in zip(poly, poly[1:] + poly[:1]))


def window(f):
    xmax = f.xmin + (f.w - 2 * f.pad) / f.s
    ymin = f.ymax - (f.h - 2 * f.pad) / f.s
    return f.xmin, xmax, ymin, f.ymax


def clip_segment(f, p, q):
    """The part of the segment pq inside the window of the figure (Liang–Barsky), or None."""
    x0, x1, y0, y1 = window(f)
    t0, t1 = 0.0, 1.0
    dx, dy = q[0] - p[0], q[1] - p[1]
    for pp, qq in ((-dx, p[0] - x0), (dx, x1 - p[0]), (-dy, p[1] - y0), (dy, y1 - p[1])):
        if pp == 0:
            if qq < 0:
                return None
            continue
        r = qq / pp
        if pp < 0:
            t0 = max(t0, r)
        else:
            t1 = min(t1, r)
    if t0 > t1:
        return None
    return add(p, mul(t0, (dx, dy))), add(p, mul(t1, (dx, dy)))


def seg(f, p, q, **kw):
    pq = clip_segment(f, p, q)
    if pq:
        f.line(pq[0], pq[1], **kw)


def ray(f, p, d, **kw):
    """The half-line from p in the direction d, clipped to the window."""
    seg(f, p, add(p, mul(100.0, d)), **kw)


def hline(f, y, **kw):
    x0, x1, _, _ = window(f)
    f.line((x0, y), (x1, y), **kw)


# ---------------------------------------------------------------------------------------------
# Polygon caps and niches from support values


class Graph:
    """The line l(s, c) = {p : p · u_s = c}, s ∈ (0, π), as the graph y = a x + b."""

    def __init__(self, s, c, kind, t=None):
        self.s, self.c, self.kind, self.t = s, c, kind, t
        self.a = -math.cos(s) / math.sin(s)
        self.b = c / math.sin(s)

    def y(self, x):
        return self.a * x + self.b


def region_polygons(xs, lo, hi):
    """The polygons {lo(x) ≤ y ≤ hi(x)} of two functions that are linear between the
    breakpoints xs (given by their values there), one for each interval where hi > lo."""
    xs, lo, hi = list(xs), list(lo), list(hi)
    d = [b - a for a, b in zip(lo, hi)]
    # insert the zero crossings of hi - lo
    X, L, H = [], [], []
    for i in range(len(xs)):
        if i > 0 and (d[i - 1] > 1e-13) != (d[i] > 1e-13) and abs(d[i] - d[i - 1]) > 1e-15:
            lam = d[i - 1] / (d[i - 1] - d[i])
            if 0 < lam < 1:
                x = xs[i - 1] + lam * (xs[i] - xs[i - 1])
                yv = lo[i - 1] + lam * (lo[i] - lo[i - 1])
                X.append(x), L.append(yv), H.append(yv)
        X.append(xs[i]), L.append(lo[i]), H.append(hi[i])
    polys, run = [], []
    for x, a, b in zip(X, L, H):
        if b - a > -1e-12:
            run.append((x, a, b))
        else:
            if len(run) > 1:
                polys.append(run)
            run = []
    if len(run) > 1:
        polys.append(run)
    out = []
    for run in polys:
        if max(b - a for _, a, b in run) < 1e-12:
            continue
        poly = [(x, a) for x, a, _ in run] + [(x, b) for x, _, b in reversed(run)]
        out.append(simplify(poly))
    return out


def simplify(poly):
    """Drop repeated and collinear vertices."""
    pts = []
    for p in poly:
        if not pts or abs(p[0] - pts[-1][0]) > 1e-12 or abs(p[1] - pts[-1][1]) > 1e-12:
            pts.append(p)
    changed = True
    while changed and len(pts) > 3:
        changed = False
        for i in range(len(pts)):
            a, b, c = pts[i - 1], pts[i], pts[(i + 1) % len(pts)]
            cross = (b[0] - a[0]) * (c[1] - b[1]) - (b[1] - a[1]) * (c[0] - b[0])
            same = abs(b[0] - a[0]) < 1e-12 and abs(b[1] - a[1]) < 1e-12
            if abs(cross) < 1e-12 or same:
                pts.pop(i)
                changed = True
                break
    return pts


class PolygonSofa:
    """The polygon cap 𝓒_Θ(h), the niche 𝒩_Θ(h) and the polygon sofa 𝓒_Θ(h) \\ 𝒩_Θ(h) of the
    support values h (a dict on Θ^◇) for the angle set Θ with rotation angle ω."""

    def __init__(self, omega, thetas, h):
        self.omega, self.thetas, self.h = omega, sorted(thetas), dict(h)
        self.right = omega > PI / 2 - 1e-12
        self.diamond = sorted(set(self.thetas) | {t + PI / 2 for t in self.thetas}
                              | {omega, PI / 2})
        assert abs(self.h[PI / 2] - 1) < 1e-12 and abs(self.h[omega] - 1) < 1e-12
        # The bottom of the fan F_ω: y ≥ 0 and p · u_ω ≥ 0.
        self.low = [Graph(PI / 2, 0.0, 'floor')]
        if not self.right:
            self.low.append(Graph(omega, 0.0, 'floor'))
        # The top of the cap: p · u_s ≤ h(s), s ∈ Θ^◇.
        self.up = [Graph(s, self.h[s], 'cap') for s in self.diamond]
        # The inner walls b(t) = l(t, h(t) - 1) and d(t) = l(t + π/2, h(t + π/2) - 1).
        self.walls = [(Graph(t, self.h[t] - 1, 'b', t),
                       Graph(t + PI / 2, self.h[t + PI / 2] - 1, 'd', t)) for t in self.thetas]
        graphs = self.low + self.up + [g for w in self.walls for g in w]
        A = np.array([g.a for g in graphs])
        B = np.array([g.b for g in graphs])
        with np.errstate(divide='ignore', invalid='ignore'):
            X = (B[None, :] - B[:, None]) / (A[:, None] - A[None, :])
        X = X[np.isfinite(X)]
        self.xs = np.unique(X[np.abs(X) < 60])
        self.A_low, self.B_low = A[:len(self.low)], B[:len(self.low)]
        k = len(self.low)
        self.A_up, self.B_up = A[k:k + len(self.up)], B[k:k + len(self.up)]
        self.A_b = np.array([w[0].a for w in self.walls])
        self.B_b = np.array([w[0].b for w in self.walls])
        self.A_d = np.array([w[1].a for w in self.walls])
        self.B_d = np.array([w[1].b for w in self.walls])

    # The boundary functions: the cap is L ≤ y ≤ U, the niche L ≤ y < N, and the polygon sofa
    # G ≤ y ≤ U with G = max(L, N), the polyline.
    def L(self, x):
        x = np.atleast_1d(x)
        return np.max(self.A_low[:, None] * x + self.B_low[:, None], axis=0)

    def U(self, x):
        x = np.atleast_1d(x)
        return np.min(self.A_up[:, None] * x + self.B_up[:, None], axis=0)

    def N(self, x):
        x = np.atleast_1d(x)
        b = self.A_b[:, None] * x + self.B_b[:, None]
        d = self.A_d[:, None] * x + self.B_d[:, None]
        return np.max(np.minimum(b, d), axis=0)

    def G(self, x):
        return np.maximum(self.L(x), self.N(x))

    @staticmethod
    def int_pos(xs, f):
        """∫ max(f, 0) dx for f linear between the breakpoints xs."""
        x0, x1, f0, f1 = xs[:-1], xs[1:], f[:-1], f[1:]
        dx = x1 - x0
        tot = np.sum(((f0 + f1) / 2 * dx)[(f0 >= 0) & (f1 >= 0)])
        m1, m2 = (f0 > 0) & (f1 < 0), (f0 < 0) & (f1 > 0)
        tot += np.sum((f0[m1] ** 2 / (f0[m1] - f1[m1]) * dx[m1] / 2))
        tot += np.sum((f1[m2] ** 2 / (f1[m2] - f0[m2]) * dx[m2] / 2))
        return float(tot)

    def area_cap(self):
        return self.int_pos(self.xs, self.U(self.xs) - self.L(self.xs))

    def area_niche(self):
        return self.int_pos(self.xs, self.N(self.xs) - self.L(self.xs))

    def area_sofa(self):
        return self.int_pos(self.xs, self.U(self.xs) - self.G(self.xs))

    def functional(self):
        """𝒜_Θ(h) = |𝓒_Θ(h)| - |𝒩_Θ(h)| (Definition 3.3.3)."""
        return self.area_cap() - self.area_niche()

    def niche_outside_cap(self):
        """|𝒩_Θ(h) \\ 𝓒_Θ(h)|: the niche lies below N and the cap below U, both above L."""
        xs = self.xs
        top = self.N(xs)
        return self.int_pos(xs, top - np.maximum(self.U(xs), self.L(xs)))

    # Polygons, for drawing.
    def cap_polygon(self):
        if getattr(self, '_cap', None) is None:
            self._cap = self._cap_polygon()
        return self._cap

    def _cap_polygon(self):
        R = 60.0
        poly = [(-R, -R), (R, -R), (R, R), (-R, R)]
        poly = clip_halfplane(poly, (0.0, -1.0), 0.0)
        if not self.right:
            poly = clip_halfplane(poly, mul(-1, uvec(self.omega)), 0.0)
        for s in self.diamond:
            poly = clip_halfplane(poly, uvec(s), self.h[s])
        return simplify(poly)

    def niche_polygons(self):
        return region_polygons(self.xs, self.L(self.xs), self.N(self.xs))

    def sofa_polygons(self):
        return region_polygons(self.xs, self.G(self.xs), self.U(self.xs))

    def inner_corner(self, t):
        """𝐱(t) = (h(t) - 1) u_t + (h(t + π/2) - 1) v_t."""
        return add(mul(self.h[t] - 1, uvec(t)), mul(self.h[t + PI / 2] - 1, vvec(t)))

    def corner_points(self):
        """C_K⁺(ω) and A_K⁻(0): the ends of the bottom of the cap."""
        poly = self.cap_polygon()
        xa = max(p[0] for p in poly if abs(p[1]) < 1e-9)
        if self.right:
            xc = min(p[0] for p in poly if abs(p[1]) < 1e-9)
        else:
            xc = min(p[0] for p in poly if abs(dot(p, uvec(self.omega))) < 1e-9)
        return (xc, float(self.L(xc)[0])), (xa, 0.0)

    def sigma(self, s):
        """σ_K(s): the length of the side of the cap with outer normal u_s."""
        poly = self.cap_polygon()
        hs = max(dot(p, uvec(s)) for p in poly)
        ds = [dot(p, vvec(s)) for p in poly if dot(p, uvec(s)) > hs - 1e-9]
        return max(ds) - min(ds)

    def polyline_pieces(self):
        if getattr(self, '_pieces', None) is None:
            self._pieces = self._polyline_pieces()
        return self._pieces

    def _polyline_pieces(self):
        """The pieces of the polyline 𝐩_K (the graph of G between C_K⁺(ω) and A_K⁻(0)), each
        with the normal angle of its line: [(x0, x1, s)], merged when consecutive."""
        (xc, _), (xa, _) = self.corner_points()
        xs = [xc] + [x for x in self.xs if xc + 1e-12 < x < xa - 1e-12] + [xa]
        pieces = []
        for x0, x1 in zip(xs[:-1], xs[1:]):
            xm = (x0 + x1) / 2
            g = float(self.G(xm)[0])
            s = None
            for gr in self.low:
                if abs(gr.y(xm) - g) < 1e-9:
                    s = gr.s
            if s is None:
                for b, d in self.walls:
                    m = min(b.y(xm), d.y(xm))
                    if abs(m - g) < 1e-9:
                        s = b.s if b.y(xm) <= d.y(xm) else d.s
            assert s is not None
            if pieces and abs(pieces[-1][2] - s) < 1e-12 and abs(pieces[-1][1] - x0) < 1e-12:
                pieces[-1] = (pieces[-1][0], x1, s)
            else:
                pieces.append((x0, x1, s))
        return pieces

    def tau(self, s):
        """τ_K(s): the total length of the pieces of the polyline with normal angle s."""
        return sum((x1 - x0) / math.sin(s0) for x0, x1, s0 in self.polyline_pieces()
                   if abs(s0 - s) < 1e-12)

    def point(self, x, f):
        return (x, float(f(x)[0]))

    def shifted(self, a):
        """The same configuration translated by (a, 0): h(s) ↦ h(s) + a cos s."""
        return PolygonSofa(self.omega, self.thetas,
                           {s: v + a * math.cos(s) for s, v in self.h.items()})

    def tightened(self):
        """The support values h_K of the cap K = 𝓒_Θ(h) itself."""
        poly = self.cap_polygon()
        return PolygonSofa(self.omega, self.thetas,
                           {s: max(dot(p, uvec(s)) for p in poly) for s in self.diamond})

    def is_balanced(self, tol=1e-6):
        return all(abs(self.sigma(s) - self.tau(s)) < tol for s in self.diamond)


def config(omega, thetas, values):
    """The configuration with h(ω) = h(π/2) = 1 and the given values on Θ ∪ (Θ + π/2)."""
    free = sorted(thetas) + sorted(t + PI / 2 for t in thetas)
    h = {PI / 2: 1.0, omega: 1.0}
    h.update(zip(free, values))
    return PolygonSofa(omega, thetas, h)


def maximize(omega, thetas, starts):
    """A maximum polygon cap: the best of local maximizations of 𝒜_Θ from the given starts,
    polished by solving the balance equations σ(s) = τ(s), s ∈ Θ ∪ (Θ + π/2): by Lemma 3.4.7
    they say that the gradient of 𝒜_Θ vanishes."""
    best = None
    for x0 in starts:
        x = np.array(x0, float)
        for _ in range(3):
            r = minimize(lambda v: -config(omega, thetas, v).functional(), x, method='L-BFGS-B',
                         options={'maxiter': 5000, 'ftol': 1e-15, 'gtol': 1e-11})
            x = r.x
        if best is None or r.fun < best.fun - 1e-12:
            best = r
    free = sorted(thetas) + sorted(t + PI / 2 for t in thetas)
    # For ω = π/2 the horizontal translations leave 𝒜_Θ unchanged: fix the first value. The
    # remaining balance equations then imply the others (Lemma 3.4.6: Σ (τ - σ)(s) v_s = 0).
    k = 1 if omega > PI / 2 - 1e-12 else 0

    def values(w):
        return np.concatenate([best.x[:k], w])

    def imbalance(w):
        ps = config(omega, thetas, values(w))
        return [ps.sigma(s) - ps.tau(s) for s in free[k:]]

    sol = root(imbalance, best.x[k:], method='hybr', options={'xtol': 1e-14})
    x = values(sol.x) if max(map(abs, imbalance(sol.x))) < 1e-10 else best.x
    assert config(omega, thetas, x).functional() > -best.fun - 1e-9
    return config(omega, thetas, x).tightened()


def maximize_random(omega, thetas, n_starts=12, seed=1):
    rng = np.random.default_rng(seed)
    k = 2 * len(thetas)
    return maximize(omega, thetas, [1 + rng.uniform(0, 1.2, k) for _ in range(n_starts)])


def centred(ps):
    """A polygon sofa with ω = π/2, translated so that its top side is centred on x = 0."""
    poly = ps.cap_polygon()
    top = [p[0] for p in poly if abs(p[1] - 1) < 1e-9]
    return ps.shifted(-(min(top) + max(top)) / 2)


def check_maximum(ps, name):
    """The facts the captions state about a maximum polygon cap: it is balanced (Theorem 3.4.9),
    contains its niche (Theorem 3.4.10), and its sofa has area 𝒜_Θ(K)."""
    assert ps.is_balanced(), name
    assert ps.niche_outside_cap() < 1e-9, name
    assert abs(ps.area_sofa() - ps.functional()) < 1e-9, name


# ---------------------------------------------------------------------------------------------
# Drawing helpers


def draw_sofa(f, ps, fill=FILLS[0], stroke=BLUE, width=1.8, opacity=1.0):
    for poly in ps.sofa_polygons():
        f.polygon(poly, fill=fill, stroke=stroke, width=width, opacity=opacity)


def draw_hallway_walls(f, x, t, color, width=1.6, dash=None):
    """The walls of the hallway 𝐱 + R_t L: the outer walls through 𝐲 = 𝐱 + u_t + v_t and the
    inner walls, the half-lines from 𝐱 in the directions -v_t and -u_t."""
    u, v = uvec(t), vvec(t)
    y = add(x, u, v)
    ray(f, y, mul(-1, v), stroke=color, width=width, dash=dash)
    ray(f, y, mul(-1, u), stroke=color, width=width, dash=dash)
    ray(f, x, mul(-1, v), stroke=color, width=width, dash=dash)
    ray(f, x, mul(-1, u), stroke=color, width=width, dash=dash)


def label(f, p, text, size=15, color=INK, **kw):
    f.text(p, text, size=size, color=color, **kw)


# ---------------------------------------------------------------------------------------------
# The examples

TWO = [PI / 6, PI / 3]


def gerver_example(c):
    """Gerver's balancing argument breaking connectedness (Baek's overview, §1.4): Θ = {π/6, π/3},
    ω = π/2, 𝐱(π/6) = (0, 1) - c u with u = u_{π/6}, and 𝐱(π/3) = (-0.9, 0.98)."""
    t1, t2 = TWO
    x1 = sub((0.0, 1.0), mul(c, uvec(t1)))
    x2 = (-0.9, 0.98)
    h = {PI / 2: 1.0, t1: dot(x1, uvec(t1)) + 1, t1 + PI / 2: dot(x1, vvec(t1)) + 1,
         t2: dot(x2, uvec(t2)) + 1, t2 + PI / 2: dot(x2, vvec(t2)) + 1}
    return PolygonSofa(PI / 2, TWO, h)


def max_two():
    """The maximum polygon cap for Θ = {π/6, π/3}, ω = π/2, centred."""
    ps = centred(maximize_random(PI / 2, TWO))
    check_maximum(ps, 'two angles')
    return ps


def max_small():
    """The maximum polygon cap for ω = 1.2 and the uniform angle set Θ = {0.4, 0.8}."""
    ps = maximize_random(1.2, [0.4, 0.8])
    check_maximum(ps, 'omega = 1.2')
    return ps


def dyadic(ns=(2, 4, 8, 16)):
    """Maximum polygon caps for the uniform angle sets Θ_{π/2, n}, each found from the previous
    one (its support values on the new angle set)."""
    out, prev = {}, None
    for n in ns:
        thetas = [i * PI / 2 / n for i in range(1, n)]
        free = sorted(thetas) + sorted(t + PI / 2 for t in thetas)
        if prev is None:
            starts = [np.full(len(free), 1.6), np.full(len(free), 1.3)]
        else:
            poly = prev.cap_polygon()
            starts = [[max(dot(p, uvec(s)) for p in poly) for s in free]]
        ps = centred(maximize(PI / 2, thetas, starts))
        check_maximum(ps, f'n = {n}')
        out[n] = ps
        prev = ps
    return out




def lower_sides(ps, s):
    """The sides of the polygon sofa on its lower boundary (the polyline, where it is not above
    the top of the cap) whose line has the normal angle s, as segments."""
    out = []
    for x0, x1, s0 in ps.polyline_pieces():
        if abs(s0 - s) > 1e-12:
            continue
        d0 = float(ps.U(x0)[0] - ps.G(x0)[0])
        d1 = float(ps.U(x1)[0] - ps.G(x1)[0])
        if d0 < -1e-12 and d1 < -1e-12:
            continue
        a, b = x0, x1
        if d0 < -1e-12 or d1 < -1e-12:
            xz = x0 + d0 / (d0 - d1) * (x1 - x0)
            a, b = (xz, x1) if d0 < -1e-12 else (x0, xz)
        out.append((ps.point(a, ps.G), ps.point(b, ps.G)))
    return out


def upper_side(ps, s):
    """The side of the cap with outer normal u_s, as a segment."""
    poly = ps.cap_polygon()
    hs = max(dot(p, uvec(s)) for p in poly)
    pts = sorted((p for p in poly if dot(p, uvec(s)) > hs - 1e-9), key=lambda p: dot(p, vvec(s)))
    return pts[0], pts[-1]


def line_band(f, s, c, y0, y1, **kw):
    """The line l(s, c), s ∈ (0, π/2], between the heights y0 and y1."""
    def x_at(y):
        return (c - y * math.sin(s)) / math.cos(s)
    f.line((x_at(y0), y0), (x_at(y1), y1), **kw)


# ---------------------------------------------------------------------------------------------
# Chapter 4


def fig_polygon_sofa(ps):
    """S_Θ = H ∩ V_ω ∩ L_{π/6} ∩ L_{π/3} for the maximum polygon cap, ω = π/2 (so V_ω = H)."""
    f = Figure(-2.9, 2.9, -1.05, 2.45, 112)
    hline(f, 0, stroke=WALL, width=2.4)
    hline(f, 1, stroke=WALL, width=2.4)
    draw_sofa(f, ps)
    for t, color, name, dx in zip(TWO, (GREEN, PURPLE), ('π/6', 'π/3'), (1, -1)):
        x = ps.inner_corner(t)
        draw_hallway_walls(f, x, t, color, width=1.5)
        f.dot(x, r=3.4, fill=color)
        y = add(x, uvec(t), vvec(t))
        f.dot(y, r=3.0, fill=color)
        label(f, add(y, (0.45 * dx, 0.1)), sb('L', name), color=color, size=17)
        label(f, add(x, (0.0, -0.36)), f'x({name})', color=color, size=14)
    label(f, (-2.55, 0.5), 'H', size=17, color=WALL)
    label(f, (-1.35, 0.42), sb('S', 'Θ'), size=17, color=BLUE)
    # The facts of the caption: S_Θ lies in H and in both hallways; its area is 2.5154.
    assert abs(ps.area_sofa() - 2.5154) < 5e-5
    for poly in ps.sofa_polygons():
        for p in poly:
            assert -1e-9 <= p[1] <= 1 + 1e-9
            for t in TWO:
                X = dot(sub(p, ps.inner_corner(t)), uvec(t))
                Y = dot(sub(p, ps.inner_corner(t)), vvec(t))
                assert X <= 1 + 1e-9 and Y <= 1 + 1e-9 and (X >= -1e-9 or Y >= -1e-9)
    return f.save(f'{CH4}/polygon-sofa',
                  'The polygon sofa S_Θ for Θ = {π/6, π/3} and ω = π/2, in blue: the part of the '
                  'horizontal strip H between the grey lines that lies in both hallways L_{π/6} '
                  '(green walls) and L_{π/3} (purple walls), whose inner corners x(π/6) and x(π/3) '
                  'are marked; it is the maximum polygon sofa for this angle set')


def fig_balancing_move():
    """The balancing move on Gerver's example: L_{π/6} pushed by ε u from c = 0.1 to c = 0."""
    t, eps = PI / 6, 0.1
    before, after = gerver_example(0.1), gerver_example(0.1 - eps)
    f = Figure(-2.85, 2.2, -0.45, 1.5, 125)
    hline(f, 0, stroke=WALL, width=2.0)
    hline(f, 1, stroke=WALL, width=2.0)
    xs = np.union1d(before.xs, after.xs)
    xs = xs[np.abs(xs) < 10]
    # The sofa gains the points above its old top and loses those below its new bottom.
    gain = region_polygons(xs, np.maximum(after.G(xs), before.U(xs)), after.U(xs))
    lose = region_polygons(xs, before.G(xs), np.minimum(after.G(xs), before.U(xs)))
    draw_sofa(f, before)
    for poly in gain:
        f.polygon(poly, fill=FILLS[2], stroke=GREEN, width=0.8)
    for poly in lose:
        f.polygon(poly, fill=FILLS[1], stroke=ORANGE, width=0.8)
    for ps, dash in ((before, None), (after, '5 4')):
        line_band(f, t, ps.h[t], -0.3, 1.3, stroke=GREEN, width=1.0, dash=dash)
        line_band(f, t, ps.h[t] - 1, -0.3, 1.3, stroke=ORANGE, width=1.0, dash=dash)
    a0, a1 = upper_side(before, t)
    f.line(a0, a1, stroke=GREEN, width=4.0)
    for p, q in lower_sides(before, t):
        f.line(p, q, stroke=ORANGE, width=4.0)
    m = mul(0.5, add(a0, a1))
    f.line(add(m, mul(0.08, uvec(t))), add(m, mul(0.5, uvec(t))), stroke=INK, width=1.4,
           arrow=True)
    label(f, add(m, mul(0.62, uvec(t)), (0.06, 0.0)), 'εu', size=15)
    label(f, add(m, mul(-0.3, uvec(t))), sp('s', '+'), size=17, color=GREEN)
    p, q = lower_sides(before, t)[0]
    label(f, add(mul(0.5, add(p, q)), mul(-0.27, uvec(t))), sp('s', '−'), size=17, color=ORANGE)
    label(f, (-1.75, 0.55), sb('S', 'Θ'), size=17, color=BLUE)
    s_plus, s_minus = before.sigma(t), before.tau(t)
    assert abs(s_plus - 1.1547) < 5e-5 and abs(s_minus - 0.7614) < 5e-5
    assert abs(sum(math.dist(p, q) for p, q in lower_sides(before, t)) - s_minus) < 1e-9
    assert s_plus > s_minus + 0.3 and after.area_sofa() > before.area_sofa()
    # The first-order change of the area is (s⁺ - s⁻) ε (Theorem 3.1.2, Lemma 3.4.7).
    delta = 1e-6
    slope = (gerver_example(0.1 - delta).area_sofa() - before.area_sofa()) / delta
    assert abs(slope - (s_plus - s_minus)) < 1e-4, (slope, s_plus, s_minus)
    path = f.save(f'{CH4}/balancing-move',
                  'The balancing move: a polygon sofa whose side s+ on the outer wall of the '
                  'hallway L_{π/6} (thick green) is longer than its sides s− on the inner wall '
                  '(thick orange). Pushing the hallway outwards by ε, to the dashed walls, gains '
                  'the green strip and loses the orange one')
    return path, s_plus, s_minus, after.area_sofa() - before.area_sofa()


def fig_disconnect(cs=(0.1, 0.0, -0.2)):
    """Gerver's example: as c decreases, S_Θ is cut through by the quadrant Q⁻(π/6)."""
    t = PI / 6
    hgt = 1.62
    f = Figure(-2.85, 2.2, -0.3 - hgt * (len(cs) - 1), 1.42, 118)
    x0, x1, _, _ = window(f)
    for k, c in enumerate(cs):
        dy = -hgt * k
        ps = gerver_example(c)

        def shift(pts, dy=dy):
            return [(x, y + dy) for x, y in pts]

        f.line((x0, dy), (x1, dy), stroke=WALL, width=1.8)
        f.line((x0, 1 + dy), (x1, 1 + dy), stroke=WALL, width=1.8)
        R = 9.0
        Q = [(-R, 0.0), (R, 0.0), (R, 1.0), (-R, 1.0)]
        Q = clip_halfplane(Q, uvec(t), ps.h[t] - 1)
        Q = clip_halfplane(Q, vvec(t), ps.h[t + PI / 2] - 1)
        f.polygon(shift(Q), fill=FILLS[1], stroke='none', width=0)
        for poly in ps.sofa_polygons():
            f.polygon(shift(poly), fill=FILLS[0], stroke=BLUE, width=1.6)
        f.line(*shift(upper_side(ps, t)), stroke=GREEN, width=3.6)
        for p, q in lower_sides(ps, t):
            f.line(*shift([p, q]), stroke=ORANGE, width=3.6)
        x = ps.inner_corner(t)
        for d in (mul(-1, vvec(t)), mul(-1, uvec(t))):
            f.line(*shift([x, add(x, mul(0.6, d))]), stroke=ORANGE, width=1.1, dash='4 3')
        f.dot(shift([x])[0], r=3.2, fill=ORANGE)
        label(f, (-2.75, 1.24 + dy), f'c = {c:g}'.replace('-', '−'), size=15, anchor='start',
              italic=False)
        parts = ps.sofa_polygons()
        assert len(parts) == (1 if c >= 0 else 2), c
        if c < 0:
            assert x[1] > 1
    # For every c ∈ [0, 0.1] the side on a(π/6) is longer than the sides on b(π/6).
    for c in np.linspace(0, 0.1, 21):
        ps = gerver_example(c)
        assert ps.sigma(t) > ps.tau(t) + 0.1, c
    return f.save(f'{CH4}/disconnect',
                  "Gerver's balancing argument breaking connectedness, in three rows for c = 0.1, 0 "
                  'and −0.2: the hallway L_{π/6} is pushed along u, its inner corner (orange dot) '
                  'rises to the line y = 1 and beyond, and the quadrant below it (light orange) '
                  'cuts the polygon sofa into two pieces')


def fig_cap_niche(ps):
    """The polygon cap and the polygon niche for ω = 1.2, Θ = {0.4, 0.8}."""
    w = ps.omega
    f = Figure(-2.75, 2.95, -0.4, 1.5, 118)
    P = [(0.0, 0.0), (1 / math.cos(w), 0.0), (math.tan(PI / 4 - w / 2), 1.0), (-math.tan(w), 1.0)]
    f.polygon(P, fill='none', stroke=FAINT, width=1.2, dash='5 4')
    ray(f, (0.0, 0.0), (1.0, 0.0), stroke=WALL, width=2.2)
    ray(f, (0.0, 0.0), vvec(w), stroke=WALL, width=2.2)
    K = ps.cap_polygon()
    f.polygon(K, fill=FILLS[0], stroke=BLUE, width=1.8)
    for poly in ps.niche_polygons():
        f.polygon(poly, fill=FILLS[1], stroke=ORANGE, width=1.6)
    for t in ps.thetas:
        x = ps.inner_corner(t)
        for d in (mul(-1, vvec(t)), mul(-1, uvec(t))):
            # The wall of the quadrant Q⁻(t), until it leaves the fan.
            lam = min(l for l in (-x[1] / d[1] if d[1] < 0 else math.inf,
                                  -dot(x, uvec(w)) / dot(d, uvec(w)) if dot(d, uvec(w)) < 0
                                  else math.inf))
            f.line(x, add(x, mul(lam, d)), stroke=ORANGE, width=1.0, dash='4 3')
        f.dot(x, r=3.2, fill=ORANGE)
    xa, xb = ps.inner_corner(0.4), ps.inner_corner(0.8)
    label(f, add(xa, (0.36, 0.13)), sb('x', 'K', '(0.4)'), size=14, color=ORANGE)
    label(f, add(xb, (-0.36, 0.14)), sb('x', 'K', '(0.8)'), size=14, color=ORANGE)
    f.dot((0.0, 0.0), r=3.0)
    label(f, (0.0, -0.2), 'O', size=14)
    o = (math.tan(PI / 4 - w / 2), 1.0)
    f.dot(o, r=3.0)
    label(f, add(o, (0.12, 0.17)), sb('o', 'ω'), size=15)
    label(f, (0.95, 0.72), 'K', size=18, color=BLUE)
    label(f, (2.35, 0.18), sb('P', 'ω'), size=16, color=FAINT)
    label(f, (2.45, 1.2), sb('F', 'ω'), size=16, color=WALL)
    # Facts: K ⊆ P_ω, the niche is the union of the two wedges, inside K (Theorem 3.4.10).
    for p in K:
        assert -1e-9 <= p[1] <= 1 + 1e-9 and -1e-9 <= dot(p, uvec(w)) <= 1 + 1e-9
    assert ps.niche_outside_cap() < 1e-9
    return f.save(f'{CH4}/cap-niche',
                  'A polygon cap K with rotation angle ω = 1.2 and angle set Θ = {0.4, 0.8}, in '
                  'blue, inside the dashed parallelogram P_ω; its polygon niche, in orange, is the '
                  'part of the fan F_ω (above the two dark half-lines from O) inside the quadrants '
                  'below the inner corners x_K(0.4) and x_K(0.8)')


def fig_fan(d=8.0):
    """REPORT.md, E6: the polygon niche needs the fan F_ω, not the parallelogram P_ω."""
    t = PI / 4
    h = {PI / 2: 1.0, t: (d + 1) / math.sqrt(2), t + PI / 2: 1 / math.sqrt(2)}
    ps = PolygonSofa(PI / 2, [t], h)
    f = Figure(-1.35, d + 1.45, -0.35, d / 2 + 1 - math.sqrt(2) + 0.6, 62)
    hline(f, 0, stroke=WALL, width=2.0)
    hline(f, 1, stroke=WALL, width=1.4, dash='6 4')
    K = ps.cap_polygon()
    f.polygon(K, fill=FILLS[0], stroke=BLUE, width=1.8)
    (T,) = ps.niche_polygons()
    low = clip_halfplane(T, (0.0, 1.0), 1.0)
    high = clip_halfplane(T, (0.0, -1.0), -1.0)
    f.polygon(high, fill=FILLS[1], stroke=ORANGE, width=1.4, dash='5 4')
    f.polygon(low, fill=ORANGE_MID, stroke=ORANGE, width=1.6)
    x = ps.inner_corner(t)
    f.dot(x, r=3.4, fill=ORANGE)
    label(f, add(x, (0.0, 0.27)), sb('x', 'K', '(π/4)'), size=15, color=ORANGE)
    label(f, (0.6, 0.62), 'K', size=17, color=BLUE)
    label(f, (-0.85, 1.25), sb('P', 'ω'), size=15, color=WALL)
    # The numbers of the caption.
    r2 = math.sqrt(2)
    assert abs(polygon_area(K) - (d + 1)) < 1e-9
    assert abs(polygon_area(T) - (d / 2 + 1 - r2) ** 2) < 1e-9
    assert abs(polygon_area(low) - (d + 1 - 2 * r2)) < 1e-9
    assert abs(x[0] - d / 2) < 1e-9 and abs(x[1] - (d / 2 + 1 - r2)) < 1e-9
    return f.save(f'{CH4}/fan',
                  'A long polygon cap K for Θ = {π/4} and ω = π/2, the trapezoid between the '
                  f'lines y = 0 and y = 1 with sides x = y − 1 and x = {d + 1:g} − y, in blue, and '
                  'its wedge below the inner corner '
                  'x_K(π/4), in orange: the polygon niche is the whole wedge, in the fan y ≥ 0; '
                  'the parallelogram P_ω, the strip below the dashed line, keeps only its darker '
                  'lower part')


def fig_balanced(ps):
    """Balanced side lengths: each upper side of the cap and the pieces of the polyline with the
    same normal angle have the same colour and the same total length."""
    w = ps.omega
    f = Figure(-2.6, 2.75, -0.45, 1.5, 150)
    colour = dict(zip(ps.diamond, (COLORS[0], COLORS[1], COLORS[2], COLORS[3], COLORS[4],
                                   COLORS[5])))
    for poly in ps.sofa_polygons():
        f.polygon(poly, fill=FLOOR, stroke='none', width=0)
    C, A = ps.corner_points()
    ray(f, C, vvec(w), stroke=FAINT, width=1.6, dash='5 4')
    ray(f, A, (1.0, 0.0), stroke=FAINT, width=1.6, dash='5 4')
    names = {}
    for i, s in enumerate(ps.diamond):
        names[s] = str(i + 1)
        p, q = upper_side(ps, s)
        f.line(p, q, stroke=colour[s], width=4.2)
        m = add(mul(0.5, add(p, q)), mul(0.2, uvec(s)))
        label(f, m, sb('σ', names[s]), size=16, color=colour[s])
    # The labels of the inner pieces go above or below them, alternately, to avoid crowding.
    pieces = ps.polyline_pieces()
    for i, (x0, x1, s) in enumerate(pieces):
        p, q = ps.point(x0, ps.G), ps.point(x1, ps.G)
        f.line(p, q, stroke=colour[s], width=4.2)
        side = 1 if 0 < i < len(pieces) - 1 and i % 2 == 1 else -1
        m = add(mul(0.5, add(p, q)), mul(0.19 * side, uvec(s)))
        label(f, m, sb('τ', names[s]), size=16, color=colour[s])
        assert abs(math.dist(p, q) - ps.sigma(s)) < 1e-9
    f.dot(C, r=3.6)
    f.dot(A, r=3.6)
    label(f, add(C, (-0.12, -0.22)), sp('C', '+', '', size=14), size=14)
    label(f, add(A, (0.0, -0.22)), sp('A', '−', '', size=14), size=14)
    assert ps.is_balanced(1e-9)
    return f.save(f'{CH4}/balanced',
                  'A balanced polygon cap for ω = 1.2 and Θ = {0.4, 0.8}: its upper sides σ1 to '
                  'σ6, with the normal angles 0.4, 0.8, ω, π/2, 0.4 + π/2 and 0.8 + π/2, and the '
                  'pieces τ1 to τ6 of the polyline from C to A below the sofa, coloured by their '
                  'normal angle; sides of the same colour have the same length')


def fig_limit(caps, ns=(4, 8, 16)):
    """The maximum polygon sofas for Θ_{π/2, n} approach Gerver's sofa."""
    g = gerver.outline(500, 6000)
    gx = [p[0] for p in g]
    g = [(x - (min(gx) + max(gx)) / 2, y) for x, y in g]
    hgt = 1.45
    f = Figure(-2.3, 2.3, -0.25 - hgt * (len(ns) - 1), 1.35, 112)
    x0, x1, _, _ = window(f)
    for k, n in enumerate(ns):
        dy = -hgt * k
        ps = caps[n]
        f.line((x0, dy), (x1, dy), stroke=FAINT, width=1.0)
        f.line((x0, 1 + dy), (x1, 1 + dy), stroke=FAINT, width=1.0)
        for poly in ps.sofa_polygons():
            f.polygon([(x, y + dy) for x, y in poly], fill=FILLS[0], stroke=BLUE, width=1.6)
        f.polygon([(x, y + dy) for x, y in g], fill='none', stroke=INK, width=1.2, dash='5 3')
        label(f, (-2.25, 1.2 + dy), f'n = {n}', size=15, anchor='start', italic=False)
    vals = [caps[n].functional() for n in ns]
    assert all(a > b for a, b in zip(vals, vals[1:])) and vals[-1] > 2.2195
    # The values and the balance quoted in the caption.
    for n, v in zip(ns, (2.4148, 2.3027, 2.2584)):
        assert abs(caps[n].functional() - v) < 5e-5 and caps[n].is_balanced(1e-12), n
    return f.save(f'{CH4}/limit',
                  "The maximum polygon sofas for the uniform angle sets with n = 4, 8 and 16 "
                  "intervals and ω = π/2, in blue, each with the outline of Gerver's sofa, dashed, "
                  'centred on the same vertical line; they approach it as n grows')


# ---------------------------------------------------------------------------------------------
# Chapter 5

ARCSEC22 = math.acos(1 / 2.2)     # sec⁻¹(2.2)
ARCTAN22 = math.atan(2.2)         # tan⁻¹(2.2)


def c_omega(w):
    """c_ω = tan((π/2 - ω)/2) = sec ω - tan ω (Proposition 4.2.1)."""
    return math.tan((PI / 2 - w) / 2)


def d_min(w):
    return 1.25 if w < ARCTAN22 else 1.1


def para(w):
    """The parallelogram P_ω: O, (sec ω, 0), o_ω, (-tan ω, 1)."""
    return [(0.0, 0.0), (1 / math.cos(w), 0.0), (math.tan(PI / 4 - w / 2), 1.0), (-math.tan(w), 1.0)]


def pentagon(w):
    """P_ω \\ Δ_ω: the parallelogram without the triangle O, c_ω u_0, c_ω v_ω."""
    c = c_omega(w)
    P = para(w)
    return [(c, 0.0), P[1], P[2], P[3], mul(c, vvec(w))]


def fig_two_bounds(w=1.0):
    """Theorem 1.5.1: the strip H meets a hallway turned by π/4 in area √2, and a translate of
    V_ω in a parallelogram of area sec ω."""
    f = Figure(-2.35, 7.25, -0.95, 1.95, 74)
    gap = 5.0
    # Left: the hallway x' + R_{-π/4} L with inner corner x' = (0, 0.3).
    xc = (0.0, 0.3)
    t = -PI / 4
    u, v = uvec(t), vvec(t)
    box = [(-2.3, 0.0), (2.3, 0.0), (2.3, 1.0), (-2.3, 1.0)]
    # H ∩ L' = (H ∩ Q⁺) minus (H ∩ Q⁻), drawn as the region between two polylines in x.
    xs = np.linspace(-2.3, 2.3, 4601)

    def in_L(p):
        X, Y = dot(sub(p, xc), u), dot(sub(p, xc), v)
        return X <= 1 + 1e-12 and Y <= 1 + 1e-12 and (X >= -1e-12 or Y >= -1e-12)

    # The slices of H ∩ L' are segments of length √2: draw the region by its slices' ends.
    ys = np.linspace(0, 1, 401)
    left, right = [], []
    for y in ys:
        pts = [x for x in xs if in_L((x, y))]
        left.append((min(pts), y))
        right.append((max(pts), y))
        assert abs(max(pts) - min(pts) - math.sqrt(2)) < 2e-3
    f.polygon(left + right[::-1], fill=FILLS[0], stroke=BLUE, width=1.6)
    for x0 in (-2.3,):
        f.line((x0, 0), (2.3, 0), stroke=WALL, width=2.2)
        f.line((x0, 1), (2.3, 1), stroke=WALL, width=2.2)
    draw_hallway_walls(f, xc, t, GREEN, width=1.5)
    yv = 0.78
    a = [p for p in left if abs(p[1] - yv) < 1.5e-3][0]
    b = [p for p in right if abs(p[1] - yv) < 1.5e-3][0]
    f.line(a, b, stroke=INK, width=1.3)
    f.dot(a, r=2.6)
    f.dot(b, r=2.6)
    label(f, add(mul(0.5, add(a, b)), (0.0, 0.15)), '√2', size=15, italic=False)
    label(f, (-1.95, 0.5), 'H', size=16, color=WALL)
    label(f, (1.55, 1.55), "L′", size=16, color=GREEN)
    # Right: a translate of V_ω, the strip a ≤ p · u_ω ≤ a + 1.
    a0 = -0.2
    P = [(a0 / math.cos(w), 0.0), ((a0 + 1) / math.cos(w), 0.0),
         ((a0 + 1 - math.sin(w)) / math.cos(w), 1.0), ((a0 - math.sin(w)) / math.cos(w), 1.0)]
    P = [(x + gap, y) for x, y in P]
    f.polygon(P, fill=FILLS[0], stroke=BLUE, width=1.6)
    f.line((gap - 2.25, 0), (gap + 2.2, 0), stroke=WALL, width=2.2)
    f.line((gap - 2.25, 1), (gap + 2.2, 1), stroke=WALL, width=2.2)
    for c in (a0, a0 + 1):
        # the line p · u_ω = c, between the heights -0.8 and 1.8
        pts = [((c - y * math.sin(w)) / math.cos(w) + gap, y) for y in (-0.8, 1.8)]
        f.line(pts[0], pts[1], stroke=GREEN, width=1.5)
    f.line(add(P[0], (0, -0.22)), add(P[1], (0, -0.22)), stroke=INK, width=1.2)
    for q in (P[0], P[1]):
        f.line(add(q, (0, -0.15)), add(q, (0, -0.29)), stroke=INK, width=1.2)
    label(f, add(mul(0.5, add(P[0], P[1])), (0.0, -0.4)), 'sec ω', size=15)
    label(f, (gap - 1.95, 0.5), 'H', size=16, color=WALL)
    label(f, add(P[2], (0.75, 0.6)), sb('V', 'ω', ' + c', size=16), size=16, color=GREEN)
    assert abs(polygon_area(P) - 1 / math.cos(w)) < 1e-12 and 1 / math.cos(w) < 2.2
    return f.save(f'{CH5}/two-bounds',
                  'The two area bounds of Theorem 1.5.1. Left: the horizontal strip H meets a '
                  'hallway L′ turned clockwise by π/4 (green walls) in a region, in blue, whose '
                  'horizontal slices all have length √2, so its area is √2. Right: H meets a '
                  'translate of the strip V_ω (green lines), here for ω = 1, in a parallelogram of '
                  'base sec ω and height 1')


def fig_horizontal_side():
    """Theorem 4.1.2: the part of the bottom side outside the niche, beyond every W_K(t)."""
    w, n = 1.3, 4
    thetas = [i * w / n for i in range(1, n)]
    ps = maximize_random(w, thetas)
    check_maximum(ps, 'omega = 1.3')
    f = Figure(-1.85, 2.15, -0.62, 1.35, 150)
    ray(f, (0.0, 0.0), (1.0, 0.0), stroke=WALL, width=2.0)
    ray(f, (0.0, 0.0), vvec(w), stroke=WALL, width=2.0)
    f.polygon(ps.cap_polygon(), fill=FILLS[0], stroke=BLUE, width=1.6)
    for poly in ps.niche_polygons():
        f.polygon(poly, fill=FILLS[1], stroke=ORANGE, width=1.4)
    C, A = ps.corner_points()
    Ws = [((ps.h[t] - 1) / math.cos(t), 0.0) for t in thetas]
    for W, t in zip(Ws, thetas):
        f.line(add(W, (0, -0.06)), add(W, (0, 0.06)), stroke=ORANGE, width=2.0)
    wmax = max(W[0] for W in Ws)
    # The free part of the bottom side, and the top side: both of length τ(π/2) = σ(π/2).
    f.line((wmax, 0.0), A, stroke=GREEN, width=4.4)
    p, q = upper_side(ps, PI / 2)
    f.line(p, q, stroke=GREEN, width=4.4)
    # The gaps w_K(t), t ∈ Θ, below the axis.
    for k, (W, t) in enumerate(sorted(zip(Ws, thetas))):
        y = -0.17 - 0.13 * k
        f.line((W[0], y), (A[0], y), stroke=INK, width=1.0)
        f.line((W[0], y - 0.04), (W[0], y + 0.04), stroke=INK, width=1.0)
        f.line((A[0], y - 0.04), (A[0], y + 0.04), stroke=INK, width=1.0)
    label(f, (A[0] + 0.18, -0.3), sb('w', 'K', '(t)'), size=15, anchor='start')
    f.dot(A, r=3.4)
    label(f, add(A, (0.12, 0.13)), sp('A', '−', '', size=14), size=14)
    f.dot((0.0, 0.0), r=3.0)
    label(f, (-0.02, -0.17), 'O', size=14)
    label(f, (0.95, 0.62), 'K', size=17, color=BLUE)
    # Facts: the free segment avoids the niche, has length τ_K(π/2) = σ_K(π/2) ≥ min_t w_K(t).
    free = A[0] - wmax
    assert abs(free - ps.tau(PI / 2)) < 1e-9 and abs(ps.tau(PI / 2) - ps.sigma(PI / 2)) < 1e-9
    for x in np.linspace(wmax + 1e-9, A[0], 50):
        assert ps.N(x)[0] <= 1e-12
    return f.save(f'{CH5}/horizontal-side',
                  'A maximum polygon cap K for ω = 1.3 and the uniform angle set with four '
                  'intervals, in blue, with its niche in orange. The ends W_K(t), t ∈ Θ, of the '
                  'wedges on the x-axis are marked, with the gaps w_K(t) to A below the axis. '
                  'The part of the bottom side right of every W_K(t) avoids the niche (green); '
                  'it has the length of the top side (green), by balancedness')


def fig_parallelogram(w=1.1):
    """Proposition 4.2.1: o_ω - v_0 = c_ω u_0, o_ω - u_ω = c_ω v_ω, and the triangle Δ_ω."""
    c = c_omega(w)
    P = para(w)
    o = P[2]
    f = Figure(-2.3, 2.6, -0.45, 1.38, 135)
    f.polygon(P, fill='none', stroke=INK, width=1.8)
    D = [(0.0, 0.0), (c, 0.0), mul(c, vvec(w))]
    f.polygon(D, fill=FILLS[1], stroke=ORANGE, width=1.8)
    for q in (D[1], D[2]):
        f.line(q, o, stroke=FAINT, width=1.3, dash='5 4')
        f.dot(q, r=3.0, fill=ORANGE)
    for q in (P[0], P[1], P[2], P[3]):
        f.dot(q, r=3.0)
    label(f, (-0.05, -0.2), 'O', size=14)
    label(f, add(P[1], (0.0, -0.2)), '(sec ω, 0)', size=14)
    label(f, add(o, (0.15, 0.17)), sb('o', 'ω'), size=15)
    label(f, add(P[3], (0.0, 0.17)), '(−tan ω, 1)', size=14)
    label(f, add(D[1], (0.33, -0.17)), sb('o', 'ω', ' − v₀', size=14), size=14, color=ORANGE)
    label(f, add(D[2], (-0.5, 0.0)), sb('o', 'ω', ' − u', size=14) + '<tspan dy="4.2" '
          'font-size="9.5">ω</tspan>', size=14, color=ORANGE)
    label(f, (0.02, 0.26), sb('Δ', 'ω', size=15), size=15, color=ORANGE, italic=False)
    label(f, (0.95, 0.5), sb('P', 'ω'), size=16)
    # Facts of the proposition.
    assert math.dist(D[1], sub(o, (0.0, 1.0))) < 1e-12
    assert math.dist(D[2], sub(o, uvec(w))) < 1e-12
    assert abs(c - (1 / math.cos(w) - math.tan(w))) < 1e-12 and abs(c - 0.2398) < 5e-5
    assert abs(dot(P[1], uvec(w)) - 1) < 1e-12
    return f.save(f'{CH5}/parallelogram',
                  'The parallelogram P_ω for ω = 1.1, with the vertices O, (sec ω, 0), o_ω and '
                  '(−tan ω, 1), and the triangle Δ_ω at O, in orange, with the vertices O, '
                  'o_ω − v_0 = c_ω u_0 and o_ω − u_ω = c_ω v_ω; the dashed segments from o_ω have '
                  'length 1')


def fig_clipped(w=1.1):
    """Lemma 4.2.2: R_{ω,d} = P_ω ∩ H₋(0, d + c_ω) ∩ H₋(ω + π/2, d + c_ω) for d = d_{ω,min}."""
    c, d = c_omega(w), d_min(w)
    P = para(w)
    R = clip_halfplane(P, uvec(0.0), d + c)
    R = clip_halfplane(R, uvec(w + PI / 2), d + c)
    f = Figure(-2.3, 2.6, -0.5, 1.38, 135)
    f.polygon(P, fill=GREY, stroke=FAINT, width=1.2, dash='5 4')
    f.polygon(R, fill=FILLS[0], stroke=BLUE, width=1.8)
    for s in (0.0, w + PI / 2):
        # the line l(s, d + c_ω), between the heights -0.15 and 1.15
        pt, v = mul(d + c, uvec(s)), vvec(s)
        a, b = (-0.15 - pt[1]) / v[1], (1.15 - pt[1]) / v[1]
        f.line(add(pt, mul(a, v)), add(pt, mul(b, v)), stroke=BLUE, width=1.0, dash='4 3')
    # The distances d + c_ω from O along the two bottom sides.
    q0 = (d + c, 0.0)
    f.line((0.0, -0.2), (q0[0], -0.2), stroke=INK, width=1.1)
    for x in (0.0, q0[0]):
        f.line((x, -0.14), (x, -0.26), stroke=INK, width=1.1)
    label(f, (q0[0] / 2, -0.36), sb('d + c', 'ω'), size=14)
    f.dot((0.0, 0.0), r=3.0)
    label(f, (-0.12, -0.12), 'O', size=14)
    label(f, (0.2, 0.5), sb('R', 'ω,d'), size=17, color=BLUE)
    area = polygon_area(R)
    expect = 1 / math.cos(w) - (math.tan(w) - d) ** 2 / math.tan(w)
    assert abs(area - expect) < 1e-12 and area < 2.2 and abs(area - 1.9446) < 5e-5
    return f.save(f'{CH5}/clipped',
                  'The region R_{ω,d} for ω = 1.1 and d = d_{ω,min} = 1.25, in blue: the '
                  'parallelogram P_ω (dashed) without the two corner triangles beyond the lines at '
                  'distance d + c_ω from O, normal to the two bottom sides'), area


def lemma_4_2_4_value(w):
    """(1 - d_{ω,min} cot ω)² + 4 cos² ω, the left side of the inequality of Lemma 4.2.4."""
    return (1 - d_min(w) / math.tan(w)) ** 2 + 4 * math.cos(w) ** 2


def fig_margin():
    """Lemma 4.2.4: (1 - d_{ω,min} cot ω)² + 4 cos² ω < 1 on [sec⁻¹(2.2), π/2)."""
    x0, x1, y0, y1 = 1.08, 1.6, 0.7, 1.03
    sx, sy = 11.5, 10.5

    def P(w, v):
        return ((w - x0) * sx, (v - y0) * sy)

    f = Figure(-0.85, (x1 - x0) * sx + 0.25, -0.75, (y1 - y0) * sy + 0.3, 92)
    f.line(P(x0, y0), P(x1, y0), stroke=INK, width=1.2)
    f.line(P(x0, y0), P(x0, y1), stroke=INK, width=1.2)
    for v in (0.7, 0.8, 0.9, 1.0):
        f.line(P(x0, v), add(P(x0, v), (-0.08, 0)), stroke=INK, width=1.0)
        label(f, add(P(x0, v), (-0.14, 0)), f'{v:.2f}', size=12, anchor='end', italic=False)
    f.line(P(x0, 1.0), P(x1, 1.0), stroke=FAINT, width=1.2, dash='5 4')
    for wv, name, anchor, dx in ((ARCSEC22, 'sec⁻¹ 2.2', 'end', 0.08),
                                 (ARCTAN22, 'tan⁻¹ 2.2', 'start', -0.08),
                                 (PI / 2, 'π/2', 'middle', 0.0)):
        f.line(P(wv, y0), add(P(wv, y0), (0, -0.08)), stroke=INK, width=1.0)
        label(f, add(P(wv, y0), (dx, -0.3)), name, size=12, italic=False, anchor=anchor)
        f.line(P(wv, y0), P(wv, y1), stroke=GREY, width=1.0)
    label(f, add(P(x1, y0), (-0.1, -0.62)), 'ω', size=15, anchor='end')
    vals = {}
    for a, b in ((ARCSEC22, ARCTAN22 - 1e-12), (ARCTAN22, PI / 2)):
        ws = np.linspace(a, b, 300)
        f.polyline([P(wv, lemma_4_2_4_value(wv)) for wv in ws], stroke=BLUE, width=2.0)
        for wv in (a, b):
            v = lemma_4_2_4_value(wv)
            vals[wv] = v
            f.dot(P(wv, v), r=3.2, fill=BLUE)
    # The endpoint values, recomputed (REPORT.md, E9): 0.957571, 0.871398, 0.934932, 1.
    expected = (0.957571, 0.871398, 0.934932, 1.0)
    for (wv, v), e in zip(sorted(vals.items()), expected):
        assert abs(v - e) < 5e-7, (wv, v, e)
    keys = sorted(vals)
    label(f, add(P(keys[0], vals[keys[0]]), (-0.45, 0.1)), '0.9576', size=12, italic=False)
    label(f, add(P(keys[1], vals[keys[1]]), (-0.45, -0.08)), '0.8714', size=12, italic=False)
    label(f, add(P(keys[2], vals[keys[2]]), (0.42, -0.12)), '0.9349', size=12, italic=False)
    label(f, add(P(keys[3], vals[keys[3]]), (-0.15, 0.2)), '1', size=12, italic=False)
    for wv in np.linspace(ARCSEC22, PI / 2 - 1e-9, 2000):
        assert lemma_4_2_4_value(wv) < 1
    return f.save(f'{CH5}/margin',
                  'The left side (1 − d cot ω)² + 4 cos² ω of the inequality of Lemma 4.2.4, with '
                  'd = d_{ω,min}, against ω from sec⁻¹(2.2) to π/2: two convex pieces, for d = 1.25 '
                  'and d = 1.1, below the dashed line at 1 except at ω = π/2'), vals


def fig_consumed(w=1.1, d=1.5, d_left=1.2):
    """Theorem 4.2.5: the hallway L_X(π/2 - ω) of X = {q₀, q₁} encloses the triangle Δ_ω."""
    c = c_omega(w)
    P = para(w)
    o = P[2]
    K = clip_halfplane(P, uvec(0.0), d + c)
    K = clip_halfplane(K, uvec(w + PI / 2), d_left + c)
    ry = 1 - d / math.tan(w)
    g = math.sqrt(1 - ry ** 2)
    q0 = add(sub(o, (0.0, 1.0)), (d, 0.0))
    q1 = sub(o, (g, 0.0))
    r = (d + c, ry)
    s_pt = sub(q0, (g, 0.0))
    t = PI / 2 - w
    a_val, c_val = dot(q0, uvec(t)), dot(q1, vvec(t))
    xX = add(mul(a_val - 1, uvec(t)), mul(c_val - 1, vvec(t)))
    f = Figure(-2.25, 2.55, -0.62, 2.0, 132)
    # The quadrant Q⁻_X(t), within the fan F_ω.
    big = [(-9.0, 0.0), (9.0, 0.0), (9.0, 9.0), (-9.0, 9.0)]
    Q = clip_halfplane(big, uvec(t), a_val - 1)
    Q = clip_halfplane(Q, vvec(t), c_val - 1)
    Q = clip_halfplane(Q, mul(-1, uvec(w)), 0.0)
    f.polygon(P, fill='none', stroke=FAINT, width=1.2, dash='5 4')
    f.polygon(K, fill=FILLS[0], stroke='none', width=0)
    f.polygon(Q, fill=FILLS[1], stroke='none', width=0)
    f.polygon(K, fill='none', stroke=BLUE, width=1.6)
    D = [(0.0, 0.0), (c, 0.0), mul(c, vvec(w))]
    f.polygon(D, fill=ORANGE_MID, stroke=ORANGE, width=1.4)
    draw_hallway_walls(f, xX, t, GREEN, width=1.5)
    # The right triangle s, q₀, r with hypotenuse 1, and the two segments of length g.
    f.polygon([s_pt, q0, r], fill='none', stroke=GREEN, width=1.3, dash='5 3')
    f.line(s_pt, q0, stroke=BLUE, width=4.2)
    f.line(q1, o, stroke=BLUE, width=4.2)
    for pt in (q0, q1, r, s_pt, o):
        f.dot(pt, r=3.2)
    label(f, add(q0, (0.25, -0.17)), sb('q', '0'), size=15)
    label(f, add(q1, (-0.05, 0.19)), sb('q', '1'), size=15)
    label(f, add(r, (0.15, 0.05)), 'r', size=15)
    label(f, add(s_pt, (-0.02, -0.19)), 's', size=15)
    label(f, add(o, (0.17, 0.15)), sb('o', 'ω'), size=15)
    label(f, (0.5 * (s_pt[0] + q0[0]), -0.19), 'g', size=15, color=BLUE)
    label(f, (0.5 * (q1[0] + o[0]), 1.15), 'g', size=15, color=BLUE)
    label(f, add(mul(0.5, add(s_pt, r)), (-0.1, 0.12)), '1', size=14, color=GREEN, italic=False)
    label(f, (0.0, -0.2), sb('Δ', 'ω', size=14), size=14, color=ORANGE, italic=False)
    yX = add(xX, uvec(t), vvec(t))
    label(f, add(yX, (0.5, 0.0)), sb('L', 'X', '(t)'), size=16, color=GREEN)
    # Facts: q₀ and q₁ lie on the outer walls; the three points lie in Q⁻_X(t) (Lemma 4.2.4).
    assert d_min(w) <= d <= math.tan(w) and ry >= 0
    assert abs(math.dist(s_pt, r) - 1) < 1e-12
    assert dot(q0, uvec(t)) >= dot(q1, uvec(t)) and dot(q1, vvec(t)) >= dot(q0, vvec(t))
    for pt in D:
        assert dot(pt, uvec(t)) < a_val - 1 and dot(pt, vvec(t)) < c_val - 1
    assert dot(sub(q0, sub(o, (0, 1))), uvec(t)) > 1 and dot(sub(q1, sub(o, uvec(w))), vvec(t)) > 1
    return f.save(f'{CH5}/consumed',
                  'The proof of Theorem 4.2.5 for ω = 1.1 and t = π/2 − ω, with a cap K in blue. '
                  'The corner q0 on the x-axis, the corner r on l(ω, 1) above it, and the point s '
                  'with |r − s| = 1 give the length g; the point q1 at distance g from o_ω lies on '
                  'the top side. The hallway with outer walls through q0 and q1 (green) has the '
                  'triangle Δ_ω (orange) inside its inner quadrant (light orange)')


def fig_rotate(w=1.1):
    """Theorem 1.5.2: P_ω \\ Δ_ω turns by π/2 - ω inside the horizontal strip."""
    c = c_omega(w)
    pent = pentagon(w)
    tri = [(0.0, 0.0), (c, 0.0), mul(c, vvec(w))]
    beta = PI / 2 - w
    phis = (beta, beta / 2, 0.0)
    names = ('φ = π/2 − ω', 'φ = (π/2 − ω)/2', 'φ = 0')
    hgt = 1.6
    f = Figure(-2.45, 2.75, -0.45 - hgt * 2, 1.38, 108)
    x0, x1, _, _ = window(f)
    for k, (phi, name) in enumerate(zip(phis, names)):
        dy = -hgt * k
        P = [rot(phi, p) for p in pent]
        T = [rot(phi, p) for p in tri]
        ymin = min(p[1] for p in P)
        shift = (0.0, dy - ymin)
        P = [add(p, shift) for p in P]
        T = [add(p, shift) for p in T]
        f.polygon([(x0, dy), (x1, dy), (x1, dy + 1), (x0, dy + 1)], fill=FLOOR, stroke='none',
                  width=0)
        f.line((x0, dy), (x1, dy), stroke=WALL, width=2.0)
        f.line((x0, dy + 1), (x1, dy + 1), stroke=WALL, width=2.0)
        f.polygon(T, fill=FILLS[1], stroke=ORANGE, width=1.3, dash='4 3')
        f.polygon(P, fill=FILLS[0], stroke=BLUE, width=1.8)
        label(f, (x0 + 0.05, dy + 1.2), name, size=14, anchor='start')
        height = max(p[1] for p in P) - min(p[1] for p in P)
        assert height <= 1 + 1e-12
        if 0 < phi < beta:
            assert min(p[1] for p in T) < dy - 0.04
    # The width of P_ω \ Δ_ω in the direction u_t, t ∈ [ω, π/2], is max(sin t, cos(t - ω)) ≤ 1.
    for tt in np.linspace(w, PI / 2, 50):
        width = max(dot(p, uvec(tt)) for p in pent) - min(dot(p, uvec(tt)) for p in pent)
        assert abs(width - max(math.sin(tt), math.cos(tt - w))) < 1e-12
    return f.save(f'{CH5}/rotate',
                  'The pentagon P_ω without Δ_ω, for ω = 1.1, in blue, turned counterclockwise by '
                  'φ = π/2 − ω, (π/2 − ω)/2 and 0, each resting on the floor of the horizontal '
                  'strip: it always fits, while the triangle Δ_ω (orange, dashed) would stick out '
                  'below the floor in the middle position')


def main():
    two, small, caps = max_two(), max_small(), dyadic()
    bm = fig_balancing_move()
    paths = [fig_polygon_sofa(two), bm[0], fig_disconnect(), fig_cap_niche(small), fig_fan(),
             fig_balanced(small), fig_limit(caps), fig_two_bounds(), fig_horizontal_side(),
             fig_parallelogram(), fig_clipped()[0], fig_margin()[0], fig_consumed(), fig_rotate()]
    for p in paths:
        print(f'wrote {p.relative_to(OUT.parents[2])}')
    # The numbers quoted in Chapters 4 and 5.
    print(f"Gerver's example, c = 0.1: s+ = {bm[1]:.4f}, s- = {bm[2]:.4f}")
    print(f'Θ = {{π/6, π/3}}: max 𝒜_Θ = {two.functional():.6f}, sides '
          + ', '.join(f'{two.sigma(s):.6f}' for s in two.diamond))
    print(f'ω = 1.2, Θ = {{0.4, 0.8}}: max 𝒜_Θ = {small.functional():.6f}')
    for n, ps in caps.items():
        print(f'Θ_(π/2, {n}): max 𝒜_Θ = {ps.functional():.6f}')


if __name__ == '__main__':
    main()
