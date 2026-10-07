#!/usr/bin/env python3
"""The figures of Chapters 8 and 9, in baek/proof/figures/08-convex-curves/ and
baek/proof/figures/09-optimality/.

    python3 scripts/figures/fig_optimality.py

Chapter 8 (convex curves and Mamikon's theorem) uses two convex bodies given by their support
functions: the convex hull of an ellipse and a point, which has two edges and a corner, and a lens,
the intersection of two discs, which has two corners and no edge. Chapter 9 uses Gerver's sofa:
its cap K is computed from its support function h_K(t) = <x(t), u_t> + 1, h_K(t + pi/2) =
<x(t), v_t> + 1 (x the rotation path of gerver.py), the bodies B_K and D_K by intersecting K with
the half-planes bounded by the inner walls, and the contact curves A, B, C, D from Romik's formulas.
Every fact that a caption states is checked by an assertion.
"""
import math

import numpy as np

import gerver
from sofa_figures import Figure, OUT, INK, FAINT, COLORS, FILLS, GREY, sb

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
LBLUE, LORANGE, LGREEN, LPURPLE = FILLS[0], FILLS[1], FILLS[2], FILLS[3]
CH8, CH9 = '08-convex-curves', '09-optimality'


# ---- plane geometry ---------------------------------------------------------------------------

def u(t):
    return (math.cos(t), math.sin(t))


def v(t):
    return (-math.sin(t), math.cos(t))


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def cross(p, q):
    return p[0] * q[1] - p[1] * q[0]


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def mul(c, p):
    return (c * p[0], c * p[1])


def seg_area(p, q):
    """The curve area functional J(p, q) = (p x q)/2 of the segment from p to q."""
    return cross(p, q) / 2


def curve_area(pts):
    """J of the polyline through pts: the sum of J over its segments (exact for polylines)."""
    return sum(seg_area(pts[i], pts[i + 1]) for i in range(len(pts) - 1))


def polygon_area(pts):
    """The signed (shoelace) area of a closed polygon, positive when counterclockwise."""
    return curve_area(list(pts) + [pts[0]])


def vint(h, a, b):
    """v_K(a, b), the intersection of the supporting lines l_K(a) and l_K(b) (Lean `vint`)."""
    c = (h(b) - h(a) * math.cos(b - a)) / math.sin(b - a)
    return add(mul(h(a), u(a)), mul(c, v(a)))


def clip(poly, n, c):
    """The part {p . n <= c} of a polygon (Sutherland-Hodgman, one half-plane)."""
    out = []
    m = len(poly)
    for i in range(m):
        p, q = poly[i], poly[(i + 1) % m]
        fp, fq = dot(p, n) - c, dot(q, n) - c
        if fp <= 0:
            out.append(p)
        if (fp < 0 < fq) or (fq < 0 < fp):
            s = fp / (fp - fq)
            out.append(add(p, mul(s, sub(q, p))))
    return out


def bisect(f, lo, hi, n=200):
    flo = f(lo)
    for _ in range(n):
        mid = (lo + hi) / 2
        fm = f(mid)
        if (fm > 0) == (flo > 0):
            lo, flo = mid, fm
        else:
            hi = mid
    return (lo + hi) / 2


def simpson(f, a, b, n=2000):
    xs = np.linspace(a, b, 2 * n + 1)
    ys = np.array([f(x) for x in xs])
    h = (b - a) / (2 * n)
    return h / 3 * (ys[0] + ys[-1] + 4 * ys[1:-1:2].sum() + 2 * ys[2:-1:2].sum())


def simplify(pts, tol):
    """Ramer-Douglas-Peucker simplification of a polyline, to keep the SVG files small. The
    figures compute with the full point lists and draw the simplified ones."""
    pts = list(pts)
    if len(pts) < 3:
        return pts
    keep = [False] * len(pts)
    keep[0] = keep[-1] = True
    stack = [(0, len(pts) - 1)]
    while stack:
        i, j = stack.pop()
        if j <= i + 1:
            continue
        (ax, ay), (bx, by) = pts[i], pts[j]
        dx, dy = bx - ax, by - ay
        norm = math.hypot(dx, dy)
        best, k = -1.0, i + 1
        for m in range(i + 1, j):
            px, py = pts[m]
            d = (abs(dx * (py - ay) - dy * (px - ax)) / norm if norm > 0
                 else math.hypot(px - ax, py - ay))
            if d > best:
                best, k = d, m
        if best > tol:
            keep[k] = True
            stack += [(i, k), (k, j)]
    return [q for q, kq in zip(pts, keep) if kq]


class Fig(Figure):
    """A `Figure` that simplifies long polylines and polygons to a quarter of a pixel."""

    def polygon(self, pts, **kw):
        super().polygon(simplify(pts, 0.25 / self.s), **kw)

    def polyline(self, pts, **kw):
        super().polyline(simplify(pts, 0.25 / self.s), **kw)


# ---- labels -----------------------------------------------------------------------------------

def bold(s):
    return f'<tspan font-weight="bold" font-style="normal">{s}</tspan>'


def seq(*parts, size=15):
    """Runs of text on the baseline ('n'), as subscripts ('sub') or as superscripts ('sup'):
    seq(('h', 'n'), ('K', 'sub'), ('(t', 'n'), ('1', 'sub'), (')', 'n')) is h_K(t_1)."""
    shift = {'n': 0.0, 'sub': 0.3 * size, 'sup': -0.38 * size, 'over': -0.38 * size}
    out, level, last = '', 0.0, ''
    for text, kind in parts:
        dy = shift[kind] - level
        fs = '' if kind == 'n' else f' font-size="{0.68 * size:.1f}"'
        # 'over': a superscript stacked over the preceding subscript
        dx = f' dx="{-0.5 * 0.68 * size * len(last):.1f}"' if kind == 'over' else ''
        if not out and kind == 'n':
            out = text
        else:
            out += f'<tspan{dx} dy="{dy:.1f}"{fs}>{text}</tspan>'
        level, last = shift[kind], text
    return out


def subsup(base, sub_, sup_, size=15, after=''):
    """Text with both a subscript and a superscript, as SVG markup."""
    d1, d2, fs = 0.3 * size, 0.38 * size, 0.68 * size
    w = 0.5 * fs * len(sub_)
    out = (f'{base}<tspan dy="{d1:.1f}" font-size="{fs:.1f}">{sub_}</tspan>'
           f'<tspan dx="{-w:.1f}" dy="{-(d1 + d2):.1f}" font-size="{fs:.1f}">{sup_}</tspan>')
    if after:
        out += f'<tspan dy="{d2:.1f}">{after}</tspan>'
    return out


# ---- Chapter 8: a convex body with two edges and a corner ---------------------------------------

class Kite:
    """K = conv(E ∪ {P}) for the ellipse E = {(x/a)^2 + (y/b)^2 <= 1} and a point P outside E.

    Its support function is h_K(t) = max(h_E(t), <P, u_t>). The tangents from P touch E at the
    normal angles t1 < t2: there K has the edges [Q1, P] and [P, Q2], and on (t1, t2) the corner P.
    """

    def __init__(self, ax=1.6, by=1.0, p=(0.8, 1.25)):
        self.ax, self.by, self.P = ax, by, p
        g = lambda t: dot(p, u(t)) - self.hE(t)
        ts = np.linspace(-PI, PI, 3601)
        roots = [bisect(g, ts[i], ts[i + 1]) for i in range(len(ts) - 1)
                 if (g(ts[i]) > 0) != (g(ts[i + 1]) > 0)]
        assert len(roots) == 2, roots
        self.t1, self.t2 = roots
        self.Q1, self.Q2 = self.pE(self.t1), self.pE(self.t2)

    def hE(self, t):
        return math.hypot(self.ax * math.cos(t), self.by * math.sin(t))

    def pE(self, t):
        s = self.hE(t)
        return (self.ax ** 2 * math.cos(t) / s, self.by ** 2 * math.sin(t) / s)

    def rhoE(self, t):
        """The radius of curvature of E at the normal angle t: the density of sigma_K there."""
        return (self.ax * self.by) ** 2 / self.hE(t) ** 3

    def h(self, t):
        return max(self.hE(t), dot(self.P, u(t)))

    def corner(self, t):
        tt = (t - self.t1) % (2 * PI)
        return 0 < tt < self.t2 - self.t1

    def vplus(self, t):
        if self.corner(t) or math.isclose(t, self.t1):
            return self.P
        if math.isclose(t, self.t2):
            return self.Q2
        return self.pE(t)

    def vminus(self, t):
        if self.corner(t) or math.isclose(t, self.t2):
            return self.P
        if math.isclose(t, self.t1):
            return self.Q1
        return self.pE(t)

    def arc(self, a, b, n=400):
        """The convex curve u_K^{a,b}, from v_K^+(a) to v_K^-(b), as a polyline (a < t1 < t2 < b)."""
        pts = [self.pE(t) for t in np.linspace(a, self.t1, n)]
        pts += [self.P]
        pts += [self.pE(t) for t in np.linspace(self.t2, b, n)]
        return pts

    def outline(self, n=1200):
        pts = [self.pE(t) for t in np.linspace(self.t2, self.t1 + 2 * PI, n)]
        return pts + [self.P]

    def half_int_h_dsigma(self, a, b):
        """(1/2) of the integral of h_K over (a, b) against sigma_K: arcs, edges and the corner."""
        smooth = (simpson(lambda t: self.hE(t) * self.rhoE(t), a, self.t1)
                  + simpson(lambda t: self.hE(t) * self.rhoE(t), self.t2, b))
        atoms = (self.h(self.t1) * math.dist(self.Q1, self.P)
                 + self.h(self.t2) * math.dist(self.P, self.Q2))
        return (smooth + atoms) / 2

    def sigma_cdf(self, a, t):
        """sigma_K((a, t]) for a < t1."""
        if t <= self.t1:
            return simpson(self.rhoE, a, t, 400) if t > a else 0.0
        m = simpson(self.rhoE, a, self.t1, 400) + math.dist(self.Q1, self.P)
        if t < self.t2:
            return m
        return m + math.dist(self.P, self.Q2) + simpson(self.rhoE, self.t2, t, 400)


KITE = Kite()
KA, KB = KITE.t1 - 0.3, KITE.t2 + 0.35     # the arc u_K^{a,b} of Figures 8.2, 8.3 and 8.5


def check_kite():
    k = KITE
    # The edges are traversed counterclockwise: v^-(t1) = Q1, v^+(t1) = P, v^-(t2) = P, v^+(t2) = Q2.
    assert dot(sub(k.P, k.Q1), v(k.t1)) > 0 and dot(sub(k.Q2, k.P), v(k.t2)) > 0
    assert 0 < KB - KA < PI and KA < k.t1 < k.t2 < KB
    # P lies on the supporting lines at t1 and t2, and K lies in every H_K(t).
    for t in (k.t1, k.t2):
        assert abs(dot(k.P, u(t)) - k.h(t)) < 1e-9
    for t in np.linspace(0, 2 * PI, 97):
        assert all(dot(p, u(t)) <= k.h(t) + 1e-9 for p in k.outline(300))


# ---- Figure 8.1: a concave quadratic on a segment ------------------------------------------------

def fig_midpoint():
    """p(lambda) = f(c_lambda(K, K')) = A + delta lambda + E lambda^2 with E < 0 and delta < 0."""
    A, delta, E = 1.0, -0.22, -0.6
    p = lambda lam: A + delta * lam + E * lam ** 2
    gap = p(0.5) - (p(0) + p(1)) / 2
    assert abs(gap + E / 4) < 1e-12 and gap > 0
    assert p(1) == A + delta + E and p(1) <= A
    assert all(p(l) <= A + delta * l + 1e-12 for l in np.linspace(0, 1, 101))
    f = Fig(-0.3, 1.5, -0.2, 1.22, 250)
    # axes
    f.line((-0.02, 0), (1.25, 0), stroke=FAINT, width=1, arrow=True)
    f.line((0, -0.02), (0, 1.17), stroke=FAINT, width=1, arrow=True)
    f.text((1.27, -0.07), 'λ', size=16, anchor='end')
    for lam, s in ((0, '0'), (0.5, '½'), (1, '1')):
        f.line((lam, -0.02), (lam, 0.02), stroke=FAINT, width=1)
        f.text((lam, -0.08), s, size=14, italic=False)
    # the tangent line at 0, the chord, the parabola
    f.line((0, A), (1.08, A + delta * 1.08), stroke=ORANGE, width=1.6, dash='6 4')
    f.line((0, p(0)), (1, p(1)), stroke=FAINT, width=1.4, dash='4 3')
    f.polyline([(l, p(l)) for l in np.linspace(0, 1, 200)], stroke=BLUE, width=2.4)
    f.line((0.5, (p(0) + p(1)) / 2), (0.5, p(0.5)), stroke=GREEN, width=2.2)
    f.line((1, 0), (1, p(1)), stroke=FAINT, width=1, dash='2 3')
    f.line((0.5, 0), (0.5, (p(0) + p(1)) / 2), stroke=FAINT, width=1, dash='2 3')
    for q in ((0, p(0)), (1, p(1)), (0.5, p(0.5)), (0.5, (p(0) + p(1)) / 2)):
        f.dot(q, r=3.4, fill=INK)
    f.text((-0.04, p(0)), 'f(K)', size=15, anchor='end')
    f.text((1.04, p(1) - 0.02), "f(K′)", size=15, anchor='start')
    f.text((0.53, (p(0.5) + (p(0) + p(1)) / 2) / 2), 'gap = −E/4', size=14, anchor='start',
           color=GREEN)
    f.text((0.84, A + delta * 0.84 + 0.08), 'slope Df(K; K′)', size=14, anchor='middle',
           color=ORANGE)
    f.text((0.8, p(0.8) + 0.06), 'p(λ)', size=15, color=BLUE, anchor='start')
    return f.save(f'{CH8}/midpoint',
                  "The graph of p(lambda) = f(c_lambda(K, K')) for lambda from 0 to 1, a concave "
                  "parabola from f(K) down to f(K'); the dashed chord joins its ends, a green "
                  "segment at lambda = 1/2 marks the gap between the parabola and the chord, and "
                  "the dashed orange tangent at lambda = 0, of slope Df(K; K'), lies above the "
                  "parabola")


# ---- Figure 8.2: the curve area functional of a convex arc ---------------------------------------

def fig_curve_area():
    k = KITE
    arc = k.arc(KA, KB)
    J = curve_area(arc)
    half_int = k.half_int_h_dsigma(KA, KB)
    assert abs(J - half_int) < 2e-4, (J, half_int)
    O = (0.0, 0.0)
    assert polygon_area([O] + arc) > 0 and abs(polygon_area([O] + arc) - J) < 1e-12
    f = Fig(-2.0, 2.05, -1.25, 1.62, 165)
    f.polygon(k.outline(), fill=LBLUE, stroke=BLUE, width=1.4)
    f.polygon([O] + arc, fill=LORANGE, stroke='none', width=0, opacity=0.95)
    # the two edges contribute whole triangles, of area h_K(t_i) sigma_K({t_i}) / 2
    f.polygon([O, k.Q1, k.P], fill='#fdba74', stroke='none', width=0, opacity=0.9)
    f.polygon([O, k.P, k.Q2], fill='#fdba74', stroke='none', width=0, opacity=0.9)
    for t in np.linspace(KA, k.t1, 7)[1:-1].tolist() + np.linspace(k.t2, KB, 6)[1:-1].tolist():
        f.line(O, k.pE(t), stroke=ORANGE, width=0.7)
    f.line(O, k.Q1, stroke=ORANGE, width=0.9)
    f.line(O, k.Q2, stroke=ORANGE, width=0.9)
    f.line(O, k.P, stroke=ORANGE, width=0.9)
    f.line(O, arc[0], stroke=ORANGE, width=1.2)
    f.line(O, arc[-1], stroke=ORANGE, width=1.2)
    f.polyline(arc, stroke=BLUE, width=3.0)
    # the supporting line l_K(t1) of the first edge, and its distance h_K(t1) from O: the dark
    # triangle O Q1 P has area h_K(t1) sigma_K({t1}) / 2
    t1 = k.t1
    foot = mul(k.h(t1), u(t1))
    assert abs(polygon_area([O, k.Q1, k.P]) - k.h(t1) * math.dist(k.Q1, k.P) / 2) < 1e-12
    f.line(add(k.Q1, mul(-0.35, v(t1))), add(k.P, mul(0.3, v(t1))), stroke=INK, width=1.0)
    f.line(O, foot, stroke=INK, width=1.1, dash='4 3')
    f.dot(foot, r=2.4)
    lab = lambda c: seq((c, 'n'), ('K', 'sub'), ('(t', 'n'), ('1', 'sub'), (')', 'n'), size=14)
    f.text(add(k.P, mul(0.3, v(t1))), lab('l'), size=14, anchor='end', dx=-6)
    f.text(add(mul(0.6, foot), (0.12, -0.08)), lab('h'), size=14, anchor='start')
    f.dot(O, r=3)
    f.text((0.07, -0.15), 'O', size=15)
    for p_ in (arc[0], arc[-1], k.P):
        f.dot(p_, r=3.2, fill=BLUE)
    f.text(add(arc[0], (0.22, -0.05)), subsup('v', 'K', '+', after='(a)'), size=15, anchor='start',
           dx=-14)
    f.text(add(arc[-1], (-0.12, -0.13)), subsup('v', 'K', '−', after='(b)'), size=15,
           anchor='end')
    f.text(add(k.P, (0.1, 0.06)), 'P', size=15, anchor='start')
    f.text((0.55, -0.72), 'K', size=18, color=BLUE)
    f.text((1.5, 1.05), subsup(bold('u'), 'K', 'a,b'), size=16, color=BLUE)
    return f.save(f'{CH8}/curve-area',
                  "A convex body K, the convex hull of an ellipse and a point P, and the arc "
                  "u_K^{a,b} of its boundary from v_K^+(a) to v_K^-(b), drawn thick; it runs along "
                  "the ellipse, an edge, the corner P, a second edge and the ellipse again. The "
                  "region swept by the segment from the origin O to a point moving along the arc "
                  "is shaded; its two darker triangles are the contributions of the edges. A "
                  "supporting line l_K(t) and its distance h_K(t) from O are marked")


# ---- Figure 8.3: the cut body and the region between an arc and its tangents --------------------

def fig_cut():
    k = KITE
    a, b = KA, KB
    arc = k.arc(a, b)
    p1, p2, p0 = arc[0], arc[-1], vint(k.h, a, b)
    assert math.dist(p1, k.vplus(a)) < 1e-12 and math.dist(p2, k.vminus(b)) < 1e-12
    # v_K(a, b) lies on both supporting lines, outside K.
    assert abs(dot(p0, u(a)) - k.h(a)) < 1e-9 and abs(dot(p0, u(b)) - k.h(b)) < 1e-9
    T = [p1, p0, p2]
    region = T + arc[::-1][1:-1]        # p1 -> p0 -> p2 -> back along the arc
    K_cut = arc                        # K' = K ∩ H', bounded by the arc and the chord
    area_T, area_cut, area_R = polygon_area(T), polygon_area(K_cut), polygon_area(region)
    assert area_T > 0 and area_cut > 0 and area_R > 0
    assert abs(area_T - area_cut - area_R) < 1e-9
    J_u = curve_area(arc)
    assert abs(area_cut - (J_u + seg_area(p2, p1))) < 1e-9          # |K'| = J(u) + J(v-(b), v+(a))
    assert abs(area_R - (seg_area(p1, p0) + seg_area(p0, p2) - J_u)) < 1e-9   # Lemma 7.3.5
    assert abs(J_u - k.half_int_h_dsigma(a, b)) < 2e-4
    # v_K^-(b) - v_K^+(a) is a positive multiple of v_{t'} with t' in (a, b), so the half-plane H'
    # bounded by the chord and containing v_K(a, b) has the normal angle t' + pi (Lemma 7.3.1)
    d = sub(p2, p1)
    tprime = math.atan2(d[1], d[0]) - PI / 2
    tprime += 2 * PI * round((0.5 * (a + b) - tprime) / (2 * PI))
    assert a < tprime < b
    f = Fig(-2.05, 2.3, -1.15, 2.2, 150)
    f.polygon(k.outline(), fill=GREY, stroke=FAINT, width=1.2)
    f.polygon(K_cut, fill=LBLUE, stroke=BLUE, width=1.4)
    f.polygon(region, fill=LORANGE, stroke='none', width=0)
    f.polyline([p1, p0, p2], stroke=ORANGE, width=1.6)
    f.line(p1, p2, stroke=BLUE, width=1.2, dash='6 4')
    f.polyline(arc, stroke=BLUE, width=2.8)
    for p_ in (p1, p2, p0):
        f.dot(p_, r=3.2, fill=INK)
    f.text(add(p1, (0.12, -0.1)), subsup('v', 'K', '+', after='(a)'), size=15, anchor='start')
    f.text(add(p2, (-0.12, -0.12)), subsup('v', 'K', '−', after='(b)'), size=15, anchor='end')
    f.text(add(p0, (0, 0.17)), sb('v', 'K', '(a, b)'), size=15)
    f.text((0.15, 0.55), "K′", size=18, color=BLUE)
    f.text((0.12, -0.6), 'K', size=17, color=FAINT)
    f.text((0.62, 1.62), 'R', size=18, color=ORANGE)
    mid = mul(0.5, add(p1, p2))
    f.text(add(mid, (0.1, -0.2)), "l′", size=15, color=BLUE)
    return f.save(f'{CH8}/cut',
                  "The convex body K of the previous figure, grey, cut along the chord l' from "
                  "v_K^-(b) to v_K^+(a): the part K' beyond the chord is blue. The supporting "
                  "lines at a and b meet at v_K(a, b), and the triangle with vertices v_K^+(a), "
                  "v_K(a, b), v_K^-(b) is the union of K' and the orange region R between the arc "
                  "and the two tangent segments")


# ---- Figure 8.4: Mamikon's theorem -------------------------------------------------------------

class Lens:
    """The lens K = D((-d, 0), r) ∩ D((d, 0), r): two circular arcs meeting at the corners
    (0, ±y0). Its upper corner carries the normal angles [psi, pi - psi]."""

    def __init__(self, r=1.5, d=0.9):
        self.r, self.d = r, d
        self.y0 = math.sqrt(r * r - d * d)
        self.psi = math.atan2(self.y0, d)

    def vplus(self, t):
        """v_K^+(t) for t in [0, pi]: the right arc, the upper corner, the left arc."""
        if t <= self.psi:
            return add((-self.d, 0), mul(self.r, u(t)))
        if t < PI - self.psi:
            return (0.0, self.y0)
        return add((self.d, 0), mul(self.r, u(t)))

    def h(self, t):
        return dot(self.vplus(t), u(t))

    def outline(self, n=400):
        right = [add((-self.d, 0), mul(self.r, u(t))) for t in np.linspace(-self.psi, self.psi, n)]
        left = [add((self.d, 0), mul(self.r, u(t)))
                for t in np.linspace(PI - self.psi, PI + self.psi, n)]
        return right + left


def fig_mamikon():
    k = Lens(r=1.5, d=0.45)
    a, b = k.psi - 0.95, PI - k.psi + 0.85
    assert 0 < b - a < PI and a < k.psi < PI - k.psi < b
    alpha = lambda t: 0.8 + 0.22 * math.cos(1.6 * (t - 0.5 * (a + b)))
    ts = np.linspace(a, b, 2001)
    base = [k.vplus(t) for t in ts]
    z = [add(k.vplus(t), mul(alpha(t), v(t))) for t in ts]
    # z(t) lies on l_K(t), and alpha(t) = <z(t) - v_K^+(t), v_t> > 0.
    for t, q in zip(ts[::50], z[::50]):
        assert abs(dot(q, u(t)) - k.h(t)) < 1e-9 and alpha(t) > 0
    arc = [base[0]] + [q for p_, q in zip(base, base[1:]) if q != p_]     # the corner once
    J_u = curve_area(arc)
    M = seg_area(base[0], z[0]) + curve_area(z) + seg_area(z[-1], base[-1]) - J_u
    half_int = simpson(lambda t: alpha(t) ** 2, a, b) / 2
    region = z + arc[::-1]             # counterclockwise: along z, then back along the arc
    assert abs(M - half_int) < 1e-4, (M, half_int)
    assert abs(polygon_area(region) - half_int) < 1e-4
    # the part swept while the segments turn about the corner is a sector-like fan
    corner = [t for t in ts if k.psi < t < PI - k.psi]
    fan = [(0.0, k.y0)] + [add((0.0, k.y0), mul(alpha(t), v(t))) for t in corner]
    assert abs(polygon_area(fan) - simpson(lambda t: alpha(t) ** 2, k.psi, PI - k.psi) / 2) < 1e-3
    # the tangent cluster: the vectors alpha(t) v_t from a common point Q
    Q = (4.05, 1.25)
    cluster = [Q] + [add(Q, mul(alpha(t), v(t))) for t in ts]
    assert abs(polygon_area(cluster) - half_int) < 1e-4
    f = Fig(-2.0, 4.35, -1.45, 2.65, 122)
    f.polygon(k.outline(), fill=LBLUE, stroke=BLUE, width=1.3)
    f.polygon(region, fill=LORANGE, stroke='none', width=0)
    f.polygon(cluster, fill=LORANGE, stroke='none', width=0)
    for t in np.linspace(a, b, 31):
        p_ = k.vplus(t)
        f.line(p_, add(p_, mul(alpha(t), v(t))), stroke=ORANGE, width=0.8)
        f.line(Q, add(Q, mul(alpha(t), v(t))), stroke=ORANGE, width=0.8)
    f.polyline(z, stroke=ORANGE, width=2.0)
    f.polyline(cluster[1:], stroke=ORANGE, width=2.0)
    f.polyline(arc, stroke=BLUE, width=2.8)
    f.dot(Q, r=3.2)
    f.dot((0.0, k.y0), r=3.2, fill=BLUE)
    for q in (base[0], base[-1]):
        f.dot(q, r=3.0, fill=BLUE)
    f.text((0.0, -0.3), 'K', size=18, color=BLUE)
    f.text(add(z[0], (0.1, 0.06)), 'z(a)', size=15, anchor='start')
    f.text(add(z[-1], (-0.08, -0.1)), 'z(b)', size=15, anchor='end')
    f.text(add(base[0], (0.12, -0.08)), subsup('v', 'K', '+', after='(a)'), size=15,
           anchor='start')
    f.text(add(base[-1], (0.12, -0.06)), subsup('v', 'K', '−', after='(b)'), size=15,
           anchor='start')
    t_lab = a + 0.1
    f.text(add(add(k.vplus(t_lab), mul(0.55 * alpha(t_lab), v(t_lab))), (0.2, 0.0)),
           sb('α(t) v', 't'), size=14, color=ORANGE, anchor='start')
    f.text((Q[0] + 0.12, Q[1] - 0.04), 'Q', size=15, anchor='start')
    t_c = 0.5 * (a + b)
    f.text(add(Q, mul(alpha(t_c) + 0.12, v(t_c))), sb('Q + α(t) v', 't'), size=14,
           color=ORANGE, anchor='end')
    return f.save(f'{CH8}/mamikon',
                  "Left: a lens K, the intersection of two discs, and the tangent segments from "
                  "v_K^+(t) to z(t) = v_K^+(t) + alpha(t) v_t for t from a to b; along the corner of "
                  "the lens they turn about the corner. They sweep the shaded region between the arc "
                  "and the curve z. Right: the same vectors alpha(t) v_t drawn from a common point "
                  "Q sweep a region of the same area, one half of the integral of alpha(t) squared")


# ---- Figure 8.5: the arc-length parametrization of a convex arc ---------------------------------

def fig_quantile():
    k = KITE
    a, b = KA, KB
    L = k.sigma_cdf(a, b)
    arc = k.arc(a, b, 2000)
    length = sum(math.dist(arc[i], arc[i + 1]) for i in range(len(arc) - 1))
    assert abs(length - L) < 1e-4, (length, L)
    F = lambda t: k.sigma_cdf(a, t) / L
    f = Fig(-0.35, 7.0, -0.3, 2.95, 128)
    # left: the normalized distribution function r = F(t) = sigma_K((a, t]) / L on [a, b]
    X = lambda t: 0.35 + 2.4 * (t - a) / (b - a)
    Y = lambda r: 0.1 + 2.5 * r
    f.line((X(a) - 0.05, Y(0)), (X(b) + 0.35, Y(0)), stroke=FAINT, width=1, arrow=True)
    f.line((X(a), Y(0) - 0.05), (X(a), Y(1) + 0.3), stroke=FAINT, width=1, arrow=True)
    f.text((X(b) + 0.38, Y(0) - 0.12), 't', size=15, anchor='end')
    f.text((X(a) - 0.1, Y(1) + 0.3), 'r', size=15, anchor='end')
    f.text((X(a) - 0.06, Y(1)), '1', size=13, anchor='end', italic=False)
    f.line((X(a) - 0.03, Y(1)), (X(b), Y(1)), stroke=FAINT, width=0.8, dash='2 3')
    for t, s in ((a, 'a'), (k.t1, sb('t', '1')), (k.t2, sb('t', '2')), (b, 'b')):
        f.line((X(t), Y(0) - 0.04), (X(t), Y(0) + 0.04), stroke=FAINT, width=1)
        f.text((X(t), Y(0) - 0.17), s, size=14)
    seg1 = [(X(t), Y(F(t))) for t in np.linspace(a, k.t1, 200)]
    seg2 = [(X(k.t1), Y(F(k.t1 + 1e-9))), (X(k.t2 - 1e-9), Y(F(k.t2 - 1e-9)))]
    seg3 = [(X(t), Y(F(t))) for t in np.linspace(k.t2, b, 200)]
    f.polyline(seg1, stroke=BLUE, width=2.4)
    f.polyline(seg2, stroke=BLUE, width=2.4)
    f.polyline(seg3, stroke=BLUE, width=2.4)
    f.line(seg1[-1], seg2[0], stroke=ORANGE, width=2.4)
    f.line(seg2[-1], seg3[0], stroke=ORANGE, width=2.4)
    f.line((X(k.t1), Y(0)), seg1[-1], stroke=FAINT, width=0.8, dash='2 3')
    f.line((X(k.t2), Y(0)), seg2[-1], stroke=FAINT, width=0.8, dash='2 3')
    f.text((X(k.t1) - 0.08, 0.5 * (seg1[-1][1] + seg2[0][1])), 'edge', size=13, anchor='end',
           color=ORANGE)
    f.text((0.5 * (X(k.t1) + X(k.t2)), seg2[0][1] + 0.15), 'corner', size=13, color=BLUE)
    f.text((X(a) + 0.55, Y(0.62)), 'r = F(t)', size=15, color=BLUE)
    # right: the arc, with the points gamma(s) at s = 0, 1/12, ..., 1
    off = (5.15, 0.95)
    sh = lambda p_: (p_[0] * 0.78 + off[0], p_[1] * 0.78 + off[1])
    f.polygon([sh(p_) for p_ in k.outline()], fill=LBLUE, stroke=FAINT, width=1.0)
    f.polyline([sh(p_) for p_ in arc], stroke=BLUE, width=2.6)
    f.line(sh(k.Q1), sh(k.P), stroke=ORANGE, width=2.6)
    f.line(sh(k.P), sh(k.Q2), stroke=ORANGE, width=2.6)
    cum = [0.0]
    for i in range(len(arc) - 1):
        cum.append(cum[-1] + math.dist(arc[i], arc[i + 1]))
    for j in range(13):
        s = j / 12 * cum[-1]
        i = min(max(np.searchsorted(cum, s) - 1, 0), len(arc) - 2)
        w = (s - cum[i]) / max(cum[i + 1] - cum[i], 1e-15)
        q = add(arc[i], mul(w, sub(arc[i + 1], arc[i])))
        f.dot(sh(q), r=2.8, fill=INK)
    f.text(sh(add(arc[0], (0.2, -0.1))), 'γ(0)', size=14, anchor='start')
    f.text(sh(add(arc[-1], (-0.15, -0.15))), 'γ(1)', size=14, anchor='end')
    f.text(sh((0.1, -0.35)), 'K', size=16, color=BLUE)
    f.text(sh(add(k.P, (0.0, 0.18))), 'P', size=14)
    return f.save(f'{CH8}/quantile',
                  "Left: the normalized distribution function r = F(t) of the surface area measure "
                  "on (a, b) for the body K of Figure 8.2; it rises along the ellipse, jumps at t1 "
                  "and t2 by the lengths of the two edges, and is flat on (t1, t2), the normal "
                  "angles of the corner P. Right: the arc with thirteen points gamma(j/12) at equal "
                  "arc length; the generalized inverse of F gives the normal angle at each point")


def main_ch8():
    check_kite()
    return [fig_midpoint(), fig_curve_area(), fig_cut(), fig_mamikon(), fig_quantile()]


# ---- Chapter 9: Gerver's sofa -------------------------------------------------------------------

GERVER_AREA = 2.2195316688     # Gerver's constant (Romik, Table 1), for the checks only


def xpath(t):
    """The rotation path x(t) of Gerver's sofa (Romik), the inner corner x_K(t) of its cap."""
    return gerver.path(t)


def dxpath(t, h=1e-6):
    a, b = gerver.path(t + h), gerver.path(t - h)
    return ((a[0] - b[0]) / (2 * h), (a[1] - b[1]) / (2 * h))


def curve_A(t):
    """A(t) = x(t) + <x'(t), u_t> v_t + u_t, the contact point with the outer wall a(t)."""
    return add(add(xpath(t), mul(dot(dxpath(t), u(t)), v(t))), u(t))


def curve_B(t):
    """B(t) = x(t) + <x'(t), u_t> v_t, the contact point with the inner wall b(t)."""
    return add(xpath(t), mul(dot(dxpath(t), u(t)), v(t)))


def curve_C(t):
    """C(t) = x(t) - <x'(t), v_t> u_t + v_t, the contact point with the outer wall c(t)."""
    return add(sub(xpath(t), mul(dot(dxpath(t), v(t)), u(t))), v(t))


def curve_D(t):
    """D(t) = x(t) - <x'(t), v_t> u_t, the contact point with the inner wall d(t)."""
    return sub(xpath(t), mul(dot(dxpath(t), v(t)), u(t)))


def outer_corner(t):
    """y_K(t) = x_K(t) + u_t + v_t."""
    return add(add(xpath(t), u(t)), v(t))


class GerverCap:
    """The cap K of Gerver's sofa, from its support function, and the bodies B_K and D_K."""

    def __init__(self):
        self.phi, self.theta = gerver.PHI, gerver.THETA
        self.psi = PI / 2 - self.phi                 # phi^L
        self.t3 = PI / 2 - self.theta
        phases = [self.phi, self.theta, self.t3, self.psi]
        ss = sorted(set(np.linspace(0, PI, 3001).tolist() + phases
                        + [t + PI / 2 for t in phases] + [PI / 2]))
        K = [(-3.0, 0.0), (2.0, 0.0), (2.0, 1.5), (-3.0, 1.5)]        # y >= 0: h_K(3 pi/2) = 0
        for s_ in ss:
            K = clip(K, u(s_), self.h(s_))
        self.K = K
        # B_K = K ∩ ⋂_{t in [phi, pi/2]} H_K^b(t), H_K^b(t) = {p : <p, u_t> >= h_K(t) - 1}
        Bk = K
        for t in sorted(set(np.linspace(self.phi, PI / 2, 1501).tolist() + [self.t3])):
            Bk = clip(Bk, mul(-1, u(t)), 1 - self.h(t))
        self.Bk = Bk
        # D_K = K ∩ ⋂_{t in [0, phi^L]} H_K^d(t), H_K^d(t) = {p : <p, v_t> >= h_K(t + pi/2) - 1}
        Dk = K
        for t in sorted(set(np.linspace(0, self.psi, 1501).tolist() + [self.theta])):
            Dk = clip(Dk, mul(-1, v(t)), 1 - self.h(t + PI / 2))
        self.Dk = Dk
        self.tailB = [curve_B(t) for t in np.linspace(self.t3, PI / 2, 900)]     # b_B, X_B -> W_B
        self.tailD = [curve_D(t) for t in np.linspace(0, self.theta, 900)]       # d_D, Z_D -> Y_D
        self.core = [xpath(t) for t in np.linspace(self.phi, self.psi, 2400)]    # x_K on I
        # the niche: B reversed, the core, D reversed, and the x-axis
        self.N = self.tailB[::-1] + self.core + self.tailD[::-1]
        c, sn = math.cos(self.phi), math.sin(self.phi)
        self.xR, self.xL = xpath(self.phi), xpath(self.psi)
        self.W = ((self.h(self.phi) - 1) / c, 0.0)                # W_K^R on b_K^R and the x-axis
        self.Z = ((1 - self.h(PI - self.phi)) / c, 0.0)           # Z_K^L on d_K^L and the x-axis
        self.WB, self.ZD = self.tailB[-1], self.tailD[0]

    @staticmethod
    def h(s_):
        """h_K(s) for s in [0, pi]: <x(s), u_s> + 1, and <x(s - pi/2), v_{s - pi/2}> + 1."""
        if s_ <= PI / 2:
            return dot(xpath(s_), u(s_)) + 1
        return dot(xpath(s_ - PI / 2), v(s_ - PI / 2)) + 1

    def b_line(self, ymin, ymax):
        """The segment of b_K^R = b_K(phi) = {<p, u_phi> = h_K(phi) - 1} between two heights."""
        c, sn, k = math.cos(self.phi), math.sin(self.phi), self.h(self.phi) - 1
        return [((k - y * sn) / c, y) for y in (ymin, ymax)]

    def d_line(self, ymin, ymax):
        """The segment of d_K^L = d_K(phi^L) = {<p, u_{pi - phi}> = h_K(pi - phi) - 1}."""
        c, sn, k = math.cos(self.phi), math.sin(self.phi), self.h(PI - self.phi) - 1
        return [((y * sn - k) / c, y) for y in (ymin, ymax)]

    def upper_bound_terms(self):
        """The six terms of Q(K, B_K, D_K) (Definition 8.2.2), with X_B = x_K^R, Y_D = x_K^L."""
        return (polygon_area(self.K), curve_area(self.tailD), seg_area(self.tailD[-1], self.xL),
                -curve_area(self.core), seg_area(self.xR, self.tailB[0]), curve_area(self.tailB))


def support(poly, t):
    return max(dot(p_, u(t)) for p_ in poly)


def check_gerver(g):
    area_K, area_N = polygon_area(g.K), polygon_area(g.N)
    assert abs(area_K - area_N - GERVER_AREA) < 1e-4, area_K - area_N
    # the niche: |N(K)| = J(x|_I) - J(B) - J(D) (Theorem 8.4.1 (2))
    assert abs(area_N - (curve_area(g.core) - curve_area(g.tailB) - curve_area(g.tailD))) < 1e-6
    # the tails end where the core begins: X_B = B(t3) = x(phi), Y_D = D(theta) = x(phi^L)
    assert math.dist(g.tailB[0], g.xR) < 1e-6 and math.dist(g.tailD[-1], g.xL) < 1e-6
    assert abs(g.WB[1]) < 1e-9 and abs(g.ZD[1]) < 1e-9
    # Q(K, B_K, D_K) = A(K) = |G| (Theorem 8.4.6)
    assert abs(sum(g.upper_bound_terms()) - (area_K - area_N)) < 1e-6
    # Lemma 8.1.7: h_K(t) + h_B(pi + t) <= 1 on [phi, pi/2], = 1 at phi and pi/2 (and on [t3, pi/2],
    # Theorem 8.4.3 (3)); likewise for D_K
    for t in np.linspace(g.phi, PI / 2, 60):
        val = g.h(t) + support(g.Bk, PI + t)
        assert val <= 1 + 1e-6 and (t < g.t3 - 1e-9 or abs(val - 1) < 1e-4), (t, val)
    for t in np.linspace(0, g.psi, 60):
        val = g.h(PI / 2 + t) + support(g.Dk, 3 * PI / 2 + t)
        assert val <= 1 + 1e-6 and (t > g.theta + 1e-9 or abs(val - 1) < 1e-4), (t, val)
    for t in (g.phi, PI / 2):
        assert abs(g.h(t) + support(g.Bk, PI + t) - 1) < 1e-6
    for t in (0, g.psi):
        assert abs(g.h(PI / 2 + t) + support(g.Dk, 3 * PI / 2 + t) - 1) < 1e-6
    # Lemma 8.1.4: K ∩ H^R and K ∩ H^L are disjoint (B_K and D_K lie in them)
    assert max(p_[0] for p_ in g.Dk) < min(p_[0] for p_ in g.Bk)
    # Lemma 8.1.5: W_K^R and Z_K^L lie inside the bottom edge, from C_K(pi/2) to A_K(0) = (1, 0)
    assert -g.h(PI) < g.Z[0] < g.W[0] < 1 and math.dist(curve_A(0), (1.0, 0.0)) < 1e-9
    # Lemma 8.1.6: x_K(t) lies outside H^R for t in (phi, pi/2], outside H^L for t in [0, phi^L)
    for t in np.linspace(g.phi, PI / 2, 80)[1:]:
        assert dot(xpath(t), u(g.phi)) < g.h(g.phi) - 1
    for t in np.linspace(0, g.psi, 80)[:-1]:
        assert dot(xpath(t), u(PI - g.phi)) < g.h(PI - g.phi) - 1
    # 2 sec(phi) + 2 tan(phi) < 2.2 and sec(phi) < 1.1 (Lemmas 8.1.4, 8.1.5)
    assert 2 / math.cos(g.phi) + 2 * math.tan(g.phi) < 2.2 and 1 / math.cos(g.phi) < 1.1


GERVER = None


def gerver_cap():
    global GERVER
    if GERVER is None:
        GERVER = GerverCap()
        check_gerver(GERVER)
    return GERVER


# ---- Figure 9.1: the cap, the bodies B_K and D_K, the core and the tails --------------------------

def fig_bodies():
    g = gerver_cap()
    f = Fig(-2.42, 1.22, -0.36, 1.18, 215)
    G = [p_ for p_ in gerver.outline(900, 8000)]
    f.polygon(g.K, fill=LBLUE, stroke=BLUE, width=1.4)
    f.polygon(g.N, fill='#ffffff', stroke='none', width=0)
    f.polygon(g.N, fill=LORANGE, stroke='none', width=0, opacity=0.7)
    f.polygon(g.Bk, fill=LGREEN, stroke=GREEN, width=1.2, opacity=0.85)
    f.polygon(g.Dk, fill=LGREEN, stroke=GREEN, width=1.2, opacity=0.85)
    for seg in (g.b_line(-0.12, 1.1), g.d_line(-0.12, 1.1)):
        f.line(seg[0], seg[1], stroke=FAINT, width=1.1, dash='5 4')
    f.polyline(g.core, stroke=ORANGE, width=2.6)
    f.polyline(g.tailB, stroke=GREEN, width=2.6)
    f.polyline(g.tailD, stroke=GREEN, width=2.6)
    f.line((-2.4, 0), (1.2, 0), stroke=FAINT, width=0.8)
    for q in (g.xR, g.xL, g.WB, g.ZD, g.W, g.Z):
        f.dot(q, r=2.9)
    f.text((0.62, 0.55), 'B', size=19, color=GREEN)
    f.text((-1.85, 0.55), 'D', size=19, color=GREEN)
    f.text((-0.62, 0.86), 'K', size=19, color=BLUE)
    f.text((-0.62, 0.33), subsup(bold('x'), 'K', ''), size=16, color=ORANGE)
    f.text(g.b_line(0, 1.1)[1], subsup('b', 'K', 'R'), size=15, anchor='start', dx=5, dy=4)
    f.text(g.d_line(0, 1.1)[1], subsup('d', 'K', 'L'), size=15, anchor='end', dx=-5, dy=4)
    # labels of the points, with leader lines where they are crowded
    def callout(q, at, s, anchor='middle'):
        f.line(q, at, stroke=FAINT, width=0.7)
        f.text(at, s, size=13, anchor=anchor, dx=(4 if anchor == 'start' else
                                                    -4 if anchor == 'end' else 0),
               dy=(9 if at[1] < q[1] else -9))
    callout(g.xR, (0.18, 0.2), seq((bold('x'), 'n'), ('K', 'sub'), ('R', 'over'), (' = X', 'n'),
                                   ('B', 'sub'), size=13), 'start')
    callout(g.xL, (-1.4, 0.2), seq((bold('x'), 'n'), ('K', 'sub'), ('L', 'over'), (' = Y', 'n'),
                                   ('D', 'sub'), size=13), 'end')
    callout(g.W, (-0.12, -0.19), subsup('W', 'K', 'R', size=13))
    callout(g.WB, (0.3, -0.19), sb('W', 'B', size=13))
    callout(g.Z, (-1.12, -0.19), subsup('Z', 'K', 'L', size=13))
    callout(g.ZD, (-1.52, -0.19), sb('Z', 'D', size=13))
    f.text((0.32, 0.075), bold('b') + sb('', 'B', size=15), size=15, color=GREEN, anchor='start')
    f.text((-1.47, 0.075), bold('d') + sb('', 'D', size=15), size=15, color=GREEN, anchor='end')
    return f.save(f'{CH9}/bodies',
                  "The cap K of Gerver's sofa, blue, between the x-axis and the line y = 1, with "
                  "its niche shaded orange. The green bodies B and D are the parts of K on the far "
                  "sides of the inner walls b_K(t), t from phi to pi/2, and d_K(t), t from 0 to "
                  "phi^L; the dashed lines are b_K^R and d_K^L. The tails b_B and d_D, green, are "
                  "the lower boundaries of B and D, and the core x_K on [phi, phi^L], orange, joins "
                  "their ends x_K^R = X_B and x_K^L = Y_D")


# ---- Figure 9.2: the right tail ----------------------------------------------------------------

def tail_alpha(g, t):
    """For s = pi + t, t in [phi, pi/2): the length of the tangent segment of R_B from v_B^+(s) along
    v_s = -v_t down to the x-axis. v_B^+(pi + t) is X_B = x_K^R for t <= t3 and B(t) after."""
    q = g.xR if t <= g.t3 else curve_B(t)
    return q[1] / math.cos(t)


def fig_tail():
    g = gerver_cap()
    c = math.cos(g.phi)
    # the right part of the niche: N ∩ H^R, H^R = {<p, u_phi> >= h_K(phi) - 1}
    right = clip(g.N, mul(-1, u(g.phi)), 1 - g.h(g.phi))
    tri = [g.xR, g.W, g.WB]                       # v_B^+(pi + phi), v_B(pi + phi, 3 pi/2), v_B^-(3 pi/2)
    J_lower = seg_area(g.xR, g.W) - curve_area(g.tailB)          # Lemma 8.2.2
    R_B = simpson(lambda t: tail_alpha(g, t) ** 2, g.phi, PI / 2 - 1e-7, 4000) / 2   # Theorem 7.4.1
    assert abs(polygon_area(right) - J_lower) < 1e-7, (polygon_area(right), J_lower)
    assert abs(R_B - J_lower) < 1e-6, (R_B, J_lower)
    # the triangle is the union of the right part of the niche and the part of B inside it
    tri_B = g.Bk
    for a_, b_ in zip(tri, tri[1:] + tri[:1]):
        n = (b_[1] - a_[1], a_[0] - b_[0])           # outer normal of the counterclockwise edge
        tri_B = clip(tri_B, n, dot(a_, n))
    assert polygon_area(tri) > 0
    assert abs(polygon_area(tri) - polygon_area(tri_B) - polygon_area(right)) < 1e-7
    f = Fig(-0.075, 0.27, -0.026, 0.1, 1850)
    f.polygon(g.K, fill=LBLUE, stroke=BLUE, width=1.2)
    f.polygon(g.Bk, fill=LGREEN, stroke=GREEN, width=1.2)
    f.polygon(right, fill=LORANGE, stroke='none', width=0)
    f.polygon(clip(g.N, u(g.phi), g.h(g.phi) - 1), fill=LORANGE, stroke='none', width=0,
              opacity=0.55)
    # the tangent segments of R_B: a fan at X_B, then from the tail down to the x-axis
    for t in np.linspace(g.phi, PI / 2 - 0.02, 34):
        q = g.xR if t <= g.t3 else curve_B(t)
        f.line(q, add(q, mul(tail_alpha(g, t), mul(-1, v(t)))), stroke=ORANGE, width=0.7)
    f.polygon(tri, fill='none', stroke=INK, width=1.0, dash='4 3')
    f.polyline(g.tailB, stroke=GREEN, width=2.6)
    f.polyline(g.core[:400], stroke=ORANGE, width=2.6)
    f.line(*g.b_line(-0.03, 0.1), stroke=FAINT, width=1.1, dash='5 4')
    f.line((-0.075, 0), (0.27, 0), stroke=FAINT, width=0.8)
    for q in (g.xR, g.W, g.WB):
        f.dot(q, r=3.2)
    f.text(add(g.xR, (-0.006, 0.006)), seq((bold('x'), 'n'), ('K', 'sub'), ('R', 'over'),
                                         (' = X', 'n'), ('B', 'sub'), size=14), size=14,
           anchor='end')
    f.text(add(g.W, (-0.004, -0.012)), subsup('W', 'K', 'R', size=14), size=14, anchor='end')
    f.text(add(g.WB, (0.0, -0.014)), sb('W', 'B', size=14), size=14)
    f.text((0.17, 0.045), 'B', size=19, color=GREEN)
    f.text((0.135, 0.019), bold('b') + sb('', 'B', size=15), size=15, color=GREEN, anchor='start')
    f.text((-0.045, 0.05), 'core', size=14, color=ORANGE)
    f.text(g.b_line(0, 0.1)[1], subsup('b', 'K', 'R', size=14), size=14, anchor='start', dx=5,
           dy=8)
    return f.save(f'{CH9}/tail',
                  "A close-up of the right tail of the niche of Gerver's sofa. The dashed triangle "
                  "has vertices x_K^R = X_B, W_K^R and W_B. The part of the niche to the right of "
                  "the line b_K^R, orange, is the triangle minus the body B; the tangent segments "
                  "of B, a fan at X_B and then segments from the tail b_B down to the x-axis, sweep "
                  "it")


# ---- Figure 9.3: the core part of the niche ----------------------------------------------------------

def fig_core():
    g = gerver_cap()
    H = 0.27
    # Lemma 8.1.6 and the injectivity condition: the first coordinate of the core decreases strictly
    xs = [q[0] for q in g.core]
    assert all(b_ < a_ for a_, b_ in zip(xs, xs[1:]))
    middle = clip(clip(g.N, u(g.phi), g.h(g.phi) - 1), u(PI - g.phi), g.h(PI - g.phi) - 1)
    J_core = seg_area(g.W, g.xR) + curve_area(g.core) + seg_area(g.xL, g.Z)      # Lemma 8.2.3
    assert abs(polygon_area(middle) - J_core) < 1e-7, (polygon_area(middle), J_core)
    bl, dl = g.b_line(-H, 0), g.d_line(-H, 0)
    region = [bl[0]] + [g.xR] + g.core + [g.xL] + [dl[0]]      # between the core and y = -H
    trap = [dl[0], bl[0], g.W, g.Z]                           # the trapezoid below the x-axis
    assert abs(polygon_area(region) - polygon_area(trap) - J_core) < 1e-7
    f = Fig(-1.47, 0.24, -0.36, 0.75, 330)
    f.polygon(region, fill=LORANGE, stroke='none', width=0)
    f.polygon(trap, fill=GREY, stroke=FAINT, width=1.0, dash='4 3')
    for xv in np.linspace(-1.15, -0.07, 10):
        i = min(range(len(g.core)), key=lambda j: abs(g.core[j][0] - xv))
        f.line((xv, -H), (xv, g.core[i][1]), stroke=ORANGE, width=0.6, dash='2 3')
    f.polyline(g.core, stroke=ORANGE, width=2.6)
    f.polyline(g.tailB, stroke=GREEN, width=2.2)
    f.polyline(g.tailD, stroke=GREEN, width=2.2)
    f.line(*g.b_line(-H - 0.05, 0.72), stroke=FAINT, width=1.1, dash='5 4')
    f.line(*g.d_line(-H - 0.05, 0.72), stroke=FAINT, width=1.1, dash='5 4')
    f.line((-1.47, 0), (0.24, 0), stroke=INK, width=0.9)
    f.line((-1.47, -H), (0.24, -H), stroke=FAINT, width=0.9)
    for q in (g.xR, g.xL, g.W, g.Z, bl[0], dl[0]):
        f.dot(q, r=2.8)
    f.text((-0.61, 0.25), 'core part', size=15, color=ORANGE)
    f.text((-0.61, -0.14), 'trapezoid', size=14, color=FAINT)
    f.text((-1.45, -H + 0.025), 'y = −H', size=13, anchor='start', color=FAINT)
    f.text((-1.45, 0.025), 'y = 0', size=13, anchor='start', color=FAINT)
    f.text(add(g.xR, (0.03, 0.03)), seq((bold('x'), 'n'), ('K', 'sub'), ('R', 'over'), size=14),
           size=14, anchor='start')
    f.text(add(g.xL, (-0.03, 0.03)), seq((bold('x'), 'n'), ('K', 'sub'), ('L', 'over'), size=14),
           size=14, anchor='end')
    f.text(add(g.W, (0.035, -0.04)), subsup('W', 'K', 'R', size=13), size=13, anchor='start')
    f.text(add(g.Z, (-0.035, -0.04)), subsup('Z', 'K', 'L', size=13), size=13, anchor='end')
    f.text(g.b_line(0, 0.72)[1], subsup('b', 'K', 'R', size=14), size=14, anchor='start', dx=5,
           dy=6)
    f.text(g.d_line(0, 0.72)[1], subsup('d', 'K', 'L', size=14), size=14, anchor='end', dx=-5,
           dy=6)
    return f.save(f'{CH9}/core',
                  "The core part of the niche of Gerver's sofa, between the lines b_K^R and d_K^L "
                  "(dashed) and under the core x_K on [phi, phi^L], orange. Together with the grey "
                  "trapezoid below the x-axis it forms the region between the core and the line "
                  "y = -H, which every vertical line meets in a single segment, since the first "
                  "coordinate of x_K decreases")


# ---- Figure 9.4: the Mamikon regions above the cap ---------------------------------------------------

def fig_mamikon_cap():
    g = gerver_cap()
    hK = g.h
    psi, phi = g.psi, g.phi

    def vplusK(s_):
        """v_K^+(s) of Gerver's cap for s in [0, pi]: A(s), then C(s - pi/2); C(0) at s = pi/2."""
        return curve_A(s_) if s_ < PI / 2 else curve_C(s_ - PI / 2)

    def mamikon_area(a, b, z, arc):
        """M_K(a, b; z) = J(v_K^+(a), z(a)) + J(z) + J(z(b), v_K^-(b)) - J(u_K^{a,b})."""
        zs = [z(s_) for s_ in np.linspace(a, b, 3000)]
        return seg_area(arc[0], zs[0]) + curve_area(zs) + seg_area(zs[-1], arc[-1]) - curve_area(arc)

    # the four Mamikon terms of S_K (Definition 8.3.2) and their arcs of the boundary of K
    corner = [curve_A(0)]                                          # u_K^{0, phi}: the corner (1, 0)
    arc2 = [curve_A(t) for t in np.linspace(phi, psi, 3000)]
    arc3 = [curve_A(t) for t in np.linspace(psi, PI / 2, 600)]
    arc4 = [curve_C(t) for t in np.linspace(0, PI / 2, 3000)]
    S_K = (mamikon_area(0, phi, lambda s_: vint(hK, s_, PI / 2), corner)
           + mamikon_area(phi, psi, outer_corner, arc2)
           + mamikon_area(psi, PI / 2, lambda s_: vint(hK, s_, PI - phi), arc3)
           + mamikon_area(PI / 2, PI - 1e-9, lambda s_: vint(hK, s_, PI), arc4))
    P_K = (polygon_area(g.K) + seg_area(g.Z, g.xL) - curve_area(g.core)
           + seg_area(g.xR, g.W))                                  # Definition 8.3.4
    # the region U: K and the four swept regions, bounded by segments and the curve y_K
    yK = [outer_corner(s_) for s_ in np.linspace(phi, psi, 600)]
    U = ([(1.0, 0.0), (1.0, 1.0), vint(hK, phi, PI / 2)] + yK
         + [vint(hK, PI / 2, PI - phi), (-hK(PI), 1.0), (-hK(PI), 0.0)])
    core_part = [g.W, g.xR] + g.core + [g.xL, g.Z]
    U_minus = U + [g.Z, g.xL] + g.core[::-1] + [g.xR, g.W]       # U minus the core part
    assert abs(polygon_area(U_minus) - (S_K + P_K)) < 1e-5, (polygon_area(U_minus), S_K + P_K)
    assert abs(polygon_area(U) - polygon_area(core_part) - polygon_area(U_minus)) < 1e-9
    # the tangent segments, from v_K^+(s) along v_s
    fam = ([(s_, vplusK(s_), vint(hK, s_, PI / 2)) for s_ in np.linspace(0, phi, 6)]
           + [(s_, vplusK(s_), outer_corner(s_)) for s_ in np.linspace(phi, psi, 40)]
           + [(s_, vplusK(s_), vint(hK, s_, PI - phi)) for s_ in np.linspace(psi, PI / 2, 7)]
           + [(s_, vplusK(s_), vint(hK, s_, PI)) for s_ in np.linspace(PI / 2, PI - 1e-6, 24)])
    for s_, a_, b_ in fam:
        assert abs(dot(a_, u(s_)) - hK(s_)) < 1e-6 and abs(dot(b_, u(s_)) - hK(s_)) < 1e-6, s_
        assert dot(sub(b_, a_), v(s_)) >= -1e-9         # alpha >= 0: the segments point along v_s
    f = Fig(-2.78, 1.62, -0.08, 2.2, 168)
    f.polygon(U, fill=LPURPLE, stroke='none', width=0)
    f.polygon(g.K, fill=LBLUE, stroke=BLUE, width=1.2)
    f.polygon(g.N, fill=LORANGE, stroke='none', width=0)
    f.polygon(core_part, fill='#ffffff', stroke='none', width=0)
    for s_, a_, b_ in fam:
        f.line(a_, b_, stroke=PURPLE, width=0.55)
    f.polyline(g.core, stroke=ORANGE, width=2.2)
    f.polygon(U_minus, fill='none', stroke=INK, width=1.8)
    for q in (outer_corner(phi), outer_corner(psi)):
        f.dot(q, r=2.8)
    f.text(add(outer_corner(phi), (0.05, 0.0)), seq((bold('y'), 'n'), ('K', 'sub'),
                                                   ('(φ', 'n'), ('R', 'sup'), (')', 'n'), size=14),
           size=14, anchor='start')
    f.text(add(outer_corner(psi), (-0.05, 0.0)), seq((bold('y'), 'n'), ('K', 'sub'),
                                                    ('(φ', 'n'), ('L', 'sup'), (')', 'n'), size=14),
           size=14, anchor='end')
    f.text((-0.61, 2.13), seq((bold('y'), 'n'), ('K', 'sub'), size=15), size=15, color=PURPLE)
    f.text((-0.61, 0.84), 'K', size=18, color=BLUE)
    f.text((-0.61, 0.2), 'core part', size=13, color=ORANGE)
    f.text((1.06, 0.5), '1', size=14, color=PURPLE, anchor='start')
    f.text((0.3, 1.5), '2', size=14, color=PURPLE)
    f.text((-1.75, 1.032), '3', size=11, color=PURPLE)
    f.text((-2.13, 0.84), '4', size=14, color=PURPLE)
    return f.save(f'{CH9}/mamikon-cap',
                  "The cap K of Gerver's sofa and four regions swept by tangent segments of K, "
                  "purple: 1, a thin fan at the corner (1, 0) up to the line y = 1; 2, the segments "
                  "from A_K(t) to the outer corner y_K(t), t from phi to phi^L; 3, a thin wedge "
                  "above the top edge; 4, the segments from the left side of K to the vertical line "
                  "x = -h_K(pi). The bold outline encloses K and the four regions, minus the core "
                  "part of the niche, white")


# ---- Figure 9.5: the chain of inequalities ----------------------------------------------------------

def fig_chain():
    g = gerver_cap()
    area_G = polygon_area(g.K) - polygon_area(g.N)
    assert abs(sum(g.upper_bound_terms()) - area_G) < 1e-6     # Q(K_G, B, D) = A(K_G) = |G|
    W, H = 700, 352
    f = Fig(0, W, 0, H, 1, pad=10)
    P = lambda x_, y_: (x_, H - y_)                  # top-down pixel coordinates
    boxes = [
        ('|S|', LBLUE, BLUE),
        ('A(K) = |K| − |N(K)|', LBLUE, BLUE),
        (seq(('Q(K, B', 'n'), ('K', 'sub'), (', D', 'n'), ('K', 'sub'), (')', 'n'), size=16),
         LORANGE, ORANGE),
        (seq(('Q(K', 'n'), ('G', 'sub'), (', B', 'n'), ('G', 'sub'), (', D', 'n'), ('G', 'sub'),
             (')', 'n'), size=16), LORANGE, ORANGE),
        ('|G| = 2.2195…', LBLUE, BLUE),
    ]
    reasons = [
        ('≤', 'K: a balanced maximum cap with rotation angle π/2',
         '(Chapters 3 to 5)'),
        ('≤', 'K satisfies the injectivity condition (Chapter 7);',
         'Q bounds the sofa area functional (Section 9.2)'),
        ('≤', 'Q is concave (Section 9.3), and its directional',
         'derivatives at Gerver\'s triple are ≤ 0 (Section 9.4)'),
        ('=', 'the bound is attained at Gerver\'s sofa',
         '(Chapter 10)'),
    ]
    bw, bh, x0, gap = 236, 36, 18, 43
    for i, (label, fill, stroke) in enumerate(boxes):
        y0 = i * (bh + gap)
        f.polygon([P(x0, y0), P(x0 + bw, y0), P(x0 + bw, y0 + bh), P(x0, y0 + bh)], fill=fill,
                  stroke=stroke, width=1.4)
        f.text(P(x0 + bw / 2, y0 + bh / 2 + 1), label, size=16)
        if i < len(reasons):
            sym, r1, r2 = reasons[i]
            yc = y0 + bh + gap / 2
            f.text(P(x0 + bw / 2, yc + 1), sym, size=20, italic=False)
            f.line(P(x0 + bw + 12, yc), P(x0 + bw + 40, yc), stroke=FAINT, width=1)
            f.text(P(x0 + bw + 48, yc - 8), r1, size=13, anchor='start', italic=False)
            f.text(P(x0 + bw + 48, yc + 9), r2, size=13, anchor='start', italic=False)
    return f.save(f'{CH9}/chain',
                  "The chain of the proof of the main theorem, from top to bottom: the area of a "
                  "moving sofa S is at most the sofa area functional A(K) of a balanced maximum cap "
                  "K, at most Q(K, B_K, D_K), at most the value of Q at Gerver's triple, which "
                  "equals the area 2.2195... of Gerver's sofa G; each step names the property used")


def main_ch9():
    return [fig_bodies(), fig_tail(), fig_core(), fig_mamikon_cap(), fig_chain()]


def main():
    paths = main_ch8() + main_ch9()
    for p_ in paths:
        print(f'wrote {p_.relative_to(OUT.parents[2])} ({p_.stat().st_size // 1024} KiB)')


if __name__ == '__main__':
    main()
