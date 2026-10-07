#!/usr/bin/env python3
"""The figures of Chapters 2 and 3, in baek/proof/figures/02-preliminaries/ and
baek/proof/figures/03-monotone/.

    python3 scripts/figures/fig_monotone.py

Chapter 2 draws the frame u_t, v_t with a line and a half-plane, the hallway with Gerver's sofa
moving in it, a convex body with its support function, edge and vertices, the limits of Theorem 2.9
(Baek's Theorem 2.1.3), a sofa with rotation angle 1.2 in standard position and in its own frame of
reference, the supporting hallway, and the push of a hallway onto its supporting hallway. Chapter 3
draws the monotonization of a disk, Gerver's sofa as the intersection of its supporting hallways,
its cap and its niche, the fan, a wedge with its ends and gaps, the mirror reflection, and a wide
cap that does not contain its niche.

Everything is computed from the definitions. Gerver's sofa is the shape of Romik's rotation path
x(t) (gerver.py); the hallways x(t) + R_t L are its supporting hallways, which is checked. The other
caps are intersections of half-planes. A niche is the union of the open quadrants
Q⁻_K(t) = {p : <p - x_K(t), u_t> < 0, <p - x_K(t), v_t> < 0}, t in (0, ω), cut by the fan: each
quadrant is closed downwards, so the niche is the region between the lower boundary of the fan and
the roof sup_t of the tops of the quadrants. Every fact that a caption states is checked by an
assertion.
"""
import math

import numpy as np

import gerver
from sofa_figures import Figure, INK, FAINT, WALL, FLOOR, COLORS, FILLS, GREY, hallway, sb, sp

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
LBLUE, LORANGE, LGREEN, LPURPLE = FILLS[0], FILLS[1], FILLS[2], FILLS[3]
CH2, CH3 = '02-preliminaries', '03-monotone'


# ---- plane geometry ---------------------------------------------------------------------------

def u(t):
    return np.array((math.cos(t), math.sin(t)))


def v(t):
    return np.array((-math.sin(t), math.cos(t)))


def rot(t, p):
    c, s = math.cos(t), math.sin(t)
    return np.array((c * p[0] - s * p[1], s * p[0] + c * p[1]))


def P(p):
    return (float(p[0]), float(p[1]))


def Ps(ps):
    return [P(p) for p in ps]


def clip(poly, n, c):
    """The part of a polygon where <p, n> <= c (one step of Sutherland–Hodgman)."""
    out = []
    m = len(poly)
    for i in range(m):
        p, q = np.asarray(poly[i], float), np.asarray(poly[(i + 1) % m], float)
        fp, fq = p @ n - c, q @ n - c
        if fp <= 0:
            out.append(p)
        if fp * fq < 0:
            out.append(p + fp / (fp - fq) * (q - p))
    return out


def box(xmin, xmax, ymin, ymax):
    return [np.array(p, float) for p in ((xmin, ymin), (xmax, ymin), (xmax, ymax), (xmin, ymax))]


def clip_box(poly, win):
    xmin, xmax, ymin, ymax = win
    for n, c in (((1, 0), xmax), ((-1, 0), -xmin), ((0, 1), ymax), ((0, -1), -ymin)):
        poly = clip(poly, np.array(n, float), c)
    return poly


def halfplanes(hps, big=80.0):
    """The convex polygon cut out by the half-planes <p, n> <= c of the list hps."""
    poly = box(-big, big, -big, big)
    for n, c in hps:
        poly = clip(poly, np.asarray(n, float), c)
    return np.array(poly)


def area(poly):
    x, y = np.asarray(poly)[:, 0], np.asarray(poly)[:, 1]
    return 0.5 * abs(float(x @ np.roll(y, -1) - y @ np.roll(x, -1)))


def in_convex(poly, p, eps=1e-9):
    """Whether p lies in the convex polygon poly (counterclockwise)."""
    poly = np.asarray(poly)
    q = np.roll(poly, -1, axis=0)
    cr = (q[:, 0] - poly[:, 0]) * (p[1] - poly[:, 1]) - (q[:, 1] - poly[:, 1]) * (p[0] - poly[:, 0])
    return bool(np.all(cr >= -eps))


def seg_in_box(a, b, win):
    """The part of the segment [a, b] inside the window (Liang–Barsky), or None."""
    xmin, xmax, ymin, ymax = win
    d = b - a
    lo, hi = 0.0, 1.0
    for p, q in ((-d[0], a[0] - xmin), (d[0], xmax - a[0]), (-d[1], a[1] - ymin),
                 (d[1], ymax - a[1])):
        if abs(p) < 1e-15:
            if q < 0:
                return None
        else:
            r = q / p
            if p < 0:
                lo = max(lo, r)
            else:
                hi = min(hi, r)
    if lo > hi:
        return None
    return a + lo * d, a + hi * d


def draw_line(f, p, d, win, big=60.0, **kw):
    """The line p + λd, clipped to the window."""
    s = seg_in_box(p - big * d, p + big * d, win)
    if s is not None:
        f.line(P(s[0]), P(s[1]), **kw)


def draw_ray(f, p, d, win, big=60.0, **kw):
    s = seg_in_box(p, p + big * d, win)
    if s is not None:
        f.line(P(s[0]), P(s[1]), **kw)


def subsup(base, sub_, sup_, after=''):
    """A label with a subscript followed by a superscript, as v_K⁺(t) is printed."""
    return sb(base, sub_, sup_ + after)


def text(f, p, s, size=15, color=INK, anchor='start', dx=0.0, dy=0.0, italic=True):
    """A label whose left end (by default) is at p + (dx, dy)."""
    f.text((float(p[0]) + dx, float(p[1]) + dy), s, size=size, color=color, anchor=anchor,
           italic=italic)


def arc(c, r, a, b, n=60):
    return [c + r * u(s) for s in np.linspace(a, b, n)]


# ---- hallways ---------------------------------------------------------------------------------

BIG = 40.0
L_FLOOR = [np.array(p, float) for p in ((-BIG, 0), (0, 0), (0, -BIG), (1, -BIG), (1, 1), (-BIG, 1))]
L_OUTER = [np.array(p, float) for p in ((-BIG, 1), (1, 1), (1, -BIG))]
L_INNER = [np.array(p, float) for p in ((-BIG, 0), (0, 0), (0, -BIG))]


def moved(x, t, ps):
    """The points of ps under p ↦ x + R_t p, which maps L onto the hallway x + R_t L."""
    return [x + rot(t, p) for p in ps]


def draw_polyline_clipped(f, ps, win, **kw):
    for a, b in zip(ps, ps[1:]):
        s = seg_in_box(a, b, win)
        if s is not None:
            f.line(P(s[0]), P(s[1]), **kw)


def draw_hallway(f, x, t, win, floor=FLOOR, wall=WALL, width=2.2, dash=None, opacity=1.0):
    """The hallway x + R_t L, clipped to the window: its floor, then its walls."""
    if floor is not None:
        f.polygon(Ps(clip_box(moved(x, t, L_FLOOR), win)), fill=floor, stroke='none', width=0,
                  opacity=opacity)
    if wall is not None:
        draw_polyline_clipped(f, moved(x, t, L_OUTER), win, stroke=wall, width=width, dash=dash)
        draw_polyline_clipped(f, moved(x, t, L_INNER), win, stroke=wall, width=width, dash=dash)


# ---- caps and niches --------------------------------------------------------------------------

def fan_floor(omega, xs):
    """The lower boundary of the fan F_ω = {y >= 0, <p, u_ω> >= 0} over the abscissae xs."""
    xs = np.asarray(xs, float)
    if omega >= PI / 2 - 1e-12:
        return np.zeros_like(xs)
    return np.maximum(0.0, -xs / math.tan(omega))


def roof(corner, omega, xs, n=1500):
    """The top of the niche over xs: the supremum over t in (0, ω) of the tops of the vertical
    slices of the open quadrants Q⁻(t) with corners corner(t), each of which is closed downwards."""
    xs = np.asarray(xs, float)
    r = np.full(len(xs), -np.inf)
    for t in np.linspace(0, omega, n + 1)[1:-1]:
        x1, x2 = corner(t)
        c, s = math.cos(t), math.sin(t)
        r = np.maximum(r, np.minimum(x2 - (xs - x1) * c / s, x2 + (xs - x1) * s / c))
    return r


def regions(xs, lo, hi):
    """The polygons {(x, y) : lo(x) <= y <= hi(x)}, one for each run of abscissae where lo < hi."""
    xs, lo, hi = np.asarray(xs), np.asarray(lo), np.asarray(hi)
    good = hi > lo + 1e-12
    out, i, n = [], 0, len(xs)
    while i < n:
        if not good[i]:
            i += 1
            continue
        j = i
        while j + 1 < n and good[j + 1]:
            j += 1
        k = slice(i, j + 1)
        out.append(list(zip(xs[k], lo[k])) + list(zip(xs[k][::-1], hi[k][::-1])))
        i = j + 1
    return out


def region(xs, lo, hi):
    """The polygon {(x, y) : lo(x) <= y <= hi(x)}, which must be a single piece."""
    parts = regions(xs, lo, hi)
    assert len(parts) == 1, len(parts)
    return parts[0]


class PolyCap:
    """A cap with rotation angle ω given as a convex polygon (counterclockwise)."""

    def __init__(self, omega, poly):
        self.omega = omega
        self.poly = np.asarray(poly, float)
        assert self.is_cap(), 'not a cap'

    def h(self, t):
        return float(np.max(self.poly @ u(t)))

    def corner(self, t):
        """The inner corner x_K(t) = (h(t) - 1) u_t + (h(t + π/2) - 1) v_t."""
        return (self.h(t) - 1) * u(t) + (self.h(t + PI / 2) - 1) * v(t)

    def outer(self, t):
        """The outer corner y_K(t) = h(t) u_t + h(t + π/2) v_t."""
        return self.h(t) * u(t) + self.h(t + PI / 2) * v(t)

    def is_cap(self):
        w = self.omega
        return (abs(self.h(w) - 1) < 1e-9 and abs(self.h(PI / 2) - 1) < 1e-9
                and abs(self.h(w + PI)) < 1e-9 and abs(self.h(3 * PI / 2)) < 1e-9)

    def vertical(self, xs):
        """The bottom and the top of K over the abscissae xs (nan outside K)."""
        lo, hi = [], []
        p = self.poly
        q = np.roll(p, -1, axis=0)
        for x in xs:
            ys = []
            for a, b in zip(p, q):
                if (a[0] - x) * (b[0] - x) <= 0 and a[0] != b[0]:
                    ys.append(a[1] + (x - a[0]) / (b[0] - a[0]) * (b[1] - a[1]))
            lo.append(min(ys) if ys else np.nan)
            hi.append(max(ys) if ys else np.nan)
        return np.array(lo), np.array(hi)

    def niche_contained(self, n=600):
        """Theorem 2.5.8 (3): every inner corner in the open fan lies in K."""
        w = self.omega
        for t in np.linspace(0, w, n + 1)[1:-1]:
            x = self.corner(t)
            if x[1] > 1e-12 and x @ u(w) > 1e-12 and not in_convex(self.poly, x):
                return False
        return True

    def parts(self, m=900, n=1500):
        """xs, the fan floor, the roof of the niche and the top of K over xs."""
        xs = np.linspace(self.poly[:, 0].min(), self.poly[:, 0].max(), m + 1)
        floor = fan_floor(self.omega, xs)
        lo, hi = self.vertical(xs)
        assert np.allclose(lo, floor, atol=1e-7), 'the bottom of a cap is the floor of the fan'
        return xs, floor, roof(self.corner, self.omega, xs, n), hi


def rounded_cap(omega, a, b, rho, n=80):
    """The cap P_ω ∩ {x <= a} ∩ {<p, v_ω> <= b}, with its two upper corners rounded by circular arcs
    of radius rho; the arcs have normal angles in [0, ω] and [π/2, ω + π/2]."""
    cr = np.linalg.solve(np.array([u(0), u(omega)]), [a - rho, 1 - rho])
    cq = np.linalg.solve(np.array([u(PI / 2), u(omega + PI / 2)]), [1 - rho, b - rho])
    hps = [(u(PI / 2), 1.0), (-u(PI / 2), 0.0), (u(omega), 1.0), (-u(omega), 0.0),
           (u(0), a), (u(omega + PI / 2), b)]
    hps += [(u(s), cr @ u(s) + rho) for s in np.linspace(0, omega, n)]
    hps += [(u(s), cq @ u(s) + rho) for s in np.linspace(PI / 2, omega + PI / 2, n)]
    return PolyCap(omega, halfplanes(hps))


# The cap with rotation angle 1.2 used in both chapters, and its parallelogram P_ω.
W12 = 1.2
CAP12 = dict(omega=W12, a=1.6, b=1.35, rho=0.6)


def para(omega):
    """The vertices of P_ω = H ∩ V_ω: O, (sec ω, 0), o_ω, (-tan ω, 1)."""
    return [np.zeros(2), np.array((1 / math.cos(omega), 0.0)),
            np.array((math.tan(PI / 4 - omega / 2), 1.0)), np.array((-math.tan(omega), 1.0))]


# ---- Gerver's sofa ----------------------------------------------------------------------------

def gerver_parts(m=900, n=6000):
    """xs over [x(π/2)_1 - 1, 1], the roof of the niche, and the top of the cap K_G over xs."""
    lo = gerver.path(PI / 2)[0] - 1
    xs = np.linspace(lo, 1.0, m + 1)
    top, _, _ = gerver.bounds(xs, n)
    top = np.maximum(top, 0.0)
    r = roof(lambda t: np.array(gerver.path(t)), PI / 2, xs, 3000)
    return xs, r, top


def gerver_outline(m=900, n=6000):
    """Gerver's sofa as a polygon, from the slices max(roof, 0) <= y <= top."""
    xs, r, top = gerver_parts(m, n)
    pts = list(zip(xs, np.minimum(np.maximum(r, 0), top))) + list(zip(xs[::-1], top[::-1]))
    return np.array(pts)


def check_gerver_supporting(pts):
    """The outer walls of x(t) + R_t L touch Gerver's sofa: h_G(t) = <x(t), u_t> + 1 and
    h_G(t + π/2) = <x(t), v_t> + 1 (up to the resolution of the polygon)."""
    for t in np.linspace(0, PI / 2, 25):
        x = np.array(gerver.path(t))
        assert abs(np.max(pts @ u(t)) - (x @ u(t) + 1)) < 4e-3, t
        assert abs(np.max(pts @ v(t)) - (x @ v(t) + 1)) < 4e-3, t


# ---- Chapter 2 --------------------------------------------------------------------------------

def fig_frame():
    """u_t, v_t, the line l(t, h) and the half-plane H₋(t, h)."""
    win = (-1.5, 3.3, -1.25, 2.75)
    f = Figure(*win, 105)
    t, h = 0.62, 1.75
    foot = h * u(t)
    # H₋(t, h): the side of l(t, h) that contains the origin.
    f.polygon(Ps(clip(box(*win), u(t), h)), fill=LBLUE, stroke='none', width=0, opacity=0.7)
    f.line((win[0], 0), (win[1], 0), stroke=FAINT, width=1)
    f.line((0, win[2]), (0, win[3]), stroke=FAINT, width=1)
    f.circle((0, 0), 1.0, stroke=FAINT, width=1, dash='4 3')
    draw_line(f, foot, v(t), win, stroke=BLUE, width=2.2)
    # The perpendicular from O to the line, of length h, with a right-angle mark at its foot.
    f.line((0, 0), P(foot), stroke=INK, width=1.1, dash='5 4')
    k = 0.16
    f.polyline(Ps([foot - k * u(t), foot - k * u(t) + k * v(t), foot + k * v(t)]), stroke=INK,
               width=1)
    f.line((0, 0), P(u(t)), stroke=INK, width=1.8, arrow=True)
    f.line((0, 0), P(v(t)), stroke=INK, width=1.8, arrow=True)
    f.polyline(Ps(arc(np.zeros(2), 0.42, 0, t)), stroke=INK, width=1)
    text(f, 0.56 * u(t / 2), 't', size=15, dy=-0.02)
    text(f, u(t), sb('u', 't'), size=16, dx=0.06, dy=-0.12)
    text(f, v(t), sb('v', 't'), size=16, dx=-0.36, dy=0.06)
    text(f, (0, 0), 'O', size=15, dx=-0.24, dy=-0.17)
    text(f, 0.78 * foot + 0.2 * v(t), 'h', size=16)
    text(f, foot + 1.85 * v(t), 'l(t, h)', size=16, color=BLUE, dx=0.12)
    text(f, (-1.2, -0.75), 'H₋(t, h)', size=16, color=BLUE)
    text(f, (2.1, 2.3), 'H₊(t, h)', size=16, color=INK)
    assert abs(foot @ u(t) - h) < 1e-12 and abs(np.zeros(2) @ u(t)) < h
    return f.save(f'{CH2}/frame', 'The unit vectors u_t and v_t at the origin O, at the angle t from '
                  'the x-axis, and the line l(t, h) perpendicular to u_t at the distance h from O; the '
                  'half-plane H minus of t, h, on the side of the line that contains O, is shaded')


def gerver_sofa():
    pts = gerver_outline()
    check_gerver_supporting(pts)
    for t in np.linspace(0, PI / 2, 9):
        for x, y in gerver.place(t, pts[::5]):
            assert x <= 1 + 2e-3 and y <= 1 + 2e-3 and (x >= -2e-3 or y >= -2e-3), (t, x, y)
    return pts


def fig_hallway(G):
    """The hallway L = H_L ∪ V_L and Gerver's sofa at three moments of its movement."""
    xmin, ymin = -3.45, -2.5
    win = (xmin, 1.45, ymin, 1.45)
    f = Figure(*win, 112)
    hallway(f, xmin, ymin)
    start, mid, end = (gerver.place(t, G) for t in (0, PI / 4, PI / 2))
    for q in (start, end):
        f.polygon(Ps(q), fill=LBLUE, stroke=BLUE, width=1.2, opacity=0.45, stroke_opacity=0.75,
                  dash='6 4')
    f.polygon(Ps(mid), fill=LBLUE, stroke=BLUE, width=2.0, opacity=0.95)
    f.dot((0, 0), r=3.2)
    f.dot((1, 1), r=3.2)
    text(f, (0, 0), '(0, 0)', size=13, dx=-0.62, dy=-0.17, italic=False)
    text(f, (1, 1), '(1, 1)', size=13, dx=0.06, dy=0.16, italic=False)
    text(f, (-3.25, 0.5), sb('H', 'L'), size=17, color=WALL)
    text(f, (0.32, -2.2), sb('V', 'L'), size=17, color=WALL)
    text(f, (-2.05, 0.25), sb('Φ', '0', '(S)'), size=15, color=BLUE)
    text(f, (0.12, -1.85), sb('Φ', '1', '(S)'), size=15, color=BLUE)
    text(f, (0.42, -0.62), sb('Φ', '1/2', '(S)'), size=15, color=BLUE)
    # The start lies in H_L and the end in V_L (Definition 1.1.2).
    assert all(x <= 1 + 2e-3 and -2e-3 <= y <= 1 + 2e-3 for x, y in start)
    assert all(-2e-3 <= x <= 1 + 2e-3 and y <= 1 + 2e-3 for x, y in end)
    return f.save(f'{CH2}/hallway', "The hallway L, the union of its horizontal side H_L and its "
                  "vertical side V_L, with inner corner (0, 0) and outer corner (1, 1); Gerver's sofa "
                  "is drawn solid halfway through its movement, and dashed at the start, in H_L, and "
                  "at the end, in V_L, turned clockwise by a right angle")


class Rounded:
    """A rounded triangle K = T + B(0, r): a convex body with three edges and three arcs."""

    def __init__(self, T, r):
        self.T, self.r = [np.array(p, float) for p in T], r

    def h(self, t):
        return max(p @ u(t) for p in self.T) + self.r

    def point(self, t):
        """The point of K with outer normal u_t on an arc (the vertex v_K⁺(t) = v_K⁻(t) there)."""
        return max(self.T, key=lambda p: p @ u(t)) + self.r * u(t)

    def outline(self, n=720):
        return [self.point(s) for s in np.linspace(0, 2 * PI, n, endpoint=False)]


def edge_body():
    """The convex body of Figures 2.3–2.4 and the normal angle t of its edge."""
    t = 0.7
    T2 = np.array((2.65, 0.6))
    T3 = T2 + 1.5 * v(t)
    return Rounded([(1.2, 0.55), T2, T3], 0.45), t


def vint(h, a, b):
    """v_K(a, b) = l_K(a) ∩ l_K(b), by the formula of the Lean definition `vint`."""
    return h(a) * u(a) + (h(b) - h(a) * math.cos(b - a)) / math.sin(b - a) * v(a)


def fig_convex_body():
    K, t = edge_body()
    win = (-0.55, 3.9, -0.5, 3.2)
    f = Figure(*win, 112)
    h = K.h(t)
    foot = h * u(t)
    T2, T3 = K.T[1], K.T[2]
    vm, vp = T2 + K.r * u(t), T3 + K.r * u(t)
    f.polygon(Ps(clip(box(*win), u(t), h)), fill=GREY, stroke='none', width=0, opacity=0.55)
    f.line((win[0], 0), (win[1], 0), stroke=FAINT, width=1)
    f.line((0, win[2]), (0, win[3]), stroke=FAINT, width=1)
    f.polygon(Ps(K.outline()), fill=LBLUE, stroke=BLUE, width=1.8)
    draw_line(f, foot, v(t), win, stroke=INK, width=1.4)
    f.line((0, 0), P(foot), stroke=INK, width=1.1, dash='5 4')
    k = 0.13
    f.polyline(Ps([foot - k * u(t), foot - k * u(t) - k * v(t), foot - k * v(t)]), stroke=INK,
               width=1)
    f.line(P(vm), P(vp), stroke=ORANGE, width=4)
    f.dot(P(vm), r=4, fill=ORANGE)
    f.dot(P(vp), r=4, fill=ORANGE)
    f.line((0, 0), P(0.62 * u(t)), stroke=INK, width=1.6, arrow=True)
    f.line((0, 0), P(0.62 * v(t)), stroke=INK, width=1.6, arrow=True)
    text(f, (0, 0), 'O', size=15, dx=-0.23, dy=-0.17)
    text(f, 0.62 * u(t), sb('u', 't'), size=15, dx=0.04, dy=-0.14)
    text(f, 0.62 * v(t), sb('v', 't'), size=15, dx=0.08, dy=0.05)
    text(f, 0.62 * foot, sb('h', 'K', '(t)'), size=15, dx=-0.62, dy=0.1)
    text(f, (1.5, 0.85), 'K', size=18, color=BLUE)
    text(f, vp, subsup('v', 'K', '⁺', '(t)'), size=15, color=ORANGE, dx=-0.15, dy=0.24)
    text(f, vm, subsup('v', 'K', '⁻', '(t)'), size=15, color=ORANGE, dx=0.12, dy=0.05)
    mid = (vm + vp) / 2
    text(f, mid, sb('e', 'K', '(t)'), size=15, color=ORANGE, dx=0.2, dy=0.18)
    lp = foot + 1.75 * v(t)
    text(f, lp, sb('l', 'K', '(t)'), size=15, dx=0.1, dy=0.08)
    text(f, (-0.4, 2.65), sb('H', 'K', '(t)'), size=15)
    # v_K⁺(t) is the end of the edge farthest in the direction v_t; both ends lie on l_K(t).
    assert vp @ v(t) > vm @ v(t)
    assert abs(vp @ u(t) - h) < 1e-12 and abs(vm @ u(t) - h) < 1e-12
    return f.save(f'{CH2}/convex-body', 'A convex body K, the origin O with the unit vectors u_t and '
                  'v_t, and the supporting line l_K(t) at the distance h_K(t) from O; the supporting '
                  'half-plane H_K(t) is shaded, and the edge e_K(t), where the line meets K, is a '
                  'segment with the vertices v_K minus of t and v_K plus of t at its ends')


def fig_limits():
    """Theorem 2.1.3: as s decreases to t, v_K^±(s) and v_K(t, s) tend to v_K⁺(t)."""
    K, t = edge_body()
    T3 = K.T[2]
    vp = T3 + K.r * u(t)
    # A window about v_K⁺(t), in the frame of the figure (u_t, v_t turned to make l_K(t) slant).
    c0 = vp + 0.06 * u(t) - 0.12 * v(t)
    win = (c0[0] - 0.7, c0[0] + 0.7, c0[1] - 0.55, c0[1] + 0.55)
    f = Figure(*win, 330)
    body = K.outline(2880)
    f.polygon(Ps(clip_box(body, win)), fill=LBLUE, stroke='none', width=0)
    draw_polyline_clipped(f, body + body[:1], win, stroke=BLUE, width=1.8)
    draw_line(f, K.h(t) * u(t), v(t), win, stroke=INK, width=1.6)
    s_edge = seg_in_box(T3 - 2 * v(t) + K.r * u(t), vp, win)
    f.line(P(s_edge[0]), P(s_edge[1]), stroke=ORANGE, width=4.5)
    deltas = (0.85, 0.45, 0.2)
    prev = None
    for i, d in enumerate(deltas):
        s = t + d
        draw_line(f, K.h(s) * u(s), v(s), win, stroke=FAINT, width=1.2, dash='5 3')
        q = vint(K.h, t, s)
        c = K.point(s)
        f.dot(P(c), r=3.8, fill=BLUE)
        f.circle(P(q), 0.012, stroke=ORANGE, width=1.8, fill='white')
        # v_K(t, s) lies on l_K(t) and on l_K(s), beyond v_K⁺(t) in the direction v_t; both
        # it and the vertex v_K⁺(s) = v_K⁻(s) approach v_K⁺(t) as s decreases to t.
        assert abs(q @ u(t) - K.h(t)) < 1e-9 and abs(q @ u(s) - K.h(s)) < 1e-9
        assert q @ v(t) > vp @ v(t)
        dist = np.linalg.norm(q - vp) + np.linalg.norm(c - vp)
        assert prev is None or dist < prev
        prev = dist
        if i == 0:
            # Label the line l_K(s) where it leaves the window on the left.
            xl = win[0] + 0.1
            lam = (xl - K.h(s) * u(s)[0]) / v(s)[0]
            text(f, K.h(s) * u(s) + lam * v(s), sb('l', 'K', '(s)'), size=15, color=FAINT,
                 dy=0.13)
    f.dot(P(vp), r=4.6, fill=INK)
    text(f, vp, subsup('v', 'K', '⁺', '(t)'), size=16, dx=0.05, dy=-0.07)
    text(f, vp - 0.38 * v(t), sb('e', 'K', '(t)'), size=16, color=ORANGE, dx=0.08, dy=0.03)
    p_l = K.h(t) * u(t) + (vp @ v(t) + 0.48) * v(t)
    text(f, p_l, sb('l', 'K', '(t)'), size=16, dx=0.05, dy=0.03)
    text(f, vp - 0.2 * u(t) - 0.15 * v(t), 'K', size=18, color=BLUE)
    return f.save(f'{CH2}/vertex-limits', 'A close-up of the convex body of Figure 2.3 at the vertex '
                  'v_K plus of t, the upper end of the edge e_K(t) on the supporting line l_K(t); for '
                  'three angles s decreasing to t, the supporting lines l_K(s) (dashed) touch K at '
                  'single points (dots) and cross l_K(t) at the points v_K(t, s) (circles), and both '
                  'approach v_K plus of t')


def cap12():
    K = rounded_cap(**CAP12)
    assert K.niche_contained()
    return K


def check_movement(K, S_pts):
    """The motion Φ_s(p) = R_{-sω}(p - x_K(sω)) keeps the sofa S = K minus its niche inside L,
    starts in H_L and ends in V_L (Theorem 2.5.9)."""
    w = K.omega
    for s in np.linspace(0, 1, 13):
        x = K.corner(s * w)
        for p in S_pts:
            q = rot(-s * w, p - x)
            assert q[0] <= 1 + 1e-6 and q[1] <= 1 + 1e-6 and (q[0] >= -1e-6 or q[1] >= -1e-6)
            if s == 0:
                assert -1e-6 <= q[1] <= 1 + 1e-6
            if s == 1:
                assert -1e-6 <= q[0] <= 1 + 1e-6


def sofa12(K):
    xs, floor, r, top = K.parts()
    S = region(xs, np.maximum(floor, r), top)
    N = region(xs, floor, r)
    assert np.all(r[r > floor + 1e-9] <= top[r > floor + 1e-9] + 1e-9)
    return S, N


def fig_standard(K, S):
    w = K.omega
    win = (-3.15, 3.25, -0.95, 1.95)
    f = Figure(*win, 100)
    Hs = clip(clip(box(*win), u(PI / 2), 1.0), -u(PI / 2), 0.0)
    Vs = clip(clip(box(*win), u(w), 1.0), -u(w), 0.0)
    f.polygon(Ps(Hs), fill=GREY, stroke='none', width=0, opacity=0.6)
    f.polygon(Ps(Vs), fill=LGREEN, stroke='none', width=0, opacity=0.6)
    Pw = para(w)
    f.polygon(Ps(Pw), fill='none', stroke=INK, width=1.6)
    for n, c, col in ((u(PI / 2), 0.0, FAINT), (u(PI / 2), 1.0, FAINT), (u(w), 0.0, GREEN),
                      (u(w), 1.0, GREEN)):
        draw_line(f, c * n, rot(PI / 2, n), win, stroke=col, width=1, dash='4 3')
    f.polygon(Ps(S), fill=LBLUE, stroke=BLUE, width=1.8)
    O, o = Pw[0], Pw[2]
    f.dot(P(O), r=3.4)
    f.dot(P(o), r=3.4)
    text(f, O, 'O', size=15, dx=0.02, dy=-0.17)
    text(f, o, sb('o', 'ω'), size=15, dx=0.06, dy=0.16)
    text(f, (-3.05, 0.5), 'H', size=17)
    text(f, (-0.55, -0.72), sb('V', 'ω'), size=17, color=GREEN)
    text(f, (1.95, 0.12), sb('P', 'ω'), size=17)
    text(f, (-0.6, 0.55), 'S', size=18, color=BLUE)
    text(f, (2.35, 1.12), 'y = 1', size=13, italic=False, color=FAINT)
    text(f, (-1.2, 1.78), 'x cos ω + y sin ω = 1', size=13, italic=False, color=GREEN)
    # Standard position: the two upper sides support S from above.
    S_arr = np.array(S)
    assert abs(S_arr[:, 1].max() - 1) < 1e-9 and abs((S_arr @ u(w)).max() - 1) < 1e-9
    assert all(in_convex(np.array(Pw), p) for p in S_arr)
    assert abs(o[0] - (1 - math.sin(w)) / math.cos(w)) < 1e-12
    return f.save(f'{CH2}/standard-position', 'A moving sofa S with rotation angle ω = 1.2 in '
                  'standard position: the horizontal strip H and the rotated strip V_ω are shaded, '
                  'they cross in the parallelogram P_ω with lower left vertex O and upper right vertex '
                  'o_ω, and the upper sides y = 1 and x cos ω + y sin ω = 1 of the two strips touch '
                  'S from above')


def fig_sofa_frame(K, S):
    """Proposition 1.2.2: in the frame of S, the hallways that contain S at the angles 0, ω/2, ω."""
    w = K.omega
    lw = (-1.85, 2.05, -1.45, 2.05)       # the window of one panel, in the frame of S
    gap = 0.25
    width = lw[1] - lw[0] + gap
    win = (lw[0], lw[0] + 3 * width - gap, lw[2] - 0.32, lw[3])
    f = Figure(*win, 68)
    S = np.array(S)
    for i, (t, lab) in enumerate(((0.0, 't = 0'), (w / 2, 't = ω/2'), (w, 't = ω'))):
        off = np.array((i * width, 0.0))
        pw = (lw[0] + off[0], lw[1] + off[0], lw[2], lw[3])
        f.polygon(Ps(box(*pw)), fill='none', stroke=GREY, width=1)
        x = K.corner(t) + off
        draw_hallway(f, x, t, pw, floor=FLOOR, wall=None)
        if i == 0:
            Hs = clip(clip(box(*pw), u(PI / 2), 1.0), -u(PI / 2), 0.0)
            f.polygon(Ps(Hs), fill='none', stroke=FAINT, width=1, dash='3 3')
        if i == 2:
            Vs = clip(clip(box(*pw), u(w), 1.0 + off @ u(w)), -u(w), -(off @ u(w)))
            f.polygon(Ps(Vs), fill='none', stroke=GREEN, width=1, dash='3 3')
        f.polygon(Ps(S + off), fill=LBLUE, stroke=BLUE, width=1.6)
        draw_hallway(f, x, t, pw, floor=None, wall=WALL, width=2.0)
        text(f, (lw[0] + off[0] + 1.45, lw[2] - 0.2), lab, size=14, italic=True)
        text(f, (-0.75 + off[0], 0.55), 'S', size=16, color=BLUE)
        # In the frame of S the hallway turned by t contains S (Proposition 1.2.2 (2)).
        for p in S[::5]:
            q = rot(-t, p - K.corner(t))
            assert q[0] <= 1 + 1e-6 and q[1] <= 1 + 1e-6 and (q[0] >= -1e-6 or q[1] >= -1e-6)
    # (1) and (3): S lies in H and in V_ω.
    assert np.all(S[:, 1] >= -1e-9) and np.all(S[:, 1] <= 1 + 1e-9)
    assert np.all(S @ u(w) >= -1e-9) and np.all(S @ u(w) <= 1 + 1e-9)
    return f.save(f'{CH2}/sofa-frame', 'Three panels with the moving sofa S of Figure 2.5 fixed in '
                  'its own frame of reference, each with a hallway that contains it: turned by 0, '
                  'where the strip H (dashed) holds S; turned by ω/2; and turned by ω, where the strip '
                  'V_ω (dashed) holds S')


def fig_supporting(G):
    """The parts of L, and the supporting hallway L_G(t) of Gerver's sofa with the same parts."""
    win = (-1.55, 7.25, -1.35, 2.3)
    f = Figure(*win, 92)
    # Left: the hallway L and its parts.
    lw = (-1.55, 1.75, -1.35, 2.3)
    f.polygon(Ps(clip_box(L_FLOOR, lw)), fill=FLOOR, stroke='none', width=0)
    f.polygon(Ps(clip_box(box(-BIG, 0, -BIG, 0), lw)), fill=LORANGE, stroke='none', width=0)
    f.line((1, lw[2]), (1, lw[3]), stroke=WALL, width=1, dash='4 3')
    f.line((lw[0], 1), (lw[1], 1), stroke=WALL, width=1, dash='4 3')
    f.line((0, 0), (0, lw[3]), stroke=WALL, width=1, dash='4 3')
    f.line((0, 0), (lw[1], 0), stroke=WALL, width=1, dash='4 3')
    f.polyline([(lw[0], 1), (1, 1), (1, lw[2])], stroke=WALL, width=2.6)
    f.polyline([(lw[0], 0), (0, 0), (0, lw[2])], stroke=WALL, width=2.6)
    f.dot((0, 0), r=3.4, fill=ORANGE)
    f.dot((1, 1), r=3.4)
    text(f, (0, 0), sb('x', 'L'), size=15, color=ORANGE, dx=0.1, dy=0.17)
    text(f, (1, 1), sb('y', 'L'), size=15, dx=0.08, dy=0.17)
    text(f, (1, -1.0), sb('a', 'L'), size=15, dx=0.08)
    text(f, (-1.2, 1), sb('c', 'L'), size=15, dy=0.17)
    text(f, (0, -1.0), sb('b', 'L'), size=15, dx=0.08)
    text(f, (-1.2, 0), sb('d', 'L'), size=15, dy=0.17)
    text(f, (-1.15, 0.45), 'L', size=17, color=WALL)
    text(f, (-1.0, -0.6), sb('Q', 'L', '⁻'), size=15, color=ORANGE)
    # Right: Gerver's sofa and its supporting hallway at the angle t.
    t = 0.5
    dx = 4.6
    off = np.array((dx, 0.35))
    rw = (1.95, 7.25, -1.35, 2.3)
    x = np.array(gerver.path(t)) + off
    y = x + u(t) + v(t)
    draw_hallway(f, x, t, rw, floor=FLOOR, wall=None)
    Qm = clip_box([x, x - BIG * u(t), x - BIG * u(t) - BIG * v(t), x - BIG * v(t)], rw)
    f.polygon(Ps(Qm), fill=LORANGE, stroke='none', width=0)
    f.polygon(Ps(np.array(G) + off), fill=LBLUE, stroke=BLUE, width=1.6)
    for d in (u(t), v(t)):
        draw_line(f, x, d, rw, stroke=WALL, width=1, dash='4 3')
    draw_hallway(f, x, t, rw, floor=None, wall=WALL, width=2.6)
    f.dot(P(x), r=3.4, fill=ORANGE)
    f.dot(P(y), r=3.4)
    text(f, x, sb('x', '', '(t)'), size=15, color=ORANGE, dx=-0.62, dy=-0.12)
    text(f, y, sb('y', '', '(t)'), size=15, dx=0.08, dy=0.12)
    text(f, x - 0.95 * u(t) - 0.95 * v(t), sb('Q', '', '⁻(t)'), size=15, color=ORANGE)
    text(f, y - 1.5 * v(t), 'a(t)', size=15, dx=0.12)
    text(f, y - 2.35 * u(t), 'c(t)', size=15, dy=0.2)
    text(f, x - 1.25 * v(t), 'b(t)', size=15, dx=0.12, dy=-0.05)
    text(f, x - 1.9 * u(t), 'd(t)', size=15, dx=-0.05, dy=-0.2)
    text(f, (2.35, 0.95), 'G', size=17, color=BLUE)
    Garr = np.array(G)
    assert abs(np.max(Garr @ u(t)) - (np.array(gerver.path(t)) @ u(t) + 1)) < 4e-3
    assert abs(np.max(Garr @ v(t)) - (np.array(gerver.path(t)) @ v(t) + 1)) < 4e-3
    return f.save(f'{CH2}/supporting-hallway', "Left: the hallway L with its inner corner x_L = "
                  "(0, 0), its outer corner y_L = (1, 1), its outer walls a_L and c_L, and its inner "
                  "walls b_L and d_L, whose lines are drawn dashed beyond the hallway; the open "
                  "quarter-plane Q_L minus is shaded. Right: Gerver's sofa G and its supporting "
                  "hallway at the angle t = 0.5, with the corresponding corners x(t) and y(t), walls "
                  "a(t), b(t), c(t), d(t) and quarter-plane Q minus of t; the outer walls touch G")


def disk_sofa():
    """The disk of diameter 1 centred at (0, 1/2), a moving sofa for every rotation angle."""
    c = np.array((0.0, 0.5))
    pts = [c + 0.5 * u(s) for s in np.linspace(0, 2 * PI, 400, endpoint=False)]
    h = lambda t: float(c @ u(t)) + 0.5
    return c, np.array(pts), h


def fig_push():
    """Proposition 2.2.3: pushing a hallway that contains S onto the supporting hallway L_S(t)."""
    r = 0.32
    c = np.array((0.0, r))
    D = np.array([c + r * u(s) for s in np.linspace(0, 2 * PI, 300, endpoint=False)])
    h = lambda t: float(c @ u(t)) + r
    t = 0.45
    xS = (h(t) - 1) * u(t) + (h(t + PI / 2) - 1) * v(t)
    xp = xS + 0.24 * u(t) + 0.18 * v(t)
    win = (-1.7, 1.95, -1.25, 1.42)
    f = Figure(*win, 120)
    draw_hallway(f, xS, t, win, floor=FLOOR, wall=None)
    f.polygon(Ps(D), fill=LBLUE, stroke=BLUE, width=1.8)
    draw_hallway(f, xp, t, win, floor=None, wall=FAINT, width=1.8, dash='6 4')
    draw_hallway(f, xS, t, win, floor=None, wall=WALL, width=2.4)
    yS, yp = xS + u(t) + v(t), xp + u(t) + v(t)
    f.line(P(yp), P(yS + 0.06 * (yp - yS) / np.linalg.norm(yp - yS)), stroke=INK, width=1.3,
           arrow=True)
    f.line(P(xp), P(xS + 0.06 * (xp - xS) / np.linalg.norm(xp - xS)), stroke=INK, width=1.3,
           arrow=True)
    text(f, yS, sb('L', 'S', '(t)'), size=15, dx=-0.85, dy=0.22)
    text(f, yp, "L'", size=15, color=FAINT, dx=0.08, dy=0.12)
    text(f, (-0.12, 0.42), 'S', size=17, color=BLUE)
    # S lies in both hallways; the supporting one touches S with both outer walls.
    for hw in (xS, xp):
        for p in D:
            q = rot(-t, p - hw)
            assert q[0] <= 1 + 1e-9 and q[1] <= 1 + 1e-9 and (q[0] >= -1e-9 or q[1] >= -1e-9)
    assert abs(max(rot(-t, p - xS)[0] for p in D) - 1) < 1e-4
    assert abs(max(rot(-t, p - xS)[1] for p in D) - 1) < 1e-4
    return f.save(f'{CH2}/push', "A disk S inside a hallway L' turned by the angle t (dashed walls), "
                  "and the supporting hallway L_S(t) (solid walls), obtained by pushing L' along "
                  "-u_t and -v_t until both outer walls touch S; the push moves the inner walls away "
                  "from S")


def main_ch2(G, K, S):
    return [fig_frame(), fig_hallway(G), fig_convex_body(), fig_limits(), fig_standard(K, S),
            fig_sofa_frame(K, S), fig_supporting(G), fig_push()]


# ---- Chapter 3 --------------------------------------------------------------------------------

def draw_segments(f, ps, win, **kw):
    """A polyline clipped to the window, segment by segment."""
    for a, b in zip(ps, ps[1:]):
        s = seg_in_box(np.asarray(a, float), np.asarray(b, float), win)
        if s is not None:
            f.polyline([P(s[0]), P(s[1])], **kw)


def fig_monotonization():
    """The monotonization of the disk of diameter 1 is a tombstone (Theorems 2.3.2 and 2.3.6)."""
    c, D, h = disk_sofa()
    w = PI / 2
    # The cap C(S) = P_ω ∩ ⋂ Q⁺_S(t): for ω = π/2, the strip H cut by the half-planes of S with
    # normal angles in [0, π].
    hps = [(u(PI / 2), 1.0), (-u(PI / 2), 0.0)] + [(u(s), h(s)) for s in np.linspace(0, PI, 1441)]
    K = PolyCap(w, halfplanes(hps))
    assert abs(area(K.poly) - (0.5 + PI / 8)) < 1e-4
    # Every inner corner x_S(t) = c - (u_t + v_t)/2 lies on or below the floor y = 0, so every open
    # quadrant Q⁻_S(t) lies below it: the niche is empty and I(S) = C(S).
    ts = np.linspace(0, w, 181)
    corners = [K.corner(t) for t in ts]
    for t, x in zip(ts, corners):
        assert np.allclose(x, c - (u(t) + v(t)) / 2, atol=1e-6) and x[1] <= 1e-9
    xs, floor, r, top = K.parts()
    assert np.all(r <= floor + 1e-9)
    win = (-1.25, 1.25, -0.5, 1.4)
    f = Figure(*win, 150)
    for y in (0.0, 1.0):
        f.line((win[0], y), (win[1], y), stroke=FAINT, width=1, dash='4 3')
    for t in (PI / 8, PI / 4, 3 * PI / 8):
        y = K.outer(t)
        draw_line(f, y, v(t), win, stroke=GREY, width=1.2)
        draw_line(f, y, u(t), win, stroke=GREY, width=1.2)
    f.polygon(Ps(K.poly), fill=LBLUE, stroke=BLUE, width=1.8)
    f.polygon(Ps(D), fill='#bfdbfe', stroke=BLUE, width=1.4)
    f.polyline(Ps(corners), stroke=ORANGE, width=1.8, dash='5 3')
    p = np.array((0.44, 0.03))
    q = np.array((0.44, 0.5 - math.sqrt(0.25 - 0.44 ** 2)))
    f.line(P(p), P(q), stroke=INK, width=1.8)
    f.dot(P(p), r=3.4)
    f.dot(P(q), r=3.4)
    text(f, p, 'p', size=15, dx=0.06, dy=-0.02)
    text(f, q, 'q', size=15, dx=0.06, dy=0.04)
    text(f, (-0.08, 0.55), 'S', size=17, color=BLUE)
    f.line((-0.86, 0.2), (-0.44, 0.06), stroke=BLUE, width=1)
    text(f, (-1.18, 0.24), 'I(S)', size=16, color=BLUE)
    text(f, (-0.12, -0.32), 'x(t)', size=15, color=ORANGE)
    text(f, (1.02, 1.08), 'y = 1', size=12, italic=False, color=FAINT)
    text(f, (1.02, 0.08), 'y = 0', size=12, italic=False, color=FAINT)
    assert not (np.linalg.norm(p - c) <= 0.5) and in_convex(K.poly, p)
    assert abs(np.linalg.norm(q - c) - 0.5) < 1e-12 and in_convex(K.poly, (p + q) / 2)
    return f.save(f'{CH3}/monotonization', 'The disk S of diameter 1 between the lines y = 0 and '
                  'y = 1, inside its monotonization I(S), the disk with the square below its upper '
                  'half, bounded by the outer walls of the supporting hallways (three are drawn); '
                  'the inner corners x(t) stay below the floor, so the niche is empty; a vertical '
                  'segment inside I(S) joins a point p of I(S) to a point q of S')


def fig_intersection(G):
    """Gerver's sofa as the intersection of the strip H and its supporting hallways."""
    win = (-2.55, 1.65, -1.05, 1.8)
    f = Figure(*win, 118)
    ts = np.linspace(0, PI / 2, 7)
    for t in ts:
        draw_hallway(f, np.array(gerver.path(t)), t, win, floor=GREY, wall=None, opacity=0.22)
    f.polygon(Ps(G), fill=BLUE, stroke=BLUE, width=2.0, opacity=0.18)
    for t in ts:
        x = np.array(gerver.path(t))
        draw_segments(f, moved(x, t, L_OUTER), win, stroke=WALL, width=1.1, opacity=0.6)
        draw_segments(f, moved(x, t, L_INNER), win, stroke=WALL, width=1.1, opacity=0.6)
    for y in (0.0, 1.0):
        f.line((win[0], y), (win[1], y), stroke=INK, width=1, dash='5 3')
    text(f, (-2.45, 0.5), 'H', size=16)
    text(f, (-0.7, 0.75), 'G', size=18, color=BLUE)
    # Every point of G lies in every hallway x(t) + R_t L (G is a moving sofa) and in H.
    for t in np.linspace(0, PI / 2, 31):
        x = np.array(gerver.path(t))
        for p in G[::6]:
            q = rot(-t, p - x)
            assert q[0] <= 1 + 3e-3 and q[1] <= 1 + 3e-3 and (q[0] >= -3e-3 or q[1] >= -3e-3)
    assert np.all(G[:, 1] >= -1e-9) and np.all(G[:, 1] <= 1 + 1e-9)
    return f.save(f'{CH3}/intersection', "Gerver's sofa G between the lines y = 0 and y = 1 of the "
                  "strip H, with seven of its supporting hallways, turned by 0, 15, 30, 45, 60, 75 "
                  "and 90 degrees, shaded in translucent grey; G is the part of H that lies in all "
                  "of them, where the shading is darkest")


def gerver_regions():
    xs, r, top = gerver_parts()
    floor = np.zeros_like(xs)
    K = list(zip(xs, floor)) + list(zip(xs[::-1], top[::-1]))
    N = region(xs, floor, r)
    S = region(xs, np.maximum(floor, r), top)
    on = r > 1e-9
    assert np.all(r[on] < top[on]), "the niche of Gerver's cap lies in the cap"
    aK, aN = area(K), area(N)
    assert abs(aK - aN - 2.21953) < 2e-3, (aK, aN)
    return xs, r, top, K, N, S


def fig_cap_niche(gr):
    """Gerver's cap K, its niche N(K), and S = K \\ N(K) (Theorems 2.4.2 and 2.5.10)."""
    xs, r, top, K, N, S = gr
    lw = (-2.45, 1.4, -0.32, 1.32)
    dy = lw[3] - lw[2] + 0.12
    win = (lw[0], lw[1], lw[2] - 2 * dy, lw[3])
    f = Figure(*win, 118)
    ts = np.linspace(0, PI / 2, 9)
    # (a) The cap: below the outer walls of the supporting hallways.
    o = np.array((0.0, 0.0))
    pw = lw
    f.polygon(Ps(K), fill=LBLUE, stroke=BLUE, width=1.8)
    for t in ts:
        y = np.array(gerver.path(t)) + u(t) + v(t)
        draw_line(f, y, v(t), pw, stroke=GREY, width=1.1)
        draw_line(f, y, u(t), pw, stroke=GREY, width=1.1)
    text(f, (-0.55, 0.45), 'K', size=17, color=BLUE)
    # (b) The niche: under the open quadrants at the inner corners, cut by the fan y >= 0.
    o = np.array((0.0, -dy))
    pw = (lw[0], lw[1], lw[2] - dy, lw[3] - dy)
    f.polygon(Ps(np.array(K) + o), fill='none', stroke=BLUE, width=1.2, dash='4 3')
    f.polygon(Ps(np.array(N) + o), fill=LORANGE, stroke=ORANGE, width=1.6)
    for t in ts[1:-1]:
        x = np.array(gerver.path(t)) + o
        for d in (u(t), v(t)):
            s = seg_in_box(x, x - 3 * d, (pw[0], pw[1], o[1], pw[3]))
            if s is not None:
                f.line(P(s[0]), P(s[1]), stroke=ORANGE, width=1, dash='3 2')
        f.dot(P(x), r=2.6, fill=ORANGE)
    path = [np.array(gerver.path(t)) + o for t in np.linspace(0, PI / 2, 200)]
    f.polyline(Ps(path), stroke=ORANGE, width=1.8)
    text(f, (0.62, 0.1 - dy), 'N(K)', size=16, color=ORANGE)
    text(f, (0.05, 0.62 - dy), 'x(t)', size=15, color=ORANGE)
    # (c) The sofa S = K minus N(K), with its upper boundary and a vertical segment.
    o = np.array((0.0, -2 * dy))
    f.polygon(Ps(np.array(S) + o), fill=LBLUE, stroke=BLUE, width=1.8)
    top_pts = [(x, y - 2 * dy) for x, y in zip(xs, top)]
    f.polyline(top_pts, stroke=BLUE, width=3.6)
    xp = -0.6
    yr = float(np.interp(xp, xs, r))
    yt = float(np.interp(xp, xs, top))
    pS = np.array((xp, yr + 0.08))
    f.line(P(pS + o), P(np.array((xp, yt)) + o), stroke=INK, width=1.6)
    f.dot(P(pS + o), r=3.2)
    f.dot(P(np.array((xp, yt)) + o), r=3.2)
    text(f, (-1.75, 0.35 - 2 * dy), 'S', size=17, color=BLUE)
    text(f, (0.55, 1.12 - 2 * dy), 'δK', size=15, color=BLUE)
    for k, lab in enumerate(('(a)', '(b)', '(c)')):
        text(f, (lw[1] - 0.32, lw[3] - 0.15 - k * dy), lab, size=13, italic=False, color=FAINT)
    return f.save(f'{CH3}/cap-niche', "Three panels for Gerver's sofa. (a) Its cap K, the part of "
                  "the strip below the outer walls of the supporting hallways (nine are drawn). (b) "
                  "Its niche N(K), the part of the upper half-plane covered by the open quarter-planes "
                  "below the inner corners x(t), whose walls are dashed; the path of x(t) bounds the "
                  "niche from above in the middle. (c) The sofa S = K minus N(K), with its upper "
                  "boundary drawn thick and a vertical segment from a point of S up to it")


def fig_fan(K, S12, N12):
    """The fan F_ω, the parallelogram P_ω, a cap K and its niche, for ω = 1.2."""
    w = K.omega
    win = (-2.95, 3.05, -0.55, 2.0)
    f = Figure(*win, 100)
    F = clip(clip(box(*win), -u(w), 0.0), -u(PI / 2), 0.0)
    f.polygon(Ps(F), fill=LGREEN, stroke='none', width=0, opacity=0.8)
    draw_ray(f, np.zeros(2), u(0), win, stroke=GREEN, width=1.8)
    draw_ray(f, np.zeros(2), v(w), win, stroke=GREEN, width=1.8)
    f.polygon(Ps(para(w)), fill='none', stroke=INK, width=1.2, dash='5 3')
    f.polygon(Ps(K.poly), fill=LBLUE, stroke=BLUE, width=1.8)
    f.polygon(Ps(N12), fill=LORANGE, stroke=ORANGE, width=1.6)
    ts = (0.3, 0.6, 0.9)
    for t in ts:
        x = K.corner(t)
        for d in (u(t), v(t)):
            draw_ray(f, x, -d, win, stroke=ORANGE, width=1, dash='3 2')
        f.dot(P(x), r=2.8, fill=ORANGE)
    f.dot((0, 0), r=3.2)
    text(f, (0, 0), 'O', size=15, dx=0.04, dy=-0.2)
    text(f, (2.35, 1.75), sb('F', 'ω'), size=17, color=GREEN)
    text(f, (2.0, 0.75), sb('P', 'ω'), size=16)
    text(f, (-1.05, 0.62), 'K', size=17, color=BLUE)
    text(f, (0.74, 0.1), 'N(K)', size=14, color=ORANGE)
    # The niche lies in the fan, below the inner corners, and inside K (Theorem 2.5.8 (3)).
    N = np.array(N12)
    assert np.all(N[:, 1] >= -1e-9) and np.all(N @ u(w) >= -1e-9)
    assert K.niche_contained()
    return f.save(f'{CH3}/fan', 'The fan F_omega, the wedge-shaped region above the x-axis and to the '
                  'right of the line through O in the direction v_omega, shaded green, for omega = '
                  '1.2; inside it the parallelogram P_omega (dashed), a cap K and its niche N(K), the '
                  'part of the fan below the open quarter-planes at the inner corners x_K(t), three '
                  'of which are drawn with their walls')


def fig_wedge(K):
    """A wedge T_K(t), its endpoints W_K(t), Z_K(t) and the gaps w_K(t), z_K(t) (Theorem 2.5.5)."""
    w, t = K.omega, 0.55
    x = K.corner(t)
    W = np.array(((K.h(t) - 1) / math.cos(t), 0.0))
    Z = (K.h(t + PI / 2) - 1) / math.cos(w - t) * v(w)
    A0 = np.array((K.h(0), 0.0))              # A_K⁻(0), on the x-axis
    Cw = K.h(w + PI / 2) * v(w)              # C_K⁺(ω), on the line l(ω, 0)
    assert in_convex(K.poly, A0) and in_convex(K.poly, Cw)
    gw, gz = (A0 - W) @ u(0), (Cw - Z) @ v(w)
    assert gw > 0 and gz > 0
    # W_K(t) lies on b_K(t) and the x-axis, Z_K(t) on d_K(t) and l(ω, 0).
    assert abs(W @ u(t) - (K.h(t) - 1)) < 1e-12 and abs(Z @ v(t) - (K.h(t + PI / 2) - 1)) < 1e-12
    assert abs(Z @ u(w)) < 1e-12
    # O lies strictly below both inner walls, so the wedge is the quadrilateral O, W, x, Z.
    assert 0 < K.h(t) - 1 and 0 < K.h(t + PI / 2) - 1
    BQ = 30.0
    Q = [x, x - BQ * v(t), x - BQ * v(t) - BQ * u(t), x - BQ * u(t)]
    T = clip(clip(Q, -u(w), 0.0), -u(PI / 2), 0.0)
    T = np.array(T)
    assert len(T) == 4
    for corner in (np.zeros(2), W, x, Z):
        assert min(np.linalg.norm(T - corner, axis=1)) < 1e-9
    # x_K(t) lies in K, so the whole wedge does (Lemma 2.5.6).
    assert in_convex(K.poly, x) and all(in_convex(K.poly, p) for p in T)
    win = (-1.85, 2.0, -0.42, 1.38)
    f = Figure(*win, 150)
    F = clip(clip(box(*win), -u(w), 0.0), -u(PI / 2), 0.0)
    f.polygon(Ps(F), fill=LGREEN, stroke='none', width=0, opacity=0.6)
    f.polygon(Ps(K.poly), fill=LBLUE, stroke=BLUE, width=1.6)
    f.polygon(Ps(T), fill=LORANGE, stroke='none', width=0)
    draw_line(f, x, v(t), win, stroke=ORANGE, width=1, dash='4 3')
    draw_line(f, x, u(t), win, stroke=ORANGE, width=1, dash='4 3')
    f.line(P(x), P(W), stroke=ORANGE, width=2)
    f.line(P(x), P(Z), stroke=ORANGE, width=2)
    draw_ray(f, np.zeros(2), u(0), win, stroke=GREEN, width=1.6)
    draw_ray(f, np.zeros(2), v(w), win, stroke=GREEN, width=1.6)
    # The gaps, drawn as thick segments along the two lower sides.
    f.line(P(W), P(A0), stroke=PURPLE, width=4.5)
    f.line(P(Z), P(Cw), stroke=PURPLE, width=4.5)
    for p_ in (np.zeros(2), W, Z, x, A0, Cw):
        f.dot(P(p_), r=3.4, fill=INK)
    text(f, (0, 0), 'O', size=14, dx=0.02, dy=-0.19)
    text(f, W, sb('W', 'K', '(t)'), size=14, dx=-0.32, dy=-0.2)
    text(f, A0, subsup('A', 'K', '⁻', '(0)'), size=14, dx=-0.2, dy=-0.2)
    text(f, Z, sb('Z', 'K', '(t)'), size=14, dx=0.1, dy=0.02)
    text(f, Cw, subsup('C', 'K', '⁺', '(ω)'), size=14, dx=-0.12, dy=0.19)
    text(f, x, sb('x', 'K', '(t)'), size=14, dx=0.08, dy=0.1)
    text(f, (W + A0) / 2, sb('w', 'K', '(t)'), size=14, color=PURPLE, dx=-0.2, dy=0.15)
    text(f, (Z + Cw) / 2, sb('z', 'K', '(t)'), size=14, color=PURPLE, dx=-0.62, dy=-0.06)
    text(f, (0.1, 0.32), sb('T', 'K', '(t)'), size=14, color=ORANGE)
    text(f, x - 0.75 * v(t), sb('b', 'K', '(t)'), size=13, color=ORANGE, dx=0.08)
    text(f, x - 0.62 * u(t), sb('d', 'K', '(t)'), size=13, color=ORANGE, dy=0.14)
    text(f, (1.15, 0.75), 'K', size=17, color=BLUE)
    return f.save(f'{CH3}/wedge', 'For the cap K of Figure 3.3 and the angle t = 0.55: the wedge '
                  'T_K(t), the part of the fan below the inner walls b_K(t) and d_K(t), is the '
                  'quadrilateral with vertices O, W_K(t), x_K(t) and Z_K(t); the gaps w_K(t), from '
                  'W_K(t) to A_K minus of 0 along the x-axis, and z_K(t), from Z_K(t) to C_K plus of '
                  'omega along the lower left side of the fan, are drawn thick')


def mirror(w, p):
    """The reflection M_ω in the line through O and o_ω (Lean: `mirror`)."""
    return np.array((-math.sin(w) * p[0] + math.cos(w) * p[1],
                     math.cos(w) * p[0] + math.sin(w) * p[1]))


def fig_mirror(K):
    """Proposition 2.5.4: M_ω maps L_K(s) onto L_{K^m}(ω - s), exchanging the walls a and c."""
    w, s = K.omega, 0.3
    Km = PolyCap(w, np.array([mirror(w, p) for p in K.poly[::-1]]))
    o = para(w)[2]
    assert np.allclose(mirror(w, o), o) and np.allclose(mirror(w, np.zeros(2)), 0)
    for t in np.linspace(0, 2 * PI, 25):
        assert abs(Km.h(t) - K.h(w + PI / 2 - t)) < 1e-9
    # M_ω(a_K(s)) = c_{K^m}(ω - s) and M_ω(c_K(s)) = a_{K^m}(ω - s), as lines n·p = c.
    yK, yM = K.outer(s), Km.outer(w - s)
    assert np.allclose(mirror(w, yK), yM) and np.allclose(mirror(w, K.corner(s)), Km.corner(w - s))
    assert np.allclose(mirror(w, u(s)), v(w - s)) and np.allclose(mirror(w, v(s)), u(w - s))
    lw = (-2.0, 2.25, -0.75, 2.2)
    gap = 0.3
    dx = lw[1] - lw[0] + gap
    win = (lw[0], lw[1] + dx, lw[2], lw[3])
    f = Figure(*win, 92)
    for k, (C, t, lab) in enumerate(((K, s, 'K'), (Km, w - s, sp('K', 'm')))):
        off = np.array((k * dx, 0.0))
        pw = (lw[0] + off[0], lw[1] + off[0], lw[2], lw[3])
        f.polygon(Ps(box(*pw)), fill='none', stroke=GREY, width=1)
        x, y = C.corner(t) + off, C.outer(t) + off
        draw_hallway(f, x, t, pw, floor=FLOOR, wall=None)
        Pw = [p + off for p in para(w)]
        draw_segments(f, Pw + Pw[:1], pw, stroke=FAINT, width=1, dash='4 3')
        draw_line(f, off, u(PI / 4 + w / 2), pw, stroke=PURPLE, width=1.2, dash='6 3')
        f.polygon(Ps(C.poly + off), fill=LBLUE if k == 0 else LGREEN,
                  stroke=BLUE if k == 0 else GREEN, width=1.6)
        draw_hallway(f, x, t, pw, floor=None, wall=WALL, width=2.0)
        text(f, y - 1.0 * v(t), 'a', size=15, dx=0.1)
        text(f, y - 1.0 * u(t), 'c', size=15, dy=0.18)
        text(f, x - 0.75 * v(t), 'b', size=15, dx=0.1)
        text(f, x - 0.75 * u(t), 'd', size=15, dy=0.18)
        text(f, off + np.array((-0.5 if k == 0 else 1.15, 0.45)), lab, size=17,
             color=BLUE if k == 0 else GREEN)
    return f.save(f'{CH3}/mirror', 'Two panels. Left: the cap K of Figure 3.3 with its supporting '
                  'hallway at the angle s = 0.3, whose outer walls a, c and inner walls b, d are '
                  'labelled, and the mirror line through O and o_omega (dashed). Right: the reflected '
                  'cap K^m with its supporting hallway at the angle omega - s, the reflection of the '
                  'left hallway; the reflection carries the wall a on the left to the wall c on the '
                  'right, and b to d')


def fig_wide_cap():
    """Remark 2.5.2: a wide cap does not contain its niche, and K minus N(K) is disconnected."""
    d = 6.0
    K = PolyCap(PI / 2, [(0, 0), (d, 0), (d, 1), (0, 1)])
    xs, floor, r, top = K.parts(m=1200)
    x45 = K.corner(PI / 4)
    assert np.allclose(x45, (d / 2, d / 2 + 1 - math.sqrt(2)))
    assert not in_convex(K.poly, x45) and x45[1] > 0 and x45[0] > 0
    # The point (d/2, 2) lies in the wedge T_K(π/4) but not in K (the Lean statement, for d = 100,
    # uses the point (50, 2)).
    p = np.array((d / 2, 2.0))
    assert (p - x45) @ u(PI / 4) < 0 and (p - x45) @ v(PI / 4) < 0 and not in_convex(K.poly, p)
    Sparts = regions(xs, np.maximum(floor, r), top)
    assert len(Sparts) == 2
    assert max(q[0] for q in Sparts[0]) < d / 2 < min(q[0] for q in Sparts[1])
    Nlo = np.minimum(r, 2.7)
    win = (-0.45, 6.5, -0.5, 2.85)
    f = Figure(*win, 92)
    f.polygon(Ps(K.poly), fill='none', stroke=BLUE, width=1.4, dash='5 3')
    f.polygon(Ps(region(xs, floor, Nlo)), fill=LORANGE, stroke=ORANGE, width=1.4, opacity=0.85)
    for part in Sparts:
        f.polygon(Ps(part), fill=LBLUE, stroke=BLUE, width=1.8)
    Q = [x45, x45 - 9 * v(PI / 4), x45 - 9 * v(PI / 4) - 9 * u(PI / 4), x45 - 9 * u(PI / 4)]
    T = clip(Q, -u(PI / 2), 0.0)
    f.polygon(Ps(T), fill='none', stroke=ORANGE, width=2.0)
    f.line((d / 2, win[2]), (d / 2, win[3]), stroke=INK, width=1.1, dash='6 4')
    f.dot(P(x45), r=3.6, fill=ORANGE)
    f.dot((d, 0), r=3.4)
    f.dot((0, 0), r=3.4)
    text(f, x45, sb('x', 'K', '(π/4)'), size=14, color=ORANGE, dx=0.1, dy=0.12)
    text(f, (d / 2 + 0.55, 1.45), sb('T', 'K', '(π/4)'), size=14, color=ORANGE)
    text(f, (d, 0), subsup('A', 'K', '⁻', '(0)'), size=14, dx=-0.35, dy=-0.22)
    text(f, (0, 0), subsup('C', 'K', '⁺', '(ω)'), size=14, dx=-0.15, dy=-0.22)
    text(f, (0.12, 0.5), 'S', size=15, color=BLUE)
    text(f, (5.68, 0.5), 'S', size=15, color=BLUE)
    text(f, (1.2, 0.72), 'N(K)', size=14, color=ORANGE)
    return f.save(f'{CH3}/wide-cap', 'The cap K = [0, 6] by [0, 1] with rotation angle pi/2, '
                  'outlined dashed: its niche N(K), shaded orange, rises far above K, and the wedge '
                  'T_K(pi/4), outlined, has its corner x_K(pi/4) = (3, 2.59) outside K; what is left '
                  'of K, the set K minus N(K), consists of two pieces near the ends, separated by '
                  'the vertical line through x_K(pi/4)')


def main_ch3(G, K, N12, S12):
    gr = gerver_regions()
    return [fig_monotonization(), fig_intersection(G), fig_cap_niche(gr), fig_fan(K, S12, N12),
            fig_wedge(K), fig_mirror(K), fig_wide_cap()]


def main():
    G = gerver_sofa()
    K = cap12()
    S, N = sofa12(K)
    check_movement(K, S[::7])
    paths = main_ch2(G, K, S) + main_ch3(G, K, N, S)
    for p in paths:
        print(f'wrote {p}')


if __name__ == '__main__':
    main()
