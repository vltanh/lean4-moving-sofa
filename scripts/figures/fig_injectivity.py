#!/usr/bin/env python3
"""The figures of Chapter 6 (the surface area measure) and Chapter 7 (the injectivity condition), in
docs/proof/figures/06-surface-area/ and docs/proof/figures/07-injectivity/.

    python3 scripts/figures/fig_injectivity.py

Every figure is computed from the definitions it illustrates:

* the surface area measure `σ_K` is the Lebesgue–Stieltjes measure of the distribution function
  `G_K(t) = ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K` (`MovingSofaOptimality.sigmaFun`), computed here from the support
  function and the vertex of a convex body given by points of its boundary;
* Gerver's sofa, its rotation path `𝐱` and the contact points `𝐀 = 𝐱 + u_t + ⟨𝐱', u_t⟩ v_t`,
  `𝐁 = 𝐱 + ⟨𝐱', u_t⟩ v_t`, `𝐂 = 𝐱 + v_t - ⟨𝐱', v_t⟩ u_t`, `𝐃 = 𝐱 - ⟨𝐱', v_t⟩ u_t`
  (`MovingSofaOptimality.contactA`, ...) come from gerver.py, with `𝐱'` written in Romik's rotating
  frame (`MovingSofaOptimality/Gerver/Frame.lean`);
* the cap of Gerver's sofa has the support function `h(t) = ⟨𝐱(t), u_t⟩ + 1`,
  `h(t + π/2) = ⟨𝐱(t), v_t⟩ + 1` for `t ∈ [0, π/2]`; the polygon cap of §7.3 is cut out by the
  supporting lines of that support function at the angles of `Θ_4`, and its niche by the quadrants
  `Q⁻(s)`, `s ∈ Θ_4`;
* the lower bounds `f_n` are the iterates of the operator `𝓕` (`MovingSofaOptimality.lowerSeq`).

The script checks with `assert`s the facts that the captions state.
"""
import math

import numpy as np

import gerver
from sofa_figures import Figure, INK, FAINT, WALL, FLOOR, COLORS, FILLS, GREY, sb

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
PHI, THETA = gerver.PHI, gerver.THETA
CH6, CH7 = '06-surface-area', '07-injectivity'


# ------------------------------------------------------------------------------- plane geometry

def uvec(t):
    return (math.cos(t), math.sin(t))


def vvec(t):
    return (-math.sin(t), math.cos(t))


def add(*ps):
    return (sum(p[0] for p in ps), sum(p[1] for p in ps))


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def mul(c, p):
    return (c * p[0], c * p[1])


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def norm(p):
    return math.hypot(p[0], p[1])


def lerp(p, q, s):
    return (p[0] + s * (q[0] - p[0]), p[1] + s * (q[1] - p[1]))


def meet(n1, c1, n2, c2):
    """The intersection of the lines ⟨q, n1⟩ = c1 and ⟨q, n2⟩ = c2."""
    det = n1[0] * n2[1] - n1[1] * n2[0]
    return ((c1 * n2[1] - c2 * n1[1]) / det, (n1[0] * c2 - n2[0] * c1) / det)


def clip_halfplane(pts, n, c):
    """Sutherland–Hodgman: the part of the polygon pts where ⟨q, n⟩ <= c."""
    out = []
    for i, p in enumerate(pts):
        q = pts[(i + 1) % len(pts)]
        fp, fq = dot(p, n) - c, dot(q, n) - c
        if fp <= 0:
            out.append(p)
        if fp * fq < 0:
            out.append(lerp(p, q, fp / (fp - fq)))
    return out


def clip_box(pts, box):
    """The part of the polygon pts inside the box (xmin, xmax, ymin, ymax)."""
    x0, x1, y0, y1 = box
    for n, c in (((-1, 0), -x0), ((1, 0), x1), ((0, -1), -y0), ((0, 1), y1)):
        pts = clip_halfplane(pts, n, c)
        if not pts:
            break
    return pts


def clip_segment(p, q, box):
    """Liang–Barsky: the part of the segment pq inside the box, or None."""
    x0, x1, y0, y1 = box
    t0, t1 = 0.0, 1.0
    dx, dy = q[0] - p[0], q[1] - p[1]
    for a, b in ((-dx, p[0] - x0), (dx, x1 - p[0]), (-dy, p[1] - y0), (dy, y1 - p[1])):
        if a == 0:
            if b < 0:
                return None
        else:
            r = b / a
            if a < 0:
                t0 = max(t0, r)
            else:
                t1 = min(t1, r)
    if t0 > t1:
        return None
    return lerp(p, q, t0), lerp(p, q, t1)


def line_in_box(n, c, box):
    """The part of the line ⟨q, n⟩ = c inside the box."""
    p0 = mul(c / dot(n, n), n)
    d = (-n[1], n[0])
    big = 100.0
    return clip_segment(add(p0, mul(-big, d)), add(p0, mul(big, d)), box)


def polygon_area(pts):
    s = 0.0
    for i, p in enumerate(pts):
        q = pts[(i + 1) % len(pts)]
        s += p[0] * q[1] - q[0] * p[1]
    return s / 2


def simplify(pts, eps):
    """Ramer–Douglas–Peucker: drop the points within eps of the chord of their neighbours."""
    pts = list(pts)
    if len(pts) < 3:
        return pts
    keep = [False] * len(pts)
    keep[0] = keep[-1] = True
    stack = [(0, len(pts) - 1)]
    while stack:
        i, j = stack.pop()
        a, b = pts[i], pts[j]
        d = sub(b, a)
        L = norm(d)
        best, k = -1.0, None
        for m in range(i + 1, j):
            q = sub(pts[m], a)
            dist = abs(d[0] * q[1] - d[1] * q[0]) / L if L > 0 else norm(q)
            if dist > best:
                best, k = dist, m
        if k is not None and best > eps:
            keep[k] = True
            stack += [(i, k), (k, j)]
    return [q for q, kq in zip(pts, keep) if kq]


def arrow(f, a, b, color=INK, width=1.5):
    """A segment from a to b with an arrowhead at b, drawn in the colour of the segment."""
    f.line(a, b, stroke=color, width=width)
    d = sub(b, a)
    length = norm(d)
    if length == 0:
        return
    e = mul(1 / length, d)
    n = (-e[1], e[0])
    head = 9.0 / f.s
    base = add(b, mul(-head, e))
    f.polygon([b, add(base, mul(0.42 * head, n)), add(base, mul(-0.42 * head, n))],
              fill=color, stroke=color, width=0.8)


def right_angle(f, p, d1, d2, size=0.12, color=INK):
    """A right-angle mark at p between the unit directions d1 and d2."""
    a = add(p, mul(size, d1))
    b = add(p, mul(size, d1), mul(size, d2))
    c = add(p, mul(size, d2))
    f.polyline([a, b, c], stroke=color, width=1.0)


# ------------------------------------------------------- convex bodies given by boundary points

class Body:
    """A convex body given by points of its boundary (all its vertices, and dense samples of its
    curved arcs), with the support function, the vertex v⁺ and the distribution function of σ."""

    def __init__(self, pts):
        self.P = np.array(pts, dtype=float)

    def supp(self, t):
        return float(np.max(self.P @ np.array(uvec(t))))

    def vplus(self, t, tol=1e-9):
        """The point of the edge e_K(t) farthest in the direction v_t (Definition 2.1.12)."""
        hs = self.P @ np.array(uvec(t))
        edge = self.P[hs >= hs.max() - tol]
        k = int(np.argmax(edge @ np.array(vvec(t))))
        return tuple(edge[k])

    def vminus(self, t, tol=1e-9):
        hs = self.P @ np.array(uvec(t))
        edge = self.P[hs >= hs.max() - tol]
        k = int(np.argmin(edge @ np.array(vvec(t))))
        return tuple(edge[k])

    def supps(self, ts):
        U = np.array([np.cos(ts), np.sin(ts)])
        return np.max(self.P @ U, axis=0)

    def vplus_dots(self, ts, tol=1e-9):
        """⟨v_K⁺(t), v_t⟩ for the angles ts."""
        ts = np.asarray(ts, dtype=float)
        H = self.P @ np.array([np.cos(ts), np.sin(ts)])
        V = self.P @ np.array([-np.sin(ts), np.cos(ts)])
        V = np.where(H >= H.max(axis=0) - tol, V, -np.inf)
        return V.max(axis=0)

    def sigma_fun(self, ts, n=20000):
        """G_K(t) = ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K on the angles ts (`sigmaFun`)."""
        ts = np.asarray(ts, dtype=float)
        lo, hi = min(ts.min(), 0.0), max(ts.max(), 0.0)
        grid = np.unique(np.concatenate([np.linspace(lo, hi, n + 1), ts, [0.0]]))
        h = self.supps(grid)
        cum = np.concatenate([[0.0], np.cumsum((h[1:] + h[:-1]) / 2 * np.diff(grid))])
        cum -= cum[int(np.searchsorted(grid, 0.0))]
        integral = cum[np.searchsorted(grid, ts)]
        return self.vplus_dots(ts) + integral


def regular_polygon(n, rot=0.0, circumscribed=True):
    """The regular n-gon whose edges have the normal angles rot + 2πk/n, circumscribed about the
    unit circle (or inscribed in it)."""
    r = 1 / math.cos(PI / n) if circumscribed else 1.0
    return [mul(r, uvec(rot + (2 * k + 1) * PI / n)) for k in range(n)]


# ------------------------------------------------------------------------------- plot helpers

class Plot:
    """Axes of a graph drawn inside a Figure: the data rectangle [t0, t1] x [g0, g1] is placed at
    the figure point `origin` with the given width and height in figure units."""

    def __init__(self, f, origin, width, height, t0, t1, g0, g1):
        self.f, self.o, self.w, self.h = f, origin, width, height
        self.t0, self.t1, self.g0, self.g1 = t0, t1, g0, g1

    def p(self, t, g):
        return (self.o[0] + (t - self.t0) / (self.t1 - self.t0) * self.w,
                self.o[1] + (g - self.g0) / (self.g1 - self.g0) * self.h)

    def axes(self, xticks, yticks, xlabel=None, ylabel=None, size=12):
        self.f.line(self.p(self.t0, self.g0), self.p(self.t1, self.g0), stroke=FAINT, width=1)
        self.f.line(self.p(self.t0, self.g0), self.p(self.t0, self.g1), stroke=FAINT, width=1)
        for t, label in xticks:
            a = self.p(t, self.g0)
            self.f.line(a, (a[0], a[1] - 0.06), stroke=FAINT, width=1)
            self.f.text((a[0], a[1] - 0.2), label, size=size, color=INK, italic=False)
        for g, label in yticks:
            a = self.p(self.t0, g)
            self.f.line(a, (a[0] - 0.06, a[1]), stroke=FAINT, width=1)
            self.f.text((a[0] - 0.1, a[1]), label, size=size, color=INK, italic=False,
                        anchor='end')
        if xlabel:
            a = self.p(self.t1, self.g0)
            self.f.text((a[0] + 0.12, a[1]), xlabel, size=size + 2, anchor='start')
        if ylabel:
            a = self.p(self.t0, self.g1)
            self.f.text((a[0], a[1] + 0.22), ylabel, size=size + 2)

    def grid(self, gs, dash='3 4'):
        for g in gs:
            self.f.line(self.p(self.t0, g), self.p(self.t1, g), stroke=GREY, width=1, dash=dash)

    def curve(self, ts, gs, **kw):
        pts = [self.p(t, g) for t, g in zip(ts, gs)]
        self.f.polyline(simplify(pts, 0.25 / self.f.s), **kw)


def staircase(plot, ts, gs, color, width=2.0, jump_tol=0.05):
    """The graph of a nondecreasing right-continuous function: its continuous pieces, with a
    filled dot at the value of each jump and an open dot at its left limit."""
    pieces, cur = [], [(ts[0], gs[0])]
    jumps = []
    for i in range(1, len(ts)):
        if gs[i] - gs[i - 1] > jump_tol:
            pieces.append(cur)
            jumps.append((ts[i], gs[i - 1], gs[i]))
            cur = []
        cur.append((ts[i], gs[i]))
    pieces.append(cur)
    for piece in pieces:
        if len(piece) > 1:
            plot.curve([q[0] for q in piece], [q[1] for q in piece], stroke=color, width=width)
    for t, g0, g1 in jumps:
        plot.f.line(plot.p(t, g0), plot.p(t, g1), stroke=color, width=1, dash='2 3')
        plot.f.circle(plot.p(t, g0), 3.2 / plot.f.s, stroke=color, width=1.3, fill='#ffffff')
        plot.f.dot(plot.p(t, g1), r=3.2, fill=color)
    return jumps


def angle_ticks(values):
    names = {0: '0', 1: 'π/2', 2: 'π', 3: '3π/2', 4: '2π'}
    return [(k * PI / 2, names[k]) for k in values]


# ------------------------------------------------------------------------- Chapter 6 figures

def fig_notation():
    """A convex body with a supporting line, an edge, its two vertices, and the frame u_t, v_t."""
    c0, R = (0.25, 0.35), 1.25
    t0 = PI / 3
    h0 = dot(c0, uvec(t0)) + 0.9
    arc = [add(c0, mul(R, uvec(s))) for s in np.linspace(0, 2 * PI, 2000, endpoint=False)]
    K = clip_halfplane(arc, uvec(t0), h0)
    body = Body(K)
    assert abs(body.supp(t0) - h0) < 1e-9
    vp, vm = body.vplus(t0), body.vminus(t0)
    length = norm(sub(vp, vm))
    assert abs(length - 2 * math.sqrt(R * R - 0.81)) < 1e-2
    # v⁺ is the end of the edge in the direction v_t.
    assert dot(sub(vp, vm), vvec(t0)) > 0
    f = Figure(-1.55, 2.6, -1.15, 2.75, 120)
    f.polygon(simplify(K + [K[0]], 0.25 / f.s)[:-1], fill=FILLS[0], stroke=BLUE, width=2.0)
    # The supporting line l_K(t) and the edge e_K(t).
    a, b = add(vp, mul(0.9, vvec(t0))), add(vm, mul(-0.75, vvec(t0)))
    f.line(a, b, stroke=FAINT, width=1.3)
    f.line(vm, vp, stroke=BLUE, width=4.0)
    f.dot(vp, r=3.8, fill=INK)
    f.dot(vm, r=3.8, fill=INK)
    f.text(add(vp, (-0.12, -0.2)), 'v⁺(t)', size=16)
    f.text(add(vm, (0.36, 0.0)), 'v⁻(t)', size=16)
    f.text(add(lerp(vm, vp, 0.2), mul(0.24, uvec(t0))), 'e(t)', size=16, color=BLUE)
    f.text(add(a, mul(0.18, vvec(t0)), (0.0, 0.06)), 'l(t)', size=15, color=FAINT)
    # The frame u_t, v_t at the foot of the perpendicular from O, just outside the line.
    O = (0.0, 0.0)
    foot = mul(h0, uvec(t0))
    m = add(foot, mul(0.1, uvec(t0)))
    arrow(f, foot, add(foot, mul(0.62, uvec(t0))), color=INK)
    arrow(f, m, add(m, mul(0.62, vvec(t0))), color=INK)
    f.text(add(foot, mul(0.78, uvec(t0))), sb('u', 't'), size=16)
    f.text(add(m, mul(0.62, vvec(t0)), mul(0.2, uvec(t0))), sb('v', 't'), size=16)
    # The support value h_K(t): the distance from O to l_K(t).
    f.line(O, foot, stroke=INK, width=1.2, dash='5 4')
    right_angle(f, foot, mul(-1, uvec(t0)), mul(-1, vvec(t0)), size=0.13)
    f.dot(O, r=3.2)
    f.text((-0.12, -0.13), 'O', size=15)
    f.text(add(lerp(O, foot, 0.5), mul(0.27, vvec(t0))), sb('h', 'K', '(t)'), size=16)
    # A second angle whose edge is a single point.
    s = -PI / 5
    p = body.vplus(s)
    assert norm(sub(p, body.vminus(s))) < 1e-2
    a2, b2 = add(p, mul(0.75, vvec(s))), add(p, mul(-0.75, vvec(s)))
    f.line(a2, b2, stroke=FAINT, width=1.3)
    f.dot(p, r=3.6)
    f.text(add(p, mul(0.42, uvec(s))), 'v⁺(s) = v⁻(s)', size=15, anchor='start')
    f.text(add(b2, mul(-0.15, vvec(s)), (0.08, 0)), 'l(s)', size=15, color=FAINT, anchor='start')
    f.text((-0.75, 0.9), 'K', size=20, color=BLUE)
    return f.save(f'{CH6}/notation',
                  'A convex body K with its supporting line l(t) of normal angle t, which meets K '
                  'in the edge e(t) from the vertex v⁻(t) to the vertex v⁺(t); the unit vectors '
                  'u_t, normal to the line, and v_t, along it; the support value h_K(t), the '
                  'distance from the origin O to the line; and a supporting line l(s) that meets '
                  'K in a single point')


def examples_bodies():
    rect = Body([(-1, 0), (1, 0), (1, 1), (-1, 1)])
    arc = [uvec(s) for s in np.linspace(0, PI, 4001)]
    semi = Body(arc + [(-1.0, 0.0), (1.0, 0.0)])
    return rect, semi


def fig_examples():
    """The rectangle and the semicircle of Baek's overview, and the distribution functions G_K."""
    rect, semi = examples_bodies()
    t0, t1 = -PI / 4, 2 * PI + PI / 4
    ts = np.concatenate([np.linspace(t0, t1, 1101), [0.0, PI / 2, PI, 3 * PI / 2, 2 * PI]])
    ts = np.unique(ts)
    G_rect = rect.sigma_fun(ts)
    G_semi = semi.sigma_fun(ts)
    # Rectangle: atoms 1, 2, 1, 2 at 0, π/2, π, 3π/2 and 1 again at 2π; constant in between.
    f = Figure(-0.4, 15.0, -0.2, 7.6, 62)
    left, right = (0.5, 0.0), (8.0, 0.0)
    P1 = Plot(f, (left[0], 0.35), 6.2, 3.9, t0, t1, 0, 7.6)
    P2 = Plot(f, (right[0], 0.35), 6.2, 3.9, t0, t1, 0, 7.6)
    P1.grid([1, 3, 4, 6, 7])
    P2.grid([PI, PI + 2])
    jumps1 = staircase(P1, ts, G_rect, BLUE)
    jumps2 = staircase(P2, ts, G_semi, BLUE)
    expect1 = [(0.0, 1.0), (PI / 2, 2.0), (PI, 1.0), (3 * PI / 2, 2.0), (2 * PI, 1.0)]
    assert len(jumps1) == 5
    for (t, g0, g1), (te, size) in zip(jumps1, expect1):
        assert abs(t - te) < 1e-9 and abs(g1 - g0 - size) < 2e-3, (t, g1 - g0)
    # Semicircle: G_K(t) = t on [0, π], one atom 2 at 3π/2, and no other jump.
    assert len(jumps2) == 1 and abs(jumps2[0][0] - 3 * PI / 2) < 1e-9
    assert abs(jumps2[0][2] - jumps2[0][1] - 2) < 2e-3
    on = (ts >= 0) & (ts <= PI)
    assert np.max(np.abs(G_semi[on] - ts[on])) < 2e-3
    # Total masses on [0, 2π): the perimeters 6 and π + 2.
    i0 = int(np.searchsorted(ts, 0.0))
    i2 = int(np.searchsorted(ts, 2 * PI))
    assert abs(G_rect[i2 - 1] - (G_rect[i0] - 1) - 6) < 2e-3
    assert abs(G_semi[i2 - 1] - G_semi[i0] - (PI + 2)) < 2e-3
    for P, ticks in ((P1, [(1, '1'), (3, '3'), (4, '4'), (6, '6'), (7, '7')]),
                     (P2, [(PI, 'π'), (PI + 2, 'π + 2')])):
        P.axes(angle_ticks(range(5)), ticks, xlabel='t', ylabel=sb('G', 'K', '(t)'))
    # The two bodies, above their graphs.
    sc = 1.05
    rx, ry = left[0] + 3.0, 5.55
    R = [(rx + sc * x, ry + sc * y) for x, y in [(-1, 0), (1, 0), (1, 1), (-1, 1)]]
    f.polygon(R, fill=FILLS[0], stroke=BLUE, width=2.0)
    labels = [((1, 0.5), 0, '1', 'σ({0})'), ((0, 1), PI / 2, '2', 'σ({π/2})'),
              ((-1, 0.5), PI, '1', 'σ({π})'), ((0, 0), 3 * PI / 2, '2', 'σ({3π/2})')]
    for (x, y), t, val, name in labels:
        q = (rx + sc * x, ry + sc * y)
        arrow(f, q, add(q, mul(0.42, uvec(t))), color=INK, width=1.2)
        off = {0: (0.62, 0.0), PI / 2: (0.0, 0.62), PI: (-0.62, 0.0),
               3 * PI / 2: (0.0, -0.62)}[t]
        f.text(add(q, off), f'{name} = {val}', size=13, italic=False,
               anchor='start' if t == 0 else ('end' if t == PI else 'middle'))
    sx, sy = right[0] + 3.0, 5.35
    arc = [(sx + 1.3 * math.cos(s), sy + 1.3 * math.sin(s)) for s in np.linspace(0, PI, 200)]
    f.polygon(arc, fill=FILLS[0], stroke=BLUE, width=2.0)
    for t in (PI / 6, PI / 2, 5 * PI / 6):
        q = (sx + 1.3 * math.cos(t), sy + 1.3 * math.sin(t))
        arrow(f, q, add(q, mul(0.4, uvec(t))), color=INK, width=1.2)
    f.text((sx + 1.62, sy + 1.12), 'density 1 on [0, π]', size=13, italic=False, anchor='start')
    q = (sx, sy)
    arrow(f, q, add(q, (0, -0.4)), color=INK, width=1.2)
    f.text((sx, sy - 0.62), 'σ({3π/2}) = 2', size=13, italic=False)
    return f.save(f'{CH6}/examples',
                  'Left: the rectangle [-1, 1] x [0, 1] and the graph of its distribution function '
                  'G_K over the angles from -π/4 to 9π/4, a staircase with jumps 1, 2, 1, 2 at 0, '
                  'π/2, π, 3π/2 and again 1 at 2π. Right: the half-disk of radius 1 and its '
                  'distribution function, which rises with slope 1 on [0, π], stays constant, and '
                  'jumps by 2 at 3π/2')


def disk_cut():
    """The unit disk cut by the lines y = -0.55 and ⟨p, u_{π/4}⟩ = 0.8."""
    pts = [uvec(s) for s in np.linspace(0, 2 * PI, 6000, endpoint=False)]
    pts = clip_halfplane(pts, (0, -1), 0.55)
    return clip_halfplane(pts, uvec(PI / 4), 0.8)


def fig_gauss_minkowski():
    """Theorem 6.12 integrated: the boundary from v⁺(a) to v⁺(b) is the sum of the v_t dσ_K(t)."""
    K = disk_cut()
    body = Body(K)
    a, b = -PI / 6, 3 * PI / 4
    pa, pb = body.vplus(a), body.vplus(b)
    assert norm(sub(pa, uvec(a))) < 2e-3 and norm(sub(pb, uvec(b))) < 2e-3
    # The atom at π/4 is the chord of length 2 sin(arccos 0.8) = 1.2.
    c0 = math.acos(0.8)
    e0, e1 = uvec(PI / 4 - c0), uvec(PI / 4 + c0)
    assert abs(norm(sub(e1, e0)) - 1.2) < 1e-12
    # v⁺(b) - v⁺(a) = ∫_{(a, b]} v_t dσ_K(t), with σ_K computed from G_K on a fine partition.
    ts = np.unique(np.concatenate([np.linspace(a, b, 4001), [PI / 4]]))
    G = body.sigma_fun(ts)
    dG = np.diff(G)
    assert dG.min() > -1e-6
    total = (float(np.sum(dG * -np.sin(ts[1:]))), float(np.sum(dG * np.cos(ts[1:]))))
    assert norm(sub(total, sub(pb, pa))) < 5e-3, (total, sub(pb, pa))
    k = int(np.searchsorted(ts, PI / 4))
    assert abs(G[k] - G[k - 1] - 1.2) < 1e-2
    f = Figure(-1.55, 2.15, -0.72, 1.32, 135)
    f.polygon(simplify(K + [K[0]], 0.25 / f.s)[:-1], fill=FILLS[0], stroke=BLUE, width=1.6)
    # The boundary from v⁺(a) to v⁺(b), as a chain of vectors v_t dσ_K(t).
    chain = [pa]
    arcs = [(a, PI / 4 - c0), (PI / 4 + c0, b)]
    for i, (s0, s1) in enumerate(arcs):
        m = max(2, int(round((s1 - s0) / 0.26)))
        for s in np.linspace(s0, s1, m + 1)[1:]:
            chain.append(uvec(s))
        if i == 0:
            chain.append(e1)
    for p, q in zip(chain, chain[1:]):
        if norm(sub(q, p)) > 1.0:
            arrow(f, p, q, color=ORANGE, width=2.6)
        else:
            arrow(f, p, q, color=BLUE, width=2.0)
    arrow(f, pa, pb, color=INK, width=1.3)
    f.dot(pa, r=3.6)
    f.dot(pb, r=3.6)
    f.text(add(pa, (0.28, -0.08)), 'v⁺(a)', size=16)
    f.text(add(pb, (-0.32, 0.08)), 'v⁺(b)', size=16)
    mid = lerp(e0, e1, 0.5)
    f.text(add(mid, mul(0.42, uvec(PI / 4)), (0.1, 0.0)), 'σ({π/4})' + ' ' + sb('v', 'π/4'),
           size=15, color=ORANGE, anchor='start')
    f.text((1.08, -0.18), sb('v', 't', ' dt'), size=15, color=BLUE, anchor='start')
    f.text((-0.3, 0.12), 'v⁺(b) − v⁺(a)', size=15)
    f.text((-0.55, -0.32), 'K', size=19, color=BLUE)
    return f.save(f'{CH6}/gauss-minkowski',
                  'A convex body K: the unit disk cut by a horizontal line at the bottom and by a '
                  'chord with normal angle π/4. From the vertex v⁺(a), a = -π/6, to the vertex '
                  'v⁺(b), b = 3π/4, the boundary is a chain of small vectors v_t dt along the arcs '
                  'and one vector of length 1.2 along the chord; their sum is v⁺(b) - v⁺(a)')


def fig_area_formula():
    """|K| = ½ Σ σ_K({t}) (h_K(t) - ⟨c, u_t⟩) for a polygon: triangles over the edges."""
    V = [(-1.25, -0.55), (0.85, -0.85), (1.45, 0.25), (0.45, 1.2), (-1.05, 0.85)]
    c = (0.0, 0.1)
    body = Body(V)
    edges = []
    for i, p in enumerate(V):
        q = V[(i + 1) % len(V)]
        d = sub(q, p)
        t = math.atan2(-d[0], d[1])     # the outer normal u_t of the edge pq, counterclockwise
        t = t % (2 * PI)
        length = norm(d)
        assert abs(body.supp(t) - dot(p, uvec(t))) < 1e-12
        # The edge is e_K(t), and σ_K({t}) = ⟨v⁺(t) - v⁻(t), v_t⟩ is its length.
        assert abs(dot(sub(body.vplus(t), body.vminus(t)), vvec(t)) - length) < 1e-12
        edges.append((p, q, t, length))
    area = polygon_area(V)
    s1 = sum(0.5 * L * (body.supp(t) - dot(c, uvec(t))) for _, _, t, L in edges)
    s0 = sum(0.5 * L * body.supp(t) for _, _, t, L in edges)
    assert abs(s1 - area) < 1e-12 and abs(s0 - area) < 1e-12
    f = Figure(-1.6, 1.9, -1.15, 1.5, 150)
    for i, (p, q, t, L) in enumerate(edges):
        f.polygon([c, p, q], fill=FILLS[0] if i % 2 == 0 else '#eef4ff', stroke=BLUE, width=1.0)
    f.polygon(V, fill='none', stroke=BLUE, width=2.0)
    # One triangle: base σ_K({t}) on the edge, height h_K(t) - ⟨c, u_t⟩ from c.
    p, q, t, L = edges[1]
    foot = add(c, mul(body.supp(t) - dot(c, uvec(t)), uvec(t)))
    f.line(c, foot, stroke=INK, width=1.3, dash='5 4')
    right_angle(f, foot, mul(-1, uvec(t)), vvec(t), size=0.1)
    f.text(add(lerp(c, foot, 0.5), mul(-0.3, vvec(t))),
           sb('h', 'K', '(t) − ⟨c, ') + sb('u', 't', '⟩'), size=14)
    f.line(p, q, stroke=ORANGE, width=3.2)
    f.text(add(lerp(p, q, 0.5), mul(0.24, uvec(t))), 'σ({t})', size=15, color=ORANGE,
           anchor='start')
    arrow(f, lerp(p, q, 0.8), add(lerp(p, q, 0.8), mul(0.35, uvec(t))), color=INK, width=1.2)
    f.text(add(lerp(p, q, 0.8), mul(0.48, uvec(t))), sb('u', 't'), size=15)
    f.dot(c, r=3.4)
    f.text(add(c, (-0.12, 0.1)), 'c', size=16)
    return f.save(f'{CH6}/area-formula',
                  'A convex pentagon K cut into five triangles with a common apex at an interior '
                  'point c, one over each edge. The triangle over the edge with normal angle t has '
                  'base σ_K({t}), the length of the edge, and height h_K(t) - ⟨c, u_t⟩, the distance '
                  'from c to the edge, so the area of K is the sum of the halves of their products')


def fig_weak_convergence():
    """The distribution functions of inscribed regular n-gons converge to that of the disk."""
    ts = np.linspace(0, 2 * PI, 3001)
    disk = Body([uvec(s) for s in np.linspace(0, 2 * PI, 40000, endpoint=False)])
    G = disk.sigma_fun(ts)
    assert np.max(np.abs(G - ts)) < 1e-3
    f = Figure(-0.75, 9.0, -0.5, 7.4, 62)
    P = Plot(f, (0.0, 0.0), 7.6, 6.2, 0, 2 * PI, 0, 2 * PI + 0.7)
    P.grid([PI / 2, PI, 3 * PI / 2, 2 * PI])
    colors = {4: PURPLE, 8: GREEN, 16: ORANGE}
    test = lambda s: math.cos(s) ** 2 + 0.3 * math.sin(3 * s)  # a continuous periodic function
    exact = PI  # ∫₀^{2π} cos² = π, ∫ sin 3t = 0
    errors = []
    for n in (4, 8, 16):
        body = Body(regular_polygon(n, circumscribed=False))
        Gn = body.sigma_fun(ts)
        staircase(P, ts, Gn, colors[n], width=1.8, jump_tol=1e-6 + 1.0 / n)
        # The atoms: n edges of length 2 sin(π/n) at the angles 2πk/n.
        atoms = [(2 * PI * k / n, 2 * math.sin(PI / n)) for k in range(n)]
        integral = sum(m * test(t) for t, m in atoms)
        errors.append(abs(integral - exact))
        y = 2.3 - 0.42 * [4, 8, 16].index(n)
        f.line((5.0, y), (5.5, y), stroke=colors[n], width=2.0)
        f.text((5.63, y), f'regular {n}-gon', size=13, color=INK, anchor='start', italic=False)
    assert errors[0] > errors[1] > errors[2]
    P.curve(ts, G, stroke=BLUE, width=2.4)
    f.line((5.0, 2.3 - 1.26), (5.5, 2.3 - 1.26), stroke=BLUE, width=2.4)
    f.text((5.63, 2.3 - 1.26), 'unit disk', size=13, color=INK, anchor='start', italic=False)
    P.axes(angle_ticks(range(5)), [(PI / 2, 'π/2'), (PI, 'π'), (3 * PI / 2, '3π/2'),
                                   (2 * PI, '2π')], xlabel='t', ylabel=sb('G', 'K', '(t)'))
    return f.save(f'{CH6}/weak-convergence',
                  'The distribution functions of the regular 4-gon, 8-gon and 16-gon inscribed in '
                  'the unit circle, staircases with n jumps of 2 sin(π/n) at the angles 2πk/n, and '
                  'the distribution function G(t) = t of the unit disk, a straight line, which the '
                  'staircases approach')


# ------------------------------------------------------------- Gerver's sofa in Romik's frame

def phase(t):
    """The phase (0, ..., 4) of `GerverParams.path` at t."""
    if t < PHI:
        return 0
    if t < THETA:
        return 1
    if t <= PI / 2 - THETA:
        return 2
    if t <= PI / 2 - PHI:
        return 3
    return 4


def frame(t):
    """(w₁, w₂, w₁', w₂', w₁'', w₂'') of the phase at t: 𝐱(t) = R_t (w₁, w₂) + κ."""
    c, s = math.cos(t), math.sin(t)
    i = phase(t)
    if i == 0:
        a1, a2 = gerver.a1, gerver.a2
        return (a1 * c + a2 * s - 1, -a2 * c + a1 * s - 0.5, -a1 * s + a2 * c, a2 * s + a1 * c,
                -a1 * c - a2 * s, a2 * c - a1 * s)
    if i == 1:
        b1, b2 = gerver.b1, gerver.b2
        return (-t * t / 4 + b1 * t + b2, t / 2 - b1 - 1, -t / 2 + b1, 0.5, -0.5, 0.0)
    if i == 2:
        return (gerver.c1 - t, gerver.c2 + t, -1.0, 1.0, 0.0, 0.0)
    if i == 3:
        d1, d2 = gerver.d1, gerver.d2
        return (-t / 2 + d1 - 1, -t * t / 4 + d1 * t + d2, -0.5, -t / 2 + d1, 0.0, -0.5)
    e1, e2 = gerver.e1, gerver.e2
    return (e1 * c + e2 * s - 0.5, -e2 * c + e1 * s - 1, -e1 * s + e2 * c, e2 * s + e1 * c,
            -e1 * c - e2 * s, e2 * c - e1 * s)


def alpha(t):
    """⟨𝐱'(t), u_t⟩ = w₁' - w₂ (`gs_α`)."""
    w1, w2, w1p, w2p, _, _ = frame(t)
    return w1p - w2


def beta(t):
    """⟨𝐱'(t), v_t⟩ = w₂' + w₁ (`gs_β`)."""
    w1, w2, w1p, w2p, _, _ = frame(t)
    return w2p + w1


def rho_A(t):
    """⟨𝐀'(t), v_t⟩ = w₁'' + w₁ + 1, the density of σ_K at t ∈ [0, π/2)."""
    w1, _, _, _, w1pp, _ = frame(t)
    return w1pp + w1 + 1


def rho_C(t):
    """⟨-𝐂'(t), u_t⟩ = w₂'' + w₂ + 1, the density of σ_K at t + π/2 ∈ (π/2, π]."""
    _, w2, _, _, _, w2pp = frame(t)
    return w2pp + w2 + 1


def xpath(t):
    return gerver.path(t)


def xprime(t):
    return add(mul(alpha(t), uvec(t)), mul(beta(t), vvec(t)))


def contact(name, t):
    """Romik's contact points (`contactA`, ..., `contactD` of `GerverParams.path`)."""
    x, u, v = xpath(t), uvec(t), vvec(t)
    if name == 'A':
        return add(x, u, mul(alpha(t), v))
    if name == 'B':
        return add(x, mul(alpha(t), v))
    if name == 'C':
        return add(x, v, mul(-beta(t), u))
    return add(x, mul(-beta(t), u))


def outer_corner(t):
    return add(xpath(t), uvec(t), vvec(t))


def gerver_supp(s):
    """The support function of the cap of Gerver's sofa on [0, π] and at 3π/2."""
    if abs(s - 3 * PI / 2) < 1e-12:
        return 0.0
    if s <= PI / 2:
        return dot(xpath(s), uvec(s)) + 1
    return dot(xpath(s - PI / 2), vvec(s - PI / 2)) + 1


def check_gerver():
    """The facts about Gerver's sofa that the captions of Chapter 7 state."""
    h = 1e-6
    for t in np.linspace(0.01, PI / 2 - 0.01, 60):
        # 𝐱' = α u_t + β v_t, by finite differences.
        d = mul(1 / (2 * h), sub(xpath(t + h), xpath(t - h)))
        assert norm(sub(d, xprime(t))) < 1e-6, t
        # The injectivity condition: f = 1 - α > 1 and g = 1 + β > 1.
        assert alpha(t) < 0 < beta(t), t
        # The first coordinate of the rotation path decreases.
        assert xprime(t)[0] < 0, t
        # Condition (1): the densities of σ_K are nonnegative, and G_K(t) = ⟨𝐀(t), v_t⟩ + ∫₀ᵗ h
        # has the derivative ρ_A(t) (the integral contributes h(t) = ⟨𝐀(t), u_t⟩).
        assert rho_A(t) >= 0 and rho_C(t) >= 0, t
        G = lambda r: dot(contact('A', r), vvec(r))
        dG = (G(t + h) - G(t - h)) / (2 * h) + gerver_supp(t)
        if abs(t - PHI) > 1e-3 and abs(t - THETA) > 1e-3:
            assert abs(dG - rho_A(t)) < 1e-5, (t, dG, rho_A(t))
    # 𝐀(0) = (1, 0); the top edge from 𝐀(π/2) to 𝐂(0) and the bottom edge from 𝐂(π/2) to 𝐀(0).
    assert norm(sub(contact('A', 0.0), (1.0, 0.0))) < 1e-12
    assert abs(contact('A', PI / 2)[1] - 1) < 1e-12 and abs(contact('C', 0.0)[1] - 1) < 1e-12
    assert abs(contact('C', PI / 2)[1]) < 1e-12
    # The ends of the inner contact curves: 𝐁(π/2 - θ) = 𝐱(φ), 𝐃(θ) = 𝐱(π/2 - φ), on the x-axis
    # at 𝐁(π/2) and 𝐃(0).
    assert norm(sub(contact('B', PI / 2 - THETA), xpath(PHI))) < 1e-9
    assert norm(sub(contact('D', THETA), xpath(PI / 2 - PHI))) < 1e-9
    assert abs(contact('B', PI / 2)[1]) < 1e-12 and abs(contact('D', 0.0)[1]) < 1e-12


def gerver_cap(m=400):
    """The cap K of Gerver's sofa, counterclockwise: the bottom edge, 𝐀, the top edge, 𝐂."""
    ts = np.linspace(0, PI / 2, m + 1)
    return [contact('A', t) for t in ts] + [contact('C', t) for t in ts]


def gerver_niche(m=400):
    """The niche 𝒩(K): the region under 𝐁, 𝐱|[φ, π/2 - φ] and 𝐃, above the x-axis."""
    B = [contact('B', t) for t in np.linspace(PI / 2, PI / 2 - THETA, m + 1)]
    X = [xpath(t) for t in np.linspace(PHI, PI / 2 - PHI, 2 * m + 1)]
    D = [contact('D', t) for t in np.linspace(THETA, 0, m + 1)]
    return B + X + D


def place_frame(t, q):
    """The coordinates (⟨q - 𝐱(t), u_t⟩, ⟨q - 𝐱(t), v_t⟩) of q in the frame of the hallway L_t."""
    d = sub(q, xpath(t))
    return (dot(d, uvec(t)), dot(d, vvec(t)))


def from_frame(t, p):
    """The point with the coordinates p in the frame of L_t: 𝐱(t) + R_t p."""
    return add(xpath(t), mul(p[0], uvec(t)), mul(p[1], vvec(t)))


# ------------------------------------------------------------------------- Chapter 7 figures

CURVE = {'A': BLUE, 'C': BLUE, 'B': GREEN, 'D': GREEN, 'x': ORANGE}


def draw_hallway(f, t, box, offset=(0.0, 0.0), big=12.0):
    """The supporting hallway L_t = 𝐱(t) + R_t L of Gerver's sofa, clipped to the box."""
    shift = lambda pts: [add(p, offset) for p in pts]
    floor = [(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)]
    poly = clip_box([from_frame(t, p) for p in floor], box)
    f.polygon(shift(poly), fill=FLOOR, stroke='none', width=0)
    for wall in ([(-big, 1), (1, 1), (1, -big)], [(-big, 0), (0, 0), (0, -big)]):
        pts = [from_frame(t, p) for p in wall]
        for p, q in zip(pts, pts[1:]):
            seg = clip_segment(p, q, box)
            if seg:
                f.line(add(seg[0], offset), add(seg[1], offset), stroke=WALL, width=2.6)


def fig_contacts(sofa):
    """Gerver's sofa and its supporting hallways at two angles, with the contact points."""
    t1 = 0.45
    t2 = PI / 2 - t1
    assert phase(t1) == 1 and phase(t2) == 3
    box = (-2.55, 1.5, -0.62, 2.12)
    dx = box[1] - box[0] + 0.35
    f = Figure(box[0], box[1] + dx, box[2], box[3] + 0.08, 96)
    for k, t in enumerate((t1, t2)):
        off = (k * dx, 0.0)
        sh = lambda p: add(p, off)
        draw_hallway(f, t, box, off)
        f.polygon(simplify([sh(p) for p in sofa], 0.25 / f.s), fill=FILLS[0], stroke=BLUE,
                  width=1.2, opacity=0.9)
        # The curves traced by the contact points, and the rotation path.
        tr = {'A': (0, PI / 2), 'C': (0, PI / 2), 'B': (PI / 2 - THETA, PI / 2),
              'D': (0, THETA)}
        for name, (s0, s1) in tr.items():
            pts = [sh(contact(name, s)) for s in np.linspace(s0, s1, 200)]
            f.polyline(simplify(pts, 0.25 / f.s), stroke=CURVE[name],
                       width=2.4 if name in 'BD' else 2.0)
        f.polyline(simplify([sh(xpath(s)) for s in np.linspace(0, PI / 2, 300)], 0.25 / f.s),
                   stroke=ORANGE, width=1.6, dash='5 3')
        names = ['A', 'C', 'D'] if k == 0 else ['A', 'C', 'B']
        x, y = xpath(t), outer_corner(t)
        # Each contact point lies on its wall, and the sofa lies in the hallway.
        frames = {n: place_frame(t, contact(n, t)) for n in 'ABCD'}
        assert abs(frames['A'][0] - 1) < 1e-12 and abs(frames['C'][1] - 1) < 1e-12
        assert abs(frames['B'][0]) < 1e-12 and abs(frames['D'][1]) < 1e-12
        assert frames['B'][1] <= 0 if k == 1 else frames['D'][0] <= 0
        for X, Y in (place_frame(t, p) for p in sofa[::5]):
            assert X <= 1 + 1e-6 and Y <= 1 + 1e-6 and (X >= -1e-6 or Y >= -1e-6)
        for n in names:
            p = contact(n, t)
            f.dot(sh(p), r=4.0, fill=CURVE[n])
        f.dot(sh(x), r=4.0, fill=ORANGE)
        f.dot(sh(y), r=3.6, fill=INK)
        u, v = uvec(t), vvec(t)
        lab = {'A': mul(0.2, u), 'C': mul(0.2, v), 'D': add(mul(-0.22, v), mul(0.06, u)),
               'B': add(mul(-0.22, u), mul(0.04, v))}
        for n in names:
            f.text(sh(add(contact(n, t), lab[n])), n + '(t)', size=15, color=CURVE[n])
        f.text(sh(add(x, mul(0.06, u), mul(0.26, v))), 'x(t)', size=15, color=ORANGE)
        f.text(sh(add(y, mul(0.14, u), mul(0.14, v))), 'y(t)', size=15)
        # The walls: a(t) and c(t) through y(t), b(t) and d(t) from x(t).
        f.text(sh(add(y, mul(0.18, u), mul(-1.25, v))), 'a(t)', size=14, color=WALL)
        f.text(sh(add(y, mul(-0.75, u), mul(0.2, v))), 'c(t)', size=14, color=WALL)
        f.text(sh(add(x, mul(-0.2, u), mul(-0.85, v))), 'b(t)', size=14, color=WALL)
        f.text(sh(add(x, mul(-0.85 if k == 1 else -0.45, u), mul(-0.2, v))), 'd(t)', size=14,
               color=WALL)
        tl = 't = 0.45' if k == 0 else 't = π/2 − 0.45'
        f.text(sh((box[1] - 0.1, box[3] - 0.1)), tl, size=14, italic=False, anchor='end')
    return f.save(f'{CH7}/contacts',
                  "Gerver's sofa, fixed, with its supporting hallway at the angle t = 0.45 (left) "
                  "and at π/2 - 0.45 (right). The outer walls a(t) and c(t) meet at the outer "
                  "corner y(t) and touch the sofa at A(t) and C(t); the inner walls b(t) and d(t) "
                  "start at the inner corner x(t). On the left the wall d(t) touches the sofa at "
                  "D(t), on the right the wall b(t) touches it at B(t). The curves traced by A and "
                  "C, by B and D, and the rotation path x are drawn")


def fig_rotation_path():
    """The cap, the niche and the rotation path of Gerver's sofa, with the velocities 𝐱'(t)."""
    K, N = gerver_cap(), gerver_niche()
    assert abs(polygon_area(K) - polygon_area(N) - 2.21953) < 5e-5
    assert abs(xpath(PI / 2)[0] + 1.228) < 5e-4 and abs(xpath(PI / 2)[1]) < 1e-12
    f = Figure(-2.42, 1.2, -0.26, 1.12, 175)
    eps = 0.25 / f.s
    f.polygon(simplify(K, eps), fill=FILLS[0], stroke=BLUE, width=2.0)
    f.polygon(simplify(N, eps), fill=FILLS[1], stroke='none', width=0)
    f.polyline(simplify(N[:-1], eps), stroke=BLUE, width=1.2)
    ts = np.linspace(0, PI / 2, 400)
    xs = [xpath(t) for t in ts]
    # The first coordinate decreases strictly: the path does not cross itself.
    assert all(q[0] < p[0] for p, q in zip(xs, xs[1:]))
    f.polyline(simplify(xs, eps), stroke=ORANGE, width=2.6)
    for t in (PI / 8, PI / 4, 3 * PI / 8):
        x = xpath(t)
        d = xprime(t)
        assert dot(d, uvec(t)) < 0 < dot(d, vvec(t))
        # The open quadrant {⟨w, u_t⟩ < 0 < ⟨w, v_t⟩} in which 𝐱'(t) lies.
        r = 0.28
        f.polygon([x, add(x, mul(-r, uvec(t))), add(x, mul(-r, uvec(t)), mul(r, vvec(t))),
                   add(x, mul(r, vvec(t)))], fill=FILLS[2], stroke='none', width=0,
                  opacity=0.85)
        f.line(x, add(x, mul(-r, uvec(t))), stroke=GREEN, width=1.0, dash='3 3')
        f.line(x, add(x, mul(r, vvec(t))), stroke=GREEN, width=1.0, dash='3 3')
        arrow(f, x, add(x, mul(0.3, d)), color=INK, width=1.6)
        f.dot(x, r=3.4, fill=ORANGE)
    f.dot(xpath(0), r=3.6, fill=ORANGE)
    f.dot(xpath(PI / 2), r=3.6, fill=ORANGE)
    f.text(add(xpath(0), (0.02, -0.13)), 'x(0)', size=15, color=ORANGE)
    f.text(add(xpath(PI / 2), (0.0, -0.13)), 'x(π/2)', size=15, color=ORANGE)
    x = xpath(PI / 4)
    f.text(add(x, mul(0.3, xprime(PI / 4)), (0.0, 0.1)), "x'(π/4)", size=15)
    f.text((-2.0, 0.75), 'K', size=19, color=BLUE)
    f.text((-0.62, 0.17), '𝒩(K)', size=16, color=ORANGE, italic=False)
    return f.save(f'{CH7}/rotation-path',
                  "The cap K of Gerver's sofa, with its niche shaded orange, and the rotation path "
                  "x from x(0) to x(π/2). At t = π/8, π/4 and 3π/8 the velocity x'(t), scaled by "
                  "0.3, points into the shaded quadrant between the directions -u_t and v_t, so the "
                  "first coordinate of x decreases")


def fig_arms():
    """The arm lengths f(t), g(t) of Gerver's cap and the velocity of the inner corner."""
    t = 0.6
    K = gerver_cap()
    x, y = xpath(t), outer_corner(t)
    A, C = contact('A', t), contact('C', t)
    u, v = uvec(t), vvec(t)
    fl, gl = 1 - alpha(t), 1 + beta(t)
    # y(t) = A + f v_t = C + g u_t (Proposition 7.5), and x'(t) = -(f - 1) u_t + (g - 1) v_t.
    assert norm(sub(y, add(A, mul(fl, v)))) < 1e-12 and norm(sub(y, add(C, mul(gl, u)))) < 1e-12
    assert norm(sub(xprime(t), add(mul(-(fl - 1), u), mul(gl - 1, v)))) < 1e-12
    assert abs(fl - 1.655) < 5e-4 and abs(gl - 2.014) < 5e-4
    box = (-2.5, 1.45, -0.3, 2.42)
    f = Figure(*box, 140)
    f.polygon(simplify(K, 0.25 / f.s), fill=FILLS[0], stroke=BLUE, width=1.6)
    f.polygon(simplify(gerver_niche(), 0.25 / f.s), fill='#ffffff', stroke=BLUE, width=1.0)
    for n, c in ((u, dot(y, u)), (v, dot(y, v))):
        seg = line_in_box(n, c, box)
        f.line(seg[0], seg[1], stroke=WALL, width=1.6)
    for n, c in ((u, dot(x, u)), (v, dot(x, v))):
        seg = line_in_box(n, c, box)
        f.line(seg[0], seg[1], stroke=FAINT, width=1.2, dash='5 4')
    f.line(A, y, stroke=PURPLE, width=4.0)
    f.line(C, y, stroke=GREEN, width=4.0)
    f.text(add(lerp(A, y, 0.5), mul(0.2, u)), 'f(t)', size=16, color=PURPLE)
    f.text(add(lerp(C, y, 0.55), mul(0.2, v)), 'g(t)', size=16, color=GREEN)
    f.dot(A, r=4.0, fill=BLUE)
    f.dot(C, r=4.0, fill=BLUE)
    f.dot(y, r=3.6)
    f.text(add(A, mul(0.27, u), mul(-0.05, v)), 'A(t)', size=15, color=BLUE)
    f.text(add(C, mul(-0.18, u), mul(0.2, v)), 'C(t)', size=15, color=BLUE)
    f.text(add(y, mul(0.17, u), mul(0.17, v)), 'y(t)', size=15)
    # The velocity of the inner corner and its two components, at half scale.
    sc = 0.5
    p1 = add(x, mul(-sc * (fl - 1), u))
    arrow(f, x, p1, color=PURPLE, width=1.3)
    arrow(f, p1, add(p1, mul(sc * (gl - 1), v)), color=GREEN, width=1.3)
    arrow(f, x, add(x, mul(sc, xprime(t))), color=INK, width=2.0)
    f.dot(x, r=4.0, fill=ORANGE)
    f.text(add(x, mul(0.2, u), mul(-0.12, v)), 'x(t)', size=15, color=ORANGE)
    f.text(add(lerp(x, p1, 0.5), mul(-0.24, v)), '−(f − 1)' + sb('u', 't'), size=14,
           color=PURPLE)
    q = add(p1, mul(0.5 * sc * (gl - 1), v))
    f.text(add(q, mul(-0.15, u)), '(g − 1)' + sb('v', 't'), size=14, color=GREEN, anchor='end')
    f.text(add(x, mul(sc, xprime(t)), mul(0.16, v), mul(0.05, u)), "x'(t)", size=15)
    f.text(add(y, mul(0.12, u), mul(-0.62, v)), 'a(t)', size=14, color=WALL)
    f.text(add(y, mul(-0.55, u), mul(0.16, v)), 'c(t)', size=14, color=WALL)
    return f.save(f'{CH7}/arms',
                  "The cap of Gerver's sofa and its supporting hallway at t = 0.6: the outer walls "
                  "a(t) and c(t) meet at y(t) and touch the cap at A(t) and C(t), at the distances "
                  "f(t) = 1.655 and g(t) = 2.014 from y(t). The inner walls, dashed, meet at x(t), "
                  "whose velocity x'(t), drawn at half scale, is the sum of -(f(t) - 1) u_t and (g(t) - 1) v_t")


# ------------------------------------------------- the polygon cap of §7.3, with n = 4 steps

N_STEPS = 4
DELTA = (PI / 2) / N_STEPS
T_MID = PI / 4


def polygon_cap():
    """The polygon cap with angle set Θ_4 = {π/8, π/4, 3π/8} whose support values at its normal
    angles Θ_4 ∪ (Θ_4 + π/2) ∪ {π/2, 3π/2} are those of Gerver's cap."""
    normals = [k * DELTA for k in range(1, N_STEPS)] + [PI / 2] + \
        [PI / 2 + k * DELTA for k in range(1, N_STEPS)] + [3 * PI / 2]
    big = 10.0
    pts = [(-big, -big), (big, -big), (big, big), (-big, big)]
    for s in normals:
        pts = clip_halfplane(pts, uvec(s), gerver_supp(s))
    return pts, normals


def to_frame_line(t, n, c):
    """The line ⟨q, n⟩ = c in the coordinates of the frame of L_t."""
    x = xpath(t)
    return (dot(n, uvec(t)), dot(n, vvec(t))), c - dot(x, n)


def frame_lines(s):
    """The walls of L_s in the frame of L_t, t = π/4, as (normal, constant): a, b, c, d."""
    h, h2 = gerver_supp(s), gerver_supp(s + PI / 2)
    return {'a': to_frame_line(T_MID, uvec(s), h), 'b': to_frame_line(T_MID, uvec(s), h - 1),
            'c': to_frame_line(T_MID, vvec(s), h2), 'd': to_frame_line(T_MID, vvec(s), h2 - 1)}


def polygon_cap_data():
    """The quantities of Lemma 7.13 and Theorem 7.15 for the polygon cap, in the frame of L_t."""
    t, d = T_MID, DELTA
    P, _ = polygon_cap()
    body = Body(P)
    L = {s: frame_lines(s) for s in (t - d, t, t + d)}
    # In the frame of L_t, b(t) is X = 0, d(t) is Y = 0, a(t) is X = 1 and c(t) is Y = 1.
    for key, (n, c) in (('a', ((1, 0), 1)), ('b', ((1, 0), 0)), ('c', ((0, 1), 1)),
                        ('d', ((0, 1), 0))):
        n2, c2 = L[t][key]
        assert norm(sub(n2, n)) < 1e-12 and abs(c2 - c) < 1e-12
    out = {'body': body, 'P': P, 'L': L}
    out['p'] = meet((1, 0), 0.0, *L[t - d]['d'])            # d(t - δ) ∩ b(t)
    out['p2'] = meet((1, 0), 0.0, *L[t + d]['d'])           # d(t + δ) ∩ b(t)
    out['q'] = meet((0, 1), 0.0, *L[t - d]['d'])            # d(t - δ) ∩ d(t)
    out['r'] = meet((0, 1), 1.0, *L[t - d]['c'])            # c(t - δ) ∩ c(t)
    out['Bm'] = meet((1, 0), 0.0, *L[t - d]['b'])           # b(t - δ) ∩ b(t)
    out['Bp'] = meet((1, 0), 0.0, *L[t + d]['b'])           # b(t + δ) ∩ b(t)
    # The vertex C⁻(t) = v⁻(t + π/2) of the polygon cap is r, and the arm g⁻(t) = ⟨y - r, u_t⟩.
    r_sofa = from_frame(t, out['r'])
    assert norm(sub(r_sofa, body.vminus(t + PI / 2, tol=1e-7))) < 1e-7
    g_minus = 1 - out['r'][0]
    C_plus = body.vplus(t + PI / 2, tol=1e-7)
    g_plus = 1 - place_frame(t, C_plus)[0]
    out['g_minus'], out['g_plus'] = g_minus, g_plus
    # Lemma 7.13 (1), (2).
    alpha1 = -out['p'][1]
    assert abs(alpha1 - math.tan(d) * max(0.0, g_minus - 1 + math.tan(d / 2))) < 1e-9
    assert 1 - g_plus + math.tan(d / 2) < 0 and out['p2'][1] > 0
    assert abs(out['r'][0] - out['q'][0] - math.tan(d / 2)) < 1e-9 and abs(out['r'][1] - 1) < 1e-12
    # σ_K(t), the length of the edge with normal angle t, and the segment b(t) ∩ S.
    sigma_t = dot(sub(body.vplus(t, tol=1e-7), body.vminus(t, tol=1e-7)), vvec(t))
    out['sigma_t'] = sigma_t
    assert abs((out['Bm'][1] - out['Bp'][1]) - (2 * math.tan(d / 2) - sigma_t)) < 1e-9
    assert out['Bm'][1] > out['Bp'][1]
    # The niche side X on b⃗(t): the points (0, Y), Y <= 0, above y = 0 and outside the open
    # quadrants Q⁻(t ± δ). It is [p, x(t)] ∪ [B₊, B₋], inside R ∪ S.
    Ys = np.linspace(-1.3, 0.0, 26001)

    def in_Q(s, Y):
        (nb, cb), (nd, cd) = L[s]['b'], L[s]['d']
        return nb[1] * Y < cb and nd[1] * Y < cd

    above = [from_frame(t, (0.0, Y))[1] >= 0 for Y in Ys]
    X = [Y for Y, ok in zip(Ys, above) if ok and not in_Q(t - d, Y) and not in_Q(t + d, Y)]
    X = np.array(X)
    top = X[X >= out['Bm'][1] + 1e-6]
    low = X[X <= out['Bm'][1] + 1e-6]
    assert abs(top.min() - out['p'][1]) < 1e-4 and abs(top.max()) < 1e-12
    assert abs(low.max() - out['Bm'][1]) < 1e-4 and abs(low.min() - out['Bp'][1]) < 1e-4
    out['X'] = (top.min(), low.min(), low.max())
    # The numbers of the captions of Figures 7.4 and 7.6.
    assert abs(g_minus - 1.680) < 5e-4 and abs(alpha1 - 0.364) < 5e-4
    assert abs(sigma_t - 0.352) < 5e-4 and abs(out['Bm'][1] - out['Bp'][1] - 0.046) < 5e-4
    return out


def frame_box_line(f, line, box, **kw):
    seg = line_in_box(line[0], line[1], box)
    if seg:
        f.line(seg[0], seg[1], **kw)


def draw_frame_cap(f, data, box):
    """The polygon cap in the frame of L_t, clipped to the box."""
    P = [place_frame(T_MID, p) for p in data['P']]
    f.polygon(clip_box(P, box), fill=FILLS[0], stroke=BLUE, width=1.4, opacity=0.45)


def fig_leg_computation():
    """Lemma 7.13 (1): the part of b⃗(t) above d(t - δ) has length tan δ (g⁻(t) - 1 + tan(δ/2))."""
    data = polygon_cap_data()
    t, d = T_MID, DELTA
    box = (-1.5, 1.45, -0.62, 1.42)
    f = Figure(*box, 175)
    big = 5.0
    floor = [(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)]
    f.polygon(clip_box(floor, box), fill=FLOOR, stroke='none', width=0)
    draw_frame_cap(f, data, box)
    f.polyline([(box[0], 1), (1, 1), (1, box[2])], stroke=WALL, width=2.4)
    f.polyline([(box[0], 0), (0, 0), (0, box[2])], stroke=WALL, width=2.4)
    L = data['L'][t - d]
    frame_box_line(f, L['c'], box, stroke=PURPLE, width=1.4, dash='6 4')
    frame_box_line(f, L['d'], box, stroke=PURPLE, width=1.4, dash='6 4')
    p, q, r = data['p'], data['q'], data['r']
    f.polygon([p, q, (0, 0)], fill=FILLS[1], stroke='none', width=0, opacity=0.9)
    f.line(p, (0, 0), stroke=ORANGE, width=4.0)
    right_angle(f, (0, 0), (-1, 0), (0, -1), size=0.07)
    # The arm g⁻(t) from r = C⁻(t) to y(t) along c(t).
    f.line(r, (1, 1), stroke=GREEN, width=4.0)
    f.text(add(lerp(r, (1, 1), 0.55), (0, 0.13)), 'g⁻(t)', size=15, color=GREEN)
    for pt, name, off in ((p, 'p', (0.13, -0.02)), (q, 'q', (-0.03, 0.13)),
                          (r, 'r = C⁻(t)', (-0.1, 0.15)), ((0, 0), 'x(t)', (0.2, 0.1)),
                          ((1, 1), 'y(t)', (0.17, 0.12))):
        f.dot(pt, r=3.8, fill=INK)
        f.text(add(pt, off), name, size=15)
    # The angle δ at q.
    arc = [add(q, mul(0.32, uvec(s))) for s in np.linspace(-d, 0, 20)]
    f.polyline(arc, stroke=INK, width=1.0)
    f.text(add(q, mul(0.45, uvec(-d / 2))), 'δ', size=15)
    f.text((0.08, -0.55), 'b(t)', size=14, color=WALL, anchor='start')
    f.text((-1.15, 0.13), 'd(t)', size=14, color=WALL)
    f.text((-1.15, 1.13), 'c(t)', size=14, color=WALL)
    f.text((1.08, 0.75), 'a(t)', size=14, color=WALL, anchor='start')
    ends = line_in_box(L['d'][0], L['d'][1], box)
    left = min(ends, key=lambda e: e[0])
    f.text(add(left, (0.12, 0.14)), 'd(t − δ)', size=14, color=PURPLE, anchor='start')
    f.text((1.08, 0.36), 'c(t − δ)', size=14, color=PURPLE, anchor='start')
    f.text((-1.25, 0.72), 'K', size=18, color=BLUE)
    return f.save(f'{CH7}/leg-computation',
                  'The supporting hallway L(t) of a polygon cap drawn upright, with the walls '
                  'c(t - δ) and d(t - δ) of the hallway at the previous angle, dashed. The line '
                  'd(t - δ) meets the inner wall b(t) at p and the wall d(t) at q, and c(t - δ) meets '
                  'c(t) at the vertex r = C⁻(t). The segment from p to the corner x(t) is the part '
                  'of the inner wall above d(t - δ); it is the side of the right triangle p q x(t) '
                  'opposite to the angle δ at q')


def fig_discrete_inequality():
    """Theorem 7.15: the niche side X on b⃗(t) lies in R ∪ S."""
    data = polygon_cap_data()
    t, d = T_MID, DELTA
    box = (-1.5, 1.35, -1.15, 1.12)
    f = Figure(*box, 175)
    big = 5.0
    floor = [(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)]
    f.polygon(clip_box(floor, box), fill=FLOOR, stroke='none', width=0)
    P = [place_frame(t, p) for p in data['P']]
    f.polygon(clip_box(P, box), fill=FILLS[0], stroke='none', width=0, opacity=0.6)
    # The polygon niche: the open quadrants Q⁻(s), s ∈ Θ_4, above the x-axis of the sofa's frame.
    for k in range(1, N_STEPS):
        s = k * DELTA
        x = xpath(s)
        quad = [x, add(x, mul(-big, uvec(s))), add(x, mul(-big, uvec(s)), mul(-big, vvec(s))),
                add(x, mul(-big, vvec(s)))]
        quad = clip_halfplane(quad, (0, -1), 0.0)
        f.polygon(clip_box([place_frame(t, p) for p in quad], box), fill='#fed7aa',
                  stroke='none', width=0)
    ground = [place_frame(t, (-5.0, 0.0)), place_frame(t, (5.0, 0.0))]
    seg = clip_segment(ground[0], ground[1], box)
    f.line(seg[0], seg[1], stroke=FAINT, width=1.2)
    f.polyline([(box[0], 1), (1, 1), (1, box[2])], stroke=WALL, width=2.4)
    f.polyline([(box[0], 0), (0, 0), (0, box[2])], stroke=WALL, width=2.4)
    for s, color in ((t - d, PURPLE), (t + d, GREEN)):
        frame_box_line(f, data['L'][s]['d'], box, stroke=color, width=1.3, dash='7 4')
        frame_box_line(f, data['L'][s]['b'], box, stroke=color, width=1.3, dash='2 3')
    p, Bm, Bp = data['p'], data['Bm'], data['Bp']
    f.line(p, (0, 0), stroke=ORANGE, width=5.0)
    f.line(Bp, Bm, stroke=ORANGE, width=5.0)
    for pt in (p, (0, 0), Bm, Bp):
        f.dot(pt, r=3.4, fill=INK)
    f.text(add(p, (0.12, 0.02)), 'p', size=15, anchor='start')
    f.text((0.17, 0.11), 'x(t)', size=15)
    f.text(add(Bm, (0.12, 0.07)), sb('B', '−'), size=15, anchor='start')
    f.text(add(Bp, (0.12, -0.08)), sb('B', '+'), size=15, anchor='start')
    f.text((-0.1, -0.18), 'in R', size=14, color=ORANGE, anchor='end', italic=False)
    f.text((-0.1, -0.86), 'in S', size=14, color=ORANGE, anchor='end', italic=False)
    f.text((-0.48, -0.4), sb('𝒩', 'Θ', '(K)'), size=15, color=ORANGE, italic=False)
    # Labels of the lines, next to their lower ends.
    for s, color, name in ((t - d, PURPLE, 't − δ'), (t + d, GREEN, 't + δ')):
        for key, off in (('d', (0.08, 0.13)), ('b', (0.08, -0.07))):
            ends = line_in_box(*data['L'][s][key], box)
            end = min(ends, key=lambda e: e[0]) if key == 'd' else max(ends, key=lambda e: e[1])
            f.text(add(end, off), f'{key}({name})', size=13, color=color, anchor='start')
    f.text((-0.06, -1.07), 'b(t)', size=14, color=WALL, anchor='end')
    f.text((-1.08, 0.12), 'd(t)', size=14, color=WALL)
    return f.save(f'{CH7}/discrete-inequality',
                  'The supporting hallway L(t) of the polygon cap drawn upright, with the polygon '
                  'niche shaded orange. Near the corner x(t), the inner wall b(t) runs above the line '
                  'd(t - δ) down to p: that part lies in R. Further down it crosses the quadrant '
                  'Q⁻(t - δ), and then runs between the lines b(t - δ) and b(t + δ) from B₋ to B₊: '
                  'that part lies in S. The side of the niche on b(t), thick, is the union of the '
                  'two parts')


# ----------------------------------------------------------------- k₀, m₀ and the bounds f_n

def k0(x):
    return np.maximum(np.abs(x - 1), (np.abs(x - 1) + 1) / 2)


def m0(x):
    return x - k0(x)


def fig_k0_m0():
    """The functions k₀ and m₀ of Definition 7.14."""
    xs = np.linspace(0, 3, 601)
    K0, M0 = k0(xs), m0(xs)
    # m₀ is 3x/2 - 1 on [0, 1], x/2 on [1, 2], 1 on [2, ∞); k₀ is 1-Lipschitz.
    for x, m in zip(xs, M0):
        expect = 1.5 * x - 1 if x <= 1 else (x / 2 if x <= 2 else 1.0)
        assert abs(m - expect) < 1e-12
    assert np.all(np.abs(np.diff(K0)) <= np.diff(xs) + 1e-12)
    assert abs(m0(np.array([2 / 3]))[0]) < 1e-12 and abs(m0(np.array([0.75]))[0] - 0.125) < 1e-12
    f = Figure(-0.75, 7.9, -0.55, 5.3, 62)
    P = Plot(f, (0.0, 0.25), 6.8, 4.6, 0, 3, -1.2, 2.2)
    P.grid([-1, 0, 1, 2])
    P.curve(xs, K0, stroke=PURPLE, width=2.4)
    P.curve(xs, M0, stroke=ORANGE, width=2.4)
    P.curve(xs[xs <= 2.2], xs[xs <= 2.2], stroke=FAINT, width=1.2, dash='5 4')
    P.axes([(0, '0'), (2 / 3, '2/3'), (1, '1'), (2, '2'), (3, '3')],
           [(-1, '−1'), (0, '0'), (0.5, '1/2'), (1, '1'), (2, '2')], xlabel='x')
    for x, y in ((0, -1), (1, 0.5), (2, 1), (2 / 3, 0)):
        f.dot(P.p(x, y), r=3.4, fill=ORANGE)
    f.dot(P.p(1, 0.5), r=3.4, fill=PURPLE)
    f.text(add(P.p(2.55, k0(np.array([2.55]))[0]), (-0.25, 0.25)), sb('k', '0', '(x)'), size=16,
           color=PURPLE)
    f.text(add(P.p(2.55, 1.0), (0.0, -0.25)), sb('m', '0', '(x)'), size=16, color=ORANGE)
    f.text(add(P.p(2.2, 2.2), (0.15, 0.0)), 'x', size=15, color=FAINT, anchor='start')
    return f.save(f'{CH7}/k0-m0',
                  'The graphs of k₀(x) = max(|x - 1|, (|x - 1| + 1)/2) and m₀(x) = x - k₀(x) for x '
                  'from 0 to 3, with the diagonal x dashed. The function m₀ is nondecreasing and '
                  'piecewise linear, through (0, -1), (2/3, 0), (1, 1/2) and (2, 1), and constant '
                  'after 2; k₀ has its minimum 1/2 at x = 1')


def lower_bounds(n_max=11, N=200000):
    """f_0, ..., f_{n_max} on a uniform grid of [0, π/2] (Definition 7.24)."""
    x = np.linspace(0, PI / 2, N + 1)
    fs = [np.zeros_like(x)]
    for _ in range(n_max):
        g = m0(fs[-1][::-1])  # m₀(f(π/2 - u)) on the grid of u
        F = 1 + np.concatenate([[0.0], np.cumsum((g[1:] + g[:-1]) / 2 * np.diff(x))])
        fs.append(np.maximum(fs[-1], F))
    return x, fs


def fig_lower_bounds():
    """The lower bounds f_n and the arm length of Gerver's sofa."""
    x, fs = lower_bounds()
    first = None
    for n, fn in enumerate(fs):
        if first is None and np.all(fn[x >= 1e-3] > 1):
            first = n
    # f_m ≥ j_{(m-1)/12} for m ≤ 10 (Lemma 7.28), and f_11 > 1 on (0, π/2].
    for m in range(1, 11):
        assert np.all(fs[m] >= np.maximum(1 - x, (m - 1) / 12) - 1e-9), m
    assert np.all(fs[11][1:] > 1) and fs[10].min() >= 0.75 - 1e-9
    assert first == 6 and not np.all(fs[5][1:] > 1)
    assert abs(fs[11][-1] - 2.31) < 5e-3 and abs((1 - alpha(PI / 2)) - 2.42) < 5e-3
    # Gerver's arm length f(t) = 1 - ⟨𝐱'(t), u_t⟩ lies above every f_n.
    ts = np.linspace(0, PI / 2, 801)
    fG = np.array([1 - alpha(t) for t in ts])
    for fn in fs:
        assert np.all(np.interp(ts, x, fn) <= fG + 1e-6)
    f = Figure(-0.7, 8.6, -0.55, 5.6, 64)
    P = Plot(f, (0.0, 0.25), 7.4, 4.9, 0, PI / 2, 0, 2.6)
    P.grid([0.5, 1, 1.5, 2, 2.5])
    shades = np.linspace(0.25, 1.0, 11)
    sub_x = x[::500]
    for n in range(1, 12):
        c = shades[n - 1]
        color = '#%02x%02x%02x' % tuple(int(round(255 - c * (255 - v))) for v in (0xea, 0x58, 0x0c))
        P.curve(sub_x, fs[n][::500], stroke=color, width=2.6 if n in (6, 11) else 1.4)
    P.curve(ts, fG, stroke=BLUE, width=2.4)
    P.f.line(P.p(0, 1), P.p(PI / 2, 1), stroke=INK, width=1.0, dash='6 4')
    P.axes([(0, '0'), (PI / 8, 'π/8'), (PI / 4, 'π/4'), (3 * PI / 8, '3π/8'), (PI / 2, 'π/2')],
           [(0.5, '0.5'), (1, '1'), (1.5, '1.5'), (2, '2'), (2.5, '2.5')], xlabel='x')
    for n, (t, dy) in {1: (1.15, 0.12), 2: (1.33, 0.12), 3: (1.4, 0.13), 4: (1.43, 0.13),
                       5: (1.45, 0.13), 6: (1.25, 0.13)}.items():
        y = float(np.interp(t, x, fs[n]))
        f.text(add(P.p(t, y), (0, dy)), sb('f', str(n)), size=14, color=ORANGE)
    f.text(add(P.p(PI / 2, fs[11][-1]), (0.12, 0.0)), sb('f', '11'), size=14, color=ORANGE,
           anchor='start')
    f.text(add(P.p(1.2, float(np.interp(1.2, ts, fG))), (-0.2, 0.2)), "Gerver's f", size=14,
           color=BLUE, italic=False)
    return f.save(f'{CH7}/lower-bounds',
                  "The lower bounds f_1, ..., f_11 on [0, π/2], darker for larger n, the line at "
                  "height 1 dashed, and the arm length f(t) of Gerver's sofa in blue above them. "
                  "f_1 = max(1 - x, 0); each bound rises above the previous one; f_6 is the first "
                  "that exceeds 1 on all of (0, π/2]; f_6 and f_11 are drawn thick")


def main():
    check_gerver()
    sofa = gerver.outline(900, 20000)
    paths = [fig_notation(), fig_examples(), fig_gauss_minkowski(), fig_area_formula(),
             fig_weak_convergence(), fig_contacts(sofa), fig_rotation_path(), fig_arms(),
             fig_leg_computation(), fig_discrete_inequality(), fig_k0_m0(), fig_lower_bounds()]
    root = paths[0].parents[4]
    for p in paths:
        print(f'wrote {p.relative_to(root)} ({p.stat().st_size // 1024} KiB)')


if __name__ == '__main__':
    main()
