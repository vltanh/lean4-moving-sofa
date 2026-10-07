#!/usr/bin/env python3
"""The figures of Chapters 11 and 12, the uniqueness of Gerver's sofa, in
baek/proof/figures/11-selection/ and baek/proof/figures/12-uniqueness/.

    python3 scripts/figures/fig_uniqueness.py

Polygon caps are computed from their assigned heights, as intersections of half-planes
(Baek's Definition 3.3.3, `MovingSofaOptimality.capH`), and their niches from the inner quadrants
(`MovingSofaOptimality.nicheH`). Gerver's sofa, its cap and its rotation path come from gerver.py.
Every fact that a caption states is checked by an assertion.
"""
import math

import numpy as np

import gerver
from sofa_figures import Figure, INK, FAINT, COLORS, FILLS, sb

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
BLUE_F, ORANGE_F = FILLS[0], FILLS[1]


# ---- planar geometry --------------------------------------------------------------------------

def uvec(t):
    return (math.cos(t), math.sin(t))


def vvec(t):
    return (-math.sin(t), math.cos(t))


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def mul(c, p):
    return (c * p[0], c * p[1])


def norm(p):
    return math.hypot(p[0], p[1])


def clip(poly, n, c):
    """The part of the convex polygon `poly` where <p, n> <= c (Sutherland–Hodgman)."""
    out = []
    for i, p in enumerate(poly):
        q = poly[(i + 1) % len(poly)]
        fp, fq = dot(p, n) - c, dot(q, n) - c
        if fp <= 0:
            out.append(p)
        if fp * fq < 0:
            s = fp / (fp - fq)
            out.append((p[0] + s * (q[0] - p[0]), p[1] + s * (q[1] - p[1])))
    return out


def halfplanes(cons, big=60.0):
    """The convex polygon of the points p with <p, n> <= c for every (n, c), counterclockwise."""
    poly = [(-big, -big), (big, -big), (big, big), (-big, big)]
    for n, c in cons:
        poly = clip(poly, n, c)
    return poly


def support(poly, t):
    return max(dot(p, uvec(t)) for p in poly)


def area(poly):
    return 0.5 * sum(p[0] * q[1] - q[0] * p[1] for p, q in zip(poly, poly[1:] + poly[:1]))


def inside(poly, p, tol=1e-9):
    """Whether p lies in the counterclockwise convex polygon `poly`."""
    for a, b in zip(poly, poly[1:] + poly[:1]):
        if (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0]) < -tol:
            return False
    return True


def edge_length(poly, t, tol=1e-7):
    """sigma({t}): the total length of the edges of `poly` with outward normal u_t."""
    total = 0.0
    for a, b in zip(poly, poly[1:] + poly[:1]):
        d = sub(b, a)
        if norm(d) < 1e-12:
            continue
        n = (d[1] / norm(d), -d[0] / norm(d))
        if abs(n[0] - math.cos(t)) < tol and abs(n[1] - math.sin(t)) < tol:
            total += norm(d)
    return total


def hull(points):
    """The convex hull of `points`, counterclockwise (monotone chain)."""
    pts = sorted(set(points))

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def parallelogram(omega):
    """P_ω = H ∩ V_ω, counterclockwise from O."""
    c = (1 - math.sin(omega)) / math.cos(omega)
    return [(0.0, 0.0), (1 / math.cos(omega), 0.0), (c, 1.0), (-math.tan(omega), 1.0)]


def c_omega(omega):
    """c_ω = sec ω - tan ω, the abscissa of o_ω (Baek's Proposition 4.2.1)."""
    return (1 - math.sin(omega)) / math.cos(omega)


# ---- polygon caps from assigned heights -------------------------------------------------------

class Heights:
    """Assigned heights h on Θ^◇ = Θ ∪ (Θ + π/2) ∪ {ω, π/2} (Baek's Definition 3.3.2)."""

    def __init__(self, omega, thetas, h):
        self.omega, self.thetas = omega, list(thetas)
        self.floating = self.thetas + [t + PI / 2 for t in self.thetas]
        self.h = {s: h(s) for s in self.floating}
        self.h_omega = h(omega)
        self.h_top = h(PI / 2)

    def raised(self, s, eps):
        """The heights raised by eps at the normal s (s floating, or 'omega', or 'top')."""
        new = Heights.__new__(Heights)
        new.omega, new.thetas, new.floating = self.omega, self.thetas, self.floating
        new.h, new.h_omega, new.h_top = dict(self.h), self.h_omega, self.h_top
        if s == 'omega':
            new.h_omega += eps
        elif s == 'top':
            new.h_top += eps
        else:
            new.h[s] += eps
        return new

    def cap(self):
        """C_Θ(h): the half-planes H₋(s, h(s)) for s ∈ Θ^◇ and the two strips (`capH`)."""
        w = self.omega
        cons = [(uvec(s), self.h[s]) for s in self.floating]
        cons += [(uvec(w), self.h_omega), (mul(-1, uvec(w)), 1 - self.h_omega),
                 (uvec(PI / 2), self.h_top), (mul(-1, uvec(PI / 2)), 1 - self.h_top)]
        return halfplanes(cons)

    def inner_lines(self):
        """For t ∈ Θ, the two inner walls b(t), d(t) as y < m x + k (t ∈ (0, π/2))."""
        out = []
        for t in self.thetas:
            s, c = math.sin(t), math.cos(t)
            a = (-c / s, (self.h[t] - 1) / s, ('b', t))
            b = (s / c, (self.h[t + PI / 2] - 1) / c, ('d', t))
            out.append((a, b))
        return out

    def floor_lines(self):
        """The fan F_h: y >= m x + k for both lines."""
        w = self.omega
        lines = [(0.0, self.h_top - 1, 'floor')]
        if w < PI / 2 - 1e-12:
            lines.append((-math.cos(w) / math.sin(w), (self.h_omega - 1) / math.sin(w), 'side'))
        return lines

    def niche(self, xlo=-20.0, xhi=20.0):
        """N_Θ(h) as a polygon (its closure), with the line that bounds each upper edge.

        Every vertical line meets F_h ∩ Q⁻(t) in an interval [lower(x), min(b_t, d_t)), so the
        niche is the region lower(x) <= y < roof(x), roof = max_t min(b_t(x), d_t(x)).
        """
        pairs = self.inner_lines()
        lows = self.floor_lines()
        allines = [l for pr in pairs for l in pr] + lows
        xs = {xlo, xhi}
        for i, (m1, k1, _) in enumerate(allines):
            for m2, k2, _ in allines[i + 1:]:
                if abs(m1 - m2) > 1e-14:
                    x = (k2 - k1) / (m1 - m2)
                    if xlo < x < xhi:
                        xs.add(x)
        xs = sorted(xs)

        def roof(x):
            best, tag = -math.inf, None
            for a, b in pairs:
                va, vb = a[0] * x + a[1], b[0] * x + b[1]
                v, tg = (va, a[2]) if va <= vb else (vb, b[2])
                if v > best:
                    best, tag = v, tg
            return best, tag

        def lower(x):
            return max(m * x + k for m, k, _ in lows)

        top, bot, edges = [], [], []
        for x0, x1 in zip(xs, xs[1:]):
            xm = 0.5 * (x0 + x1)
            r, tag = roof(xm)
            if r > lower(xm) + 1e-12:
                p0, p1 = (x0, roof(x0)[0]), (x1, roof(x1)[0])
                top.append(p0)
                top.append(p1)
                bot.append((x0, lower(x0)))
                bot.append((x1, lower(x1)))
                edges.append((p0, p1, tag))
        assert edges, 'empty niche'
        # The niche is one region: its x-range is an interval.
        poly = []
        for p in bot + top[::-1]:
            if not poly or norm(sub(p, poly[-1])) > 1e-12:
                poly.append(p)
        return poly, edges

    def tau(self, edges, kind, t):
        """τ: the length of the niche's upper boundary on the wall b(t) or d(t)."""
        return sum(norm(sub(p1, p0)) for p0, p1, tag in edges if tag == (kind, t))


def mirror(omega, p):
    """Baek's reflection M_ω across the line through O and o_ω (`MovingSofaOptimality.mirror`)."""
    c, s = math.cos(PI / 2 + omega), math.sin(PI / 2 + omega)
    return (c * p[0] + s * p[1], s * p[0] - c * p[1])


def example_cap(omega=1.0, rho=0.55, n=4):
    """A polygon cap of the uniform angle set Θ_{ω,n}: the polygon C_Θ(K₀) circumscribed about a cap
    K₀, the convex hull of O, o_ω, an arc of radius ρ with normals in [0, ω] that touches the floor
    and the right side of P_ω, and the mirror image of that arc."""
    centre = ((1 - rho) / math.cos(omega), 0.0)
    arc = [add(centre, mul(rho, uvec(omega * i / 200))) for i in range(201)]
    k0 = hull([(0.0, 0.0), (c_omega(omega), 1.0)] + arc + [mirror(omega, p) for p in arc])
    thetas = [i * omega / n for i in range(1, n)]
    H = Heights(omega, thetas, lambda s: support(k0, s))
    K = H.cap()
    for s in H.floating:
        assert edge_length(K, s) > 0.08, (s, edge_length(K, s))
    # K is a cap: it touches the four lines of the two strips.
    for s, val in ((omega, 1), (PI / 2, 1), (omega + PI, 0), (3 * PI / 2, 0)):
        assert abs(support(K, s) - val) < 1e-9, (s, support(K, s))
    return H, K


# ---- Chapter 11 -------------------------------------------------------------------------------

def toy_selection():
    """Note 03's example: exact maximizers of F_n = x/n stay at 1; penalized ones converge."""
    xs_star = 0.3
    ns = (1, 2, 4, 8)
    gap = 1.45
    f = Figure(-0.12, 1 + gap + 0.3, -0.42, 1.2, 230)
    shades = ['#fdba74', '#fb923c', '#ea580c', '#9a3412']
    greys = ['#d1d5db', '#9ca3af', '#6b7280', '#374151']
    for panel in (0, 1):
        ox = panel * gap
        f.line((ox, 0), (ox + 1.06, 0), stroke=INK, width=1.1, arrow=True)
        f.line((ox, -0.4), (ox, 1.15), stroke=INK, width=1.1, arrow=True)
        f.text((ox + 1.09, -0.06), 'x', size=15, anchor='start')
        f.line((ox + 1, -0.025), (ox + 1, 0.025), stroke=INK, width=1.1)
        f.text((ox + 1, -0.09), '1', size=13, italic=False)
        f.text((ox - 0.03, -0.09), '0', size=13, italic=False, anchor='end')
        # F = 0 on [0, 1]: every point is a maximizer.
        f.line((ox, 0), (ox + 1, 0), stroke=BLUE, width=4)
    f.text((0.5, -0.09), 'F = 0', size=15, color=BLUE)
    xs = np.linspace(0, 1, 201)
    for k, n in enumerate(ns):
        f.line((0, 0), (1, 1 / n), stroke=greys[k], width=1.6)
        f.dot((1, 1 / n), r=4, fill=greys[k])
        f.text((1.03, 1 / n), sb('F', str(n)), size=14, anchor='start', color=greys[k])
        # The penalized objective F_n(x) - (x - x*)^2 and its maximizer x* + 1/(2n).
        ys = xs / n - (xs - xs_star) ** 2
        xm = xs[np.argmax(ys)]
        assert abs(xm - (xs_star + 1 / (2 * n))) < 0.006, (n, xm)
        f.polyline([(gap + x, y) for x, y in zip(xs, ys)], stroke=shades[k], width=1.8)
        xm = xs_star + 1 / (2 * n)
        f.dot((gap + xm, xm / n - (xm - xs_star) ** 2), r=4, fill=shades[k])
        yl = 1 / n - (1 - xs_star) ** 2 + (0.07 if n == 2 else 0)
        f.text((gap + 1.03, yl), sb('G', str(n)), size=14, anchor='start', color=shades[k])
    f.dot((gap + xs_star, 0), r=4.5, fill=BLUE)
    f.text((gap + xs_star, -0.1), 'x*', size=15, color=BLUE)
    f.line((gap + xs_star, 0), (gap + xs_star, 0.09), stroke=BLUE, width=1.2, dash='3 3')
    return f.save('11-selection/toy',
                  'Left: on the interval from 0 to 1, the zero function F and the increasing lines '
                  'F_n(x) = x/n for n = 1, 2, 4, 8, each with its maximum only at x = 1. Right: '
                  'the penalized functions G_n(x) = F_n(x) - (x - x*)^2, whose maxima, marked by '
                  'dots, move towards the chosen maximizer x* = 0.3 of F')


def dyadic_level(omega, m):
    n = 2 ** (m + 1)
    return [i * omega / n for i in range(1, n)]


def level_weight(omega, m):
    """dyadicLevelWeight: (1/2)^(m+1) / (2 |Θ^(m)|)."""
    return 0.5 ** (m + 1) / (2 * len(dyadic_level(omega, m)))


def gerver_cap():
    """Gerver's cap C(G), the convex hull of Gerver's sofa."""
    return hull(gerver.outline(900, 9000))


def dyadic_samples(capG):
    """Gerver's cap with its supports sampled at the dyadic normals, and the sample weights."""
    w = PI / 2
    stage = 1
    thetas = dyadic_level(w, stage)
    H = Heights(w, thetas, lambda s: support(capG, s))
    rec = H.cap()
    # The recovery polygon has the supports of the cap at every sampled normal: penalty zero.
    for m in range(stage + 1):
        for t in dyadic_level(w, m):
            for s in (t, t + PI / 2):
                assert abs(support(rec, s) - support(capG, s)) < 1e-9
    # Total weights: level m carries (1/2)^(m+1); stage n carries 1 - (1/2)^(n+1).
    for n in range(6):
        tot = sum(2 * len(dyadic_level(w, m)) * level_weight(w, m) for m in range(n + 1))
        assert abs(tot - (1 - 0.5 ** (n + 1))) < 1e-12
    f = Figure(-2.75, 1.55, -2.55, 1.42, 150)
    f.polygon(capG, fill=BLUE_F, stroke=BLUE, width=1.8)
    f.polygon(rec, stroke=ORANGE, width=1.6, dash='6 4')
    f.text((-0.62, 0.45), 'C(G)', size=16, color=BLUE)
    # Outward normals at the contact points: level 0 thick, level 1 thin.
    for m, width, length in ((1, 1.3, 0.24), (0, 2.6, 0.34)):
        for t in dyadic_level(w, m):
            for s in (t, t + PI / 2):
                p = max(capG, key=lambda q: dot(q, uvec(s)))
                f.line(p, add(p, mul(length, uvec(s))), stroke=INK, width=width, arrow=True)
    pk = max(capG, key=lambda q: dot(q, uvec(PI / 4)))
    f.text(add(pk, (0.33, 0.22)), sb('u', 'π/4'), size=14, anchor='start')
    # The level diagram: the sampled normals of each level, on the axis of normal angles [0, π].
    x0, sx, y0 = -2.05, 2.9 / PI, -0.55
    f.line((x0, y0 - 1.75), (x0 + PI * sx, y0 - 1.75), stroke=INK, width=1.1)
    for s, lab in ((0, '0'), (PI / 4, 'π/4'), (PI / 2, 'π/2'), (3 * PI / 4, '3π/4'), (PI, 'π')):
        f.line((x0 + s * sx, y0 - 1.72), (x0 + s * sx, y0 - 1.78), stroke=INK, width=1.1)
        f.text((x0 + s * sx, y0 - 1.88), lab, size=13, italic=False)
    f.line((x0 + PI / 2 * sx, y0 + 0.08), (x0 + PI / 2 * sx, y0 - 1.72), stroke=FAINT, width=1,
           dash='3 3')
    radii = [6.5, 4.6, 3.3, 2.4]
    totals = ['1/2', '1/4', '1/8', '1/16']
    for m in range(4):
        y = y0 - 0.4 * m
        for t in dyadic_level(w, m):
            for s in (t, t + PI / 2):
                f.dot((x0 + s * sx, y), r=radii[m], fill=BLUE if m == 0 else INK)
        f.text((x0 - 0.12, y), f'm = {m}', size=13, anchor='end', italic=False)
        f.text((x0 + PI * sx + 0.12, y), 'total ' + totals[m], size=13, anchor='start',
               italic=False)
    return f.save('11-selection/samples',
                  "Top: Gerver's cap C(G), the outward normals at which its support function is "
                  'sampled at levels 0 (thick) and 1 (thin), and the dashed polygon circumscribed '
                  'about the cap at these normals. Bottom: the sampled normals of levels 0 to 3 on '
                  'the axis of normal angles from 0 to pi, with dots that shrink with the weight; '
                  'the samples of level m have total weight one half to the power m + 1')


def draw_cap_and_niche(f, H, K, ox=0.0, label=True):
    shift = lambda poly: [(p[0] + ox, p[1]) for p in poly]
    para = parallelogram(H.omega)
    f.polygon(shift(para), stroke=FAINT, width=1.0, dash='4 3')
    f.polygon(shift(K), fill=BLUE_F, stroke=BLUE, width=1.6)
    N, edges = H.niche()
    f.polygon(shift(N), fill=ORANGE_F, stroke=ORANGE, width=1.4)
    if label:
        f.text((0.95 + ox, 0.72), 'K', size=16, color=BLUE)
    return N, edges


def moves(H, K):
    """A floating facet raised, and the strip of a pinned normal moved."""
    omega = H.omega
    t = omega / 2
    assert H.thetas == [t]
    eps = 0.12
    gap = 3.75
    f = Figure(-1.75, 2.05 + gap, -0.42, 1.48, 150)
    # Floating move at t = ω/2.
    N, edges = draw_cap_and_niche(f, H, K)
    Hp = H.raised(t, eps)
    Kp = Hp.cap()
    Np, _ = Hp.niche()
    sig, tau = edge_length(K, t), H.tau(edges, 'b', t)
    assert sig > 0.1 and tau > 0.1, (sig, tau)
    # First variation (Baek's Lemma 3.4.7): |K⁺| - |K| ≈ σ ε and |N(h⁺)| - |N(h)| ≈ τ ε.
    small = 1e-3
    Hs = H.raised(t, small)
    dK = (area(Hs.cap()) - area(K)) / small
    dN = (area(Hs.niche()[0]) - area(N)) / small
    assert abs(dK - sig) < 0.01 and abs(dN - tau) < 0.01, (dK, sig, dN, tau)
    f.polygon(Kp, stroke=GREEN, width=1.6, dash='5 3')
    f.polygon(Np, stroke=PURPLE, width=1.4, dash='5 3')
    f.text((1.83, 0.38), 'K⁺', size=16, color=GREEN)
    # The facet of K with normal t, and the niche's side on the inner wall b(t).
    for a, b in zip(K, K[1:] + K[:1]):
        d = sub(b, a)
        if abs(d[1] / norm(d) - math.cos(t)) < 1e-7 and abs(-d[0] / norm(d) - math.sin(t)) < 1e-7:
            f.line(a, b, stroke=BLUE, width=4.5)
            mid = mul(0.5, add(a, b))
            f.line(mid, add(mid, mul(eps, uvec(t))), stroke=GREEN, width=1.6, arrow=True)
            f.text(add(mid, mul(-0.2, uvec(t))), sb('σ', 'K', '(t)'), size=15, color=BLUE)
            f.text(add(add(mid, mul(eps + 0.13, uvec(t))), (0.04, 0)), 'ε', size=15, color=GREEN)
    for p0, p1, tag in edges:
        if tag == ('b', t):
            f.line(p0, p1, stroke=ORANGE, width=4.5)
            mid = mul(0.5, add(p0, p1))
            f.text(add(mid, (0.28, 0.06)), sb('τ', 'K', '(t)'), size=15, color=ORANGE)
    f.text((0.12, -0.2), 'O', size=14)
    f.dot((0, 0), r=2.8)
    # Pinned move at π/2: both lines of the horizontal strip rise by ε.
    ox = gap
    draw_cap_and_niche(f, H, K, ox=ox, label=False)
    Hq = H.raised('top', eps)
    Kq = Hq.cap()
    Nq, _ = Hq.niche()
    f.polygon([(p[0] + ox, p[1]) for p in Kq], stroke=GREEN, width=1.6, dash='5 3')
    f.polygon([(p[0] + ox, p[1]) for p in Nq], stroke=PURPLE, width=1.4, dash='5 3')
    for y in (eps, 1 + eps):
        f.line((ox - 1.7, y), (ox + 2.0, y), stroke=GREEN, width=1.0, dash='2 3')
    sig_top = edge_length(K, PI / 2)
    assert sig_top > 0.1
    top = [p for p in K if abs(p[1] - 1) < 1e-9]
    f.line((min(top)[0] + ox, 1), (max(top)[0] + ox, 1), stroke=BLUE, width=4.5)
    f.text((ox + max(top)[0] + 0.12, 0.91), sb('σ', 'K', '(π/2)'), size=15, color=BLUE,
           anchor='start')
    f.text((ox - 1.05, 1.27), 'K′', size=16, color=GREEN)
    f.text((ox + 0.95, 0.72), 'K', size=16, color=BLUE)
    f.line((ox + 1.62, 1), (ox + 1.62, 1 + eps), stroke=GREEN, width=1.4, arrow=True)
    f.line((ox + 1.62, 0), (ox + 1.62, eps), stroke=GREEN, width=1.4, arrow=True)
    f.text((ox + 1.75, 1.08), 'ε', size=15, color=GREEN)
    f.text((ox + 1.75, 0.08), 'ε', size=15, color=GREEN)
    f.text((0.12 + ox, -0.2), 'O', size=14)
    f.dot((ox, 0), r=2.8)
    return f.save('11-selection/moves',
                  'Two copies of a polygon cap K with angle set {ω/2}, ω = 1, inside the '
                  'dashed parallelogram, with its polygon niche in orange. Left: the height at the '
                  'normal t = ω/2 is raised by ε; the cap gains a strip along its edge of length '
                  'sigma, and the niche a strip along its side of length tau on the inner wall. '
                  'Right: the height at π/2 is raised by ε, which moves both lines of the horizontal '
                  'strip up by ε; the new cap K′ and its niche are dashed')


def sandwich(H, K):
    """The pinned move: (1 - ε)K + ε o_ω ⊆ K' ⊆ (1 + ε)K."""
    omega = H.omega
    eps = 0.15
    o = (c_omega(omega), 1.0)
    Kp = H.raised('top', eps).cap()
    inner = [add(mul(1 - eps, p), mul(eps, o)) for p in K]
    outer = [mul(1 + eps, p) for p in K]
    for p in inner:
        assert inside(Kp, p), p
    for p in Kp:
        assert inside(outer, p), p
    f = Figure(-1.95, 3.55, -0.3, 1.3, 170)
    f.polygon(K, fill=BLUE_F, stroke=BLUE, width=1.4)
    f.polygon(outer, stroke=INK, width=1.3, dash='6 4')
    f.polygon(Kp, stroke=GREEN, width=2.0)
    f.polygon(inner, stroke=BLUE, width=1.4, dash='2 3')
    f.dot((0, 0), r=3.2)
    f.text((0.0, -0.15), 'O', size=15)
    f.dot(o, r=3.2)
    f.text((o[0] + 0.1, o[1] + 0.07), sb('o', 'ω'), size=15, anchor='start')
    # Legend.
    lx, ly = 2.45, 1.05
    items = [('K', dict(fill=BLUE_F, stroke=BLUE, width=1.4)),
             ('K′', dict(stroke=GREEN, width=2.0)),
             ('(1 + ε)K', dict(stroke=INK, width=1.3, dash='6 4')),
             ('(1 − ε)K + ε' + sb('o', 'ω'), dict(stroke=BLUE, width=1.4, dash='2 3'))]
    for k, (lab, style) in enumerate(items):
        y = ly - 0.28 * k
        f.polygon([(lx, y - 0.07), (lx + 0.32, y - 0.07), (lx + 0.32, y + 0.07), (lx, y + 0.07)],
                  **style)
        f.text((lx + 0.42, y), lab, size=15, anchor='start')
    return f.save('11-selection/sandwich',
                  "The pinned sandwich for ε = 0.15: the cap K (blue), the cap K' after the strip "
                  "at π/2 has moved up by ε (green), the smaller copy (1 - ε)K + ε o_ω (dotted), "
                  "which lies in K', and the larger copy (1 + ε)K (dashed), which contains K'")


def gap_figure(H, K):
    """w_K° ≤ τ_K(π/2): the part of the bottom edge outside every wedge."""
    omega = H.omega
    N, edges = H.niche()
    Ws = [((H.h[t] - 1) / math.cos(t), t) for t in H.thetas]
    wstar, tstar = max(Ws)
    A = support(K, 0)
    assert abs(edge_length(K, 3 * PI / 2) - A) < 1e-9          # the bottom edge is [O, A⁻(0)]
    floor_niche = max(p[0] for p in N if abs(p[1]) < 1e-12)
    assert abs(floor_niche - wstar) < 1e-9                    # the niche meets the floor in [O, W*)
    tau_top = A - wstar                                       # τ_K(π/2)
    # w_K(t) = A - W_K(t)_x over a fine grid of t ∈ (0, ω) stays above τ_K(π/2)... no: above w°.
    ts = np.linspace(1e-4, omega - 1e-4, 4001)
    winf = min(A - (support(K, t) - 1) / math.cos(t) for t in ts)
    assert winf <= tau_top + 1e-12
    f = Figure(-1.75, 2.05, -0.62, 1.15, 175)
    draw_cap_and_niche(f, H, K)
    for t in H.thetas:
        W = ((H.h[t] - 1) / math.cos(t), 0.0)
        f.dot(W, r=3.2, fill=ORANGE)
    f.text((wstar + 0.02, -0.15), 'W*', size=14, color=ORANGE)
    f.line((wstar, 0), (A, 0), stroke=GREEN, width=5)
    f.dot((A, 0), r=3.4)
    f.text((A + 0.05, -0.14), 'A', size=15, anchor='start')
    f.dot((0, 0), r=3.2)
    f.text((-0.02, -0.15), 'O', size=14, anchor='end')
    # Brace under the green segment.
    f.line((wstar, -0.33), (A, -0.33), stroke=GREEN, width=1.2)
    f.line((wstar, -0.3), (wstar, -0.36), stroke=GREEN, width=1.2)
    f.line((A, -0.3), (A, -0.36), stroke=GREEN, width=1.2)
    f.text((0.5 * (wstar + A), -0.46), 'τ(π/2) = w(t*)', size=14, color=GREEN)
    return f.save('11-selection/gap',
                  'A polygon cap K with angle set {ω/4, ω/2, 3ω/4}, ω = 1, with its polygon niche in '
                  'orange and the three wedge endpoints W_K(t) on the floor. The niche meets the '
                  'bottom edge of the cap, from O to the vertex A, in the segment from O to the '
                  'rightmost wedge endpoint W*; the rest of the edge, in green, has length tau_K(π/2) '
                  '= w_K(t*), which is at least the infimum of the wedge gaps w_K(t)')


# ---- Chapter 12 -------------------------------------------------------------------------------

def k0(x):
    """Baek's k₀(x) = max(|x - 1|, (|x - 1| + 1)/2) (Definition 6.3.4, `MovingSofaOptimality.k0`)."""
    return max(abs(x - 1), (abs(x - 1) + 1) / 2)


def m0(x):
    return x - k0(x)


def gerver_frame(t):
    """α, β with x'(t) = α u_t + β v_t for Romik's path, and α'(t), phase by phase.

    On each phase x(t) = R_t w(t) + κ, so x' = R_t (J w + w') with J(a, b) = (-b, a).
    """
    g = gerver
    c, s = math.cos(t), math.sin(t)
    if t < g.PHI:
        return (2 * g.a2 * c - 2 * g.a1 * s + 0.5, 2 * g.a1 * c + 2 * g.a2 * s - 1,
                -2 * g.a2 * s - 2 * g.a1 * c)
    if t < g.THETA:
        return -t + 2 * g.b1 + 1, -t * t / 4 + g.b1 * t + g.b2 + 0.5, -1.0
    if t <= PI / 2 - g.THETA:
        return -g.c2 - t - 1, g.c1 - t + 1, -1.0
    if t <= PI / 2 - g.PHI:
        return t * t / 4 - g.d1 * t - g.d2 - 0.5, -t + 2 * g.d1 - 1, t / 2 - g.d1
    return (2 * g.e2 * c - 2 * g.e1 * s + 1, 2 * g.e1 * c + 2 * g.e2 * s - 0.5,
            -2 * g.e2 * s - 2 * g.e1 * c)


def check_frame():
    """The phase formulas agree with numerical derivatives of `gerver.path`."""
    for t in np.linspace(0.01, PI / 2 - 0.01, 157):
        h = 1e-7
        p, q = gerver.path(t + h), gerver.path(t - h)
        d = ((p[0] - q[0]) / (2 * h), (p[1] - q[1]) / (2 * h))
        a, b, _ = gerver_frame(t)
        assert abs(dot(d, uvec(t)) - a) < 1e-6 and abs(dot(d, vvec(t)) - b) < 1e-6, t


def chain():
    """The containment chain of the proof of Theorem 12.1."""
    f = Figure(0, 4.65, 0, 6.15, 100)
    rows = [('S', 'a moving sofa with |S| = |G|'),
            ('S + ' + sb('v', '0') + ' ⊆ T', 'T monotone of angle ω, |T| = |G|, its cap maximizes ' +
             sb('A', 'ω')),
            (sb('R', 'a') + '(S + ' + sb('v', '0') + ') ⊆ ' + sb('R', 'a') + 'T',
             sb('R', 'a') + 'T moves with angle π/2'),
            (sb('g', '1') + '(S) ⊆ U = G + (b, 0)', 'U monotone of angle π/2, |U| = |G|'),
            ('g(S) = G', 'g(S) ⊆ G, |g(S)| = |G|, G is the closure of its interior')]
    arrows = ['translate by ' + sb('v', '0') + ', monotonize',
              'rotate by a (a = 0 if ω = π/2)',
              'translate by ' + sb('v', '1') + ', monotonize',
              'translate by (−b, 0)']
    top, h, step = 5.95, 0.72, 1.3
    for k, (head, note) in enumerate(rows):
        y1 = top - k * step
        y0 = y1 - h
        f.polygon([(0.15, y0), (4.1, y0), (4.1, y1), (0.15, y1)], fill=BLUE_F if k in (0, 4)
                  else '#ffffff', stroke=BLUE, width=1.4)
        f.text((0.32, y1 - 0.24), head, size=16, anchor='start')
        f.text((0.32, y1 - 0.53), note, size=12.5, anchor='start', color='#4b5563',
               italic=False)
        if k < len(arrows):
            f.line((2.1, y0 - 0.02), (2.1, y0 - step + h + 0.04), stroke=INK, width=1.4,
                   arrow=True)
            f.text((2.25, y0 - (step - h) / 2), arrows[k], size=13, anchor='start',
                   color=ORANGE, italic=False)
    return f.save('12-uniqueness/chain',
                  'The proof of the uniqueness theorem as a chain of five boxes: a moving sofa S '
                  'with the area of G; a translate of S inside its monotonization T; the rotated '
                  'copy inside R_a T, which moves with angle π/2; a rigid image of S inside the '
                  'monotonization U, which is a horizontal translate of G; and finally g(S) = G')


def curvature():
    """The curvature bound σ ≤ k₀(g(t)) dt for Gerver's cap, a maximizing cap."""
    g = gerver
    ts = np.linspace(0, PI / 2, 3001)[:-1]
    rows = []
    for t in ts:
        a, b, ap = gerver_frame(t)
        r = 1 + b + ap                      # ⟨A'(t), v_t⟩ with A = x + α v + u
        rows.append((t, r, k0(1 + b), b))
    for t, r, k, b in rows:
        assert r <= k + 1e-12, (t, r, k)
    # Equality exactly where Romik's phases give it: on [φ, t*] (β ≥ 1) and on [π/2 - θ, π/2 - φ].
    tstar = max(t for t, r, k, b in rows if g.PHI <= t < g.THETA and b >= 1)
    assert 0.61 < tstar < 0.62, tstar                                # g(t*) = 2 near t = 0.6165
    for t, r, k, b in rows:
        tight = (g.PHI <= t <= tstar) or (PI / 2 - g.THETA <= t <= PI / 2 - g.PHI)
        assert (abs(r - k) < 1e-9) == tight, (t, r, k)
    f = Figure(-0.12, PI / 2 + 0.25, -0.2, 1.62, 330)
    sy = 1.0
    f.line((0, 0), (PI / 2 + 0.12, 0), stroke=INK, width=1.1, arrow=True)
    f.line((0, 0), (0, 1.58), stroke=INK, width=1.1, arrow=True)
    for y in (0.5, 1.0, 1.5):
        f.line((-0.02, y), (0.02, y), stroke=INK, width=1.1)
        f.text((-0.04, y), f'{y:g}', size=12, anchor='end', italic=False)
    for t, lab, dx in ((g.PHI, sb('t', '1'), 0), (g.THETA, sb('t', '2'), 0),
                       (PI / 2 - g.THETA, sb('t', '3'), 0), (PI / 2 - g.PHI, sb('t', '4'), -0.025)):
        f.line((t, 0), (t, 1.5), stroke=FAINT, width=0.9, dash='3 3')
        f.text((t + dx, -0.09), lab, size=13)
    f.text((PI / 2 + 0.02, -0.19), 'π/2', size=13, italic=False)
    f.text((0, -0.09), '0', size=13, italic=False)
    f.text((PI / 2 + 0.16, 0.0), 't', size=15)
    drawn = rows[::6] + rows[-1:]
    upper = [(t, k) for t, r, k, b in drawn]
    lower = [(t, r) for t, r, k, b in drawn]
    f.polygon(upper + lower[::-1], fill=ORANGE_F, stroke='none', width=0)
    # Draw the density phase by phase: it jumps at t₁ and t₄.
    phases = [(0, g.PHI), (g.PHI, PI / 2 - g.THETA), (PI / 2 - g.THETA, PI / 2 - g.PHI),
              (PI / 2 - g.PHI, PI / 2)]
    for lo, hi in phases:
        seg = [(t, r) for t, r, k, b in rows if lo <= t < hi]
        f.polyline(seg[::6] + seg[-1:], stroke=BLUE, width=2.4)
    f.polyline(upper, stroke=ORANGE, width=1.8, dash='6 4')
    f.text((0.98, 0.98), 'k₀(g(t))', size=15, color=ORANGE, anchor='start')
    f.text((0.82, 0.7), 'r(t)', size=15, color=BLUE, anchor='start')
    return f.save('12-uniqueness/curvature',
                  "The curvature bound for Gerver's cap on the interval from 0 to π/2: the density "
                  'r(t) of its surface area measure (blue) lies below k₀(g(t)) (orange, dashed); '
                  'they agree on two intervals, from t₁ to about 0.62 and from t₃ to t₄, and the '
                  'gap between them is shaded')


def lower_sequence():
    """Baek's lower sequence f_n (Definition 6.5.2) and the arm f of Gerver's cap."""
    N = 6000
    x = np.linspace(0, PI / 2, N + 1)
    dx = x[1] - x[0]
    k0v = np.vectorize(k0)
    fs = [np.zeros_like(x)]
    for n in range(11):
        f_prev = fs[-1]
        integrand = f_prev[::-1] - k0v(f_prev[::-1])         # m₀(f_n(π/2 - u)) on the grid u = x
        cum = np.concatenate([[0.0], np.cumsum((integrand[1:] + integrand[:-1]) / 2 * dx)])
        fs.append(np.maximum(f_prev, 1 + cum))
    assert fs[11][1:].min() > 1 + 1e-4                           # Baek's Lemma 6.5.5: f₁₁ > 1
    fg = np.array([1 - gerver_frame(t)[0] for t in x])            # f = 1 - α (Proposition 6.4.6)
    assert np.all(fg >= fs[11] - 1e-6)                            # f_G ≥ f₁₁
    f = Figure(-0.15, PI / 2 + 0.3, -0.18, 2.62, 230)
    f.line((0, 0), (PI / 2 + 0.15, 0), stroke=INK, width=1.1, arrow=True)
    f.line((0, 0), (0, 2.6), stroke=INK, width=1.1, arrow=True)
    for y in (1.0, 2.0):
        f.line((-0.02, y), (0.02, y), stroke=INK, width=1.1)
        f.text((-0.04, y), f'{y:g}', size=12, anchor='end', italic=False)
    f.text((PI / 2, -0.09), 'π/2', size=13, italic=False)
    f.text((0, -0.09), '0', size=13, italic=False)
    f.text((PI / 2 + 0.2, 0.0), 't', size=15)
    f.line((0, 1), (PI / 2, 1), stroke=FAINT, width=1.1, dash='4 3')
    greys = np.linspace(0.82, 0.25, 11)
    step = 20
    for n in range(1, 12):
        col = '#%02x%02x%02x' % tuple(int(255 * g) for g in (greys[n - 1],) * 3)
        if n == 11:
            col = ORANGE
        pts = list(zip(x[::step], fs[n][::step]))
        f.polyline(pts, stroke=col, width=2.2 if n == 11 else 1.3)
    for n, (xl, dy) in {1: (0.62, 0.08), 3: (1.18, 0.09), 5: (1.33, 0.07)}.items():
        i = int(xl / (PI / 2) * N)
        f.text((xl, fs[n][i] + dy), sb('f', str(n)), size=14, color='#4b5563')
    f.text((PI / 2 + 0.03, fs[11][-1] - 0.05), sb('f', '11'), size=14, color=ORANGE,
           anchor='start')
    f.polyline(list(zip(x[::step], fg[::step])), stroke=BLUE, width=2.0, dash='6 4')
    f.text((PI / 2 + 0.03, fg[-1] + 0.05), 'f', size=15, color=BLUE, anchor='start')
    return f.save('12-uniqueness/lower-sequence',
                  "Baek's lower sequence f₁, ..., f₁₁ on the interval from 0 to π/2, rising from "
                  'light to dark grey, with f₁₁ in orange above the dashed line at height 1, and the '
                  "arm f of Gerver's cap (blue, dashed) above f₁₁")


def rotation():
    """Proposition 12.13: P_ω minus the triangle Δ has width at most one in the directions
    u_t, t ∈ [ω, π/2], so it can rotate by π/2 - ω inside the horizontal strip."""
    omega = 1.1
    beta = PI / 2 - omega
    c = c_omega(omega)
    para = parallelogram(omega)
    o = (c, 1.0)
    p1, p2 = mul(c, uvec(0)), mul(c, vvec(omega))
    assert norm(sub(p1, sub(o, vvec(0)))) < 1e-12 and norm(sub(p2, sub(o, uvec(omega)))) < 1e-12
    X = [p1, para[1], para[2], para[3], p2]                   # P_ω minus Δ, counterclockwise
    for t in np.linspace(omega, PI / 2, 401):
        w = max(dot(p, uvec(t)) for p in X) - min(dot(p, uvec(t)) for p in X)
        assert abs(w - max(math.sin(t), math.cos(t - omega))) < 1e-12 and w <= 1 + 1e-12
    rows = ((beta, GREEN, 'φ = β'), (beta / 2, PURPLE, 'φ = β/2'), (0.0, BLUE, 'φ = 0'))
    gap, top0 = 1.42, -0.45
    f = Figure(-2.4, 2.75, top0 - gap * len(rows) + 0.35, 1.22, 118)
    f.polygon(para, stroke=FAINT, width=1.1, dash='4 3')
    f.polygon(X, fill=BLUE_F, stroke=BLUE, width=1.6)
    f.polygon([(0, 0), p1, p2], fill=ORANGE_F, stroke=ORANGE, width=1.6)
    f.dot((0, 0), r=3)
    f.text((0.02, -0.15), 'O', size=14)
    f.dot(o, r=3)
    f.text((o[0] + 0.07, o[1] + 0.08), sb('o', 'ω'), size=14, anchor='start')
    f.text((-0.17, 0.3), 'Δ', size=15, color=ORANGE)
    f.text((0.85, 0.5), sb('P', 'ω') + ' ∖ Δ', size=15, color=BLUE)
    # Below: the pentagon rotated by φ = β, β/2, 0, each in a copy of the strip H.
    cx = sum(p[0] for p in X) / len(X)
    for k, (phi, col, lab) in enumerate(rows):
        y0 = top0 - gap * (k + 1) + 0.35
        f.polygon([(-2.35, y0), (2.2, y0), (2.2, y0 + 1), (-2.35, y0 + 1)], fill='#f3f4f6',
                  stroke='none', width=0)
        f.line((-2.35, y0), (2.2, y0), stroke=INK, width=1.1)
        f.line((-2.35, y0 + 1), (2.2, y0 + 1), stroke=INK, width=1.1)
        R = [(math.cos(phi) * (p[0] - cx) - math.sin(phi) * p[1],
              math.sin(phi) * (p[0] - cx) + math.cos(phi) * p[1]) for p in X]
        lo = min(q[1] for q in R)
        assert max(q[1] for q in R) - lo <= 1 + 1e-12
        if k == 1:
            # Rotated by β/2, the edge from c u_0 to c v_ω that Δ cut off is horizontal, at the bottom.
            assert abs(R[0][1] - lo) < 1e-12 and abs(R[4][1] - lo) < 1e-12
        f.polygon([(q[0], q[1] - lo + y0) for q in R], fill=FILLS[[2, 3, 0][k]], stroke=col,
                  width=1.6)
        f.text((2.3, y0 + 0.5), lab, size=14, anchor='start', color=col, italic=False)
    return f.save('12-uniqueness/rotation',
                  'Top: the parallelogram P_ω for ω = 1.1, dashed, with the small triangle Δ at its '
                  'corner O in orange, and the pentagon P_ω minus Δ in blue. Below: three copies of '
                  'the horizontal strip H of width one, holding the pentagon rotated by the angles '
                  'β = π/2 - ω, β/2 and 0')


def translation(capG):
    """Proposition 12.19: support functions that differ by a cos t on [0, π]."""
    g = gerver
    a = 0.55
    t = 0.65
    K2 = [(p[0] + a, p[1]) for p in capG]
    assert abs(support(K2, t) - support(capG, t) - a * math.cos(t)) < 1e-12
    f = Figure(-2.45, 1.85, -1.75, 1.5, 150)
    f.polygon(capG, fill=BLUE_F, stroke=BLUE, width=1.6)
    f.polygon(K2, stroke=GREEN, width=1.6, dash='6 4')
    f.text((-0.75, 0.45), 'C(G)', size=16, color=BLUE)
    f.text((0.3, 0.45), 'C(G) + (a, 0)', size=15, color=GREEN)
    # The supporting lines at the normal t, and the offset a cos t between them.
    for poly, col in ((capG, BLUE), (K2, GREEN)):
        q = max(poly, key=lambda p: dot(p, uvec(t)))
        f.line(add(q, mul(-0.45, vvec(t))), add(q, mul(0.62, vvec(t))), stroke=col, width=1.3,
               dash='4 3')
    q = max(capG, key=lambda p: dot(p, uvec(t)))
    q1 = add(q, mul(0.22, vvec(t)))
    q2 = add(q1, mul(a * math.cos(t), uvec(t)))
    f.line(q1, q2, stroke=INK, width=1.3, arrow=True)
    f.line(q2, q1, stroke=INK, width=1.3, arrow=True)
    f.text(add(mul(0.5, add(q1, q2)), (-0.12, 0.2)), 'a cos t', size=14, anchor='start')
    # Below: f(t) = a cos t on [0, π].
    y0, sx, sy = -1.15, 3.6 / PI, 0.8
    x0 = -2.2
    f.line((x0, y0), (x0 + PI * sx + 0.15, y0), stroke=INK, width=1.1, arrow=True)
    f.line((x0, y0 - 0.55), (x0, y0 + 0.55), stroke=INK, width=1.1)
    ts = np.linspace(0, PI, 300)
    f.polyline([(x0 + s_ * sx, y0 + sy * a * math.cos(s_)) for s_ in ts], stroke=ORANGE,
               width=2.4)
    for s_, lab in ((0, '0'), (PI / 2, 'π/2'), (PI, 'π')):
        f.line((x0 + s_ * sx, y0 - 0.03), (x0 + s_ * sx, y0 + 0.03), stroke=INK, width=1.1)
        f.text((x0 + s_ * sx + (0.06 if s_ == 0 else 0), y0 - 0.13), lab, size=13, italic=False)
    f.text((x0 + PI * sx + 0.2, y0), 't', size=15, anchor='start')
    f.text((x0 + 0.75, y0 + 0.38), 'f(t) = a cos t', size=15, anchor='start', color=ORANGE)
    return f.save('12-uniqueness/translation',
                  "Top: Gerver's cap C(G) and its horizontal translate by (a, 0), with their "
                  'supporting lines at one normal t, which lie a cos t apart. Bottom: the difference '
                  'f(t) = a cos t of the two support functions on the interval from 0 to π')


def envelope():
    """The envelope Γ = D ∪ x ∪ B of the inner corner of Gerver's sofa."""
    g = gerver
    D = [sub(g.path(t), mul(gerver_frame(t)[1], uvec(t))) for t in np.linspace(0, g.THETA, 200)]
    X = [g.path(t) for t in np.linspace(PI / 2 - g.PHI, g.PHI, 600)]
    B = [add(g.path(t), mul(gerver_frame(t)[0], vvec(t)))
         for t in np.linspace(PI / 2 - g.THETA, PI / 2, 200)]
    # The contact conditions: D(θ) = x(π/2 - φ) and B(π/2 - θ) = x(φ).
    assert norm(sub(D[-1], X[0])) < 1e-9 and norm(sub(B[0], X[-1])) < 1e-9
    return D, X, B


def regular_closed():
    """Proposition 12.24: G is the closure of its interior."""
    g = gerver
    D, X, B = envelope()
    gamma = D + X + B
    a, b = D[0][0], B[-1][0]
    assert abs(D[0][1]) < 1e-9 and abs(B[-1][1]) < 1e-9 and a < b
    hmax = max(p[1] for p in gamma)
    ts = np.linspace(0, PI / 2, 20001)
    hpath = max(g.path(t)[1] for t in ts)
    assert abs(hmax - hpath) < 1e-5 and hpath < 0.67
    # The bottom of Gerver's sofa over [a, b] is the envelope: the niche is the region under Γ.
    xs = np.linspace(a + 0.01, b - 0.01, 60)
    _, bottom, _ = g.bounds(xs, 20000)
    gx = np.array([p[0] for p in gamma])
    gy = np.array([p[1] for p in gamma])
    order = np.argsort(gx)
    env = np.interp(xs, gx[order], gy[order])
    assert np.max(np.abs(bottom - env)) < 2e-3, np.max(np.abs(bottom - env))
    pts = g.outline(900, 9000)
    capG = hull(pts)
    for corner in ((a, 0), (b, 0), (a, 1), (b, 1)):
        assert inside(capG, corner, tol=1e-6), corner
    f = Figure(-2.35, 1.2, -0.3, 1.22, 175)
    f.polygon(pts, fill=BLUE_F, stroke=BLUE, width=1.8)
    f.polygon([(a, 0), (b, 0), (b, 1), (a, 1)], stroke=INK, width=1.1, dash='5 4')
    f.polyline(gamma, stroke=ORANGE, width=2.4)
    f.line((-2.3, 1), (1.15, 1), stroke=FAINT, width=1.0, dash='3 3')
    f.line((a - 0.15, hmax), (b + 0.15, hmax), stroke=ORANGE, width=1.0, dash='2 3')
    f.text((b + 0.18, hmax), f'{hmax:.3f}', size=12, anchor='start', color=ORANGE, italic=False)
    f.text((1.17, 1), '1', size=12, anchor='start', color=FAINT, italic=False)
    f.dot((a, 1), r=3.2)
    f.dot((b, 1), r=3.2)
    f.text((a, 1.1), '(a, 1)', size=13, italic=False)
    f.text((b, 1.1), '(b, 1)', size=13, italic=False)
    f.text((a, -0.13), 'a', size=14)
    f.text((b, -0.13), 'b', size=14)
    f.text((-0.65, 0.48), 'Γ', size=16, color=ORANGE)
    # A point of Γ and the interior points above it.
    p = g.path(1.05)
    f.dot(p, r=3.2, fill=INK)
    f.line(p, (p[0], p[1] + 0.22), stroke=INK, width=1.4, arrow=True)
    f.text((p[0] + 0.05, p[1] - 0.06), 'p', size=15, anchor='start')
    f.text((-1.95, 0.48), 'G', size=17, color=BLUE)
    return f.save('12-uniqueness/regular-closed',
                  "Gerver's sofa G in blue. Its niche is the region strictly under the orange curve "
                  'Γ, made of the curves D and B and the rotation path between them; Γ stays below '
                  'height 0.665, under the dashed line at height one, and the dashed rectangle from '
                  'a to b lies in the cap. Every point p of Γ is the limit of the interior points '
                  'just above it')


def recovery():
    """A set with a hair, and a closed subset of G that misses a disk."""
    f = Figure(-0.25, 6.35, -0.35, 1.25, 120)
    f.polygon([(0, 0), (1, 0), (1, 1), (0, 1)], fill=BLUE_F, stroke=BLUE, width=1.6)
    f.line((1, 0), (2, 0), stroke=BLUE, width=3.2)
    f.text((0.5, 0.5), 'E', size=17, color=BLUE)
    f.text((1.5, 0.15), 'hair', size=13, color=BLUE, italic=False)
    ox = 4.55
    pts = gerver.outline(700, 6000)
    f.polygon([(p[0] + ox, p[1]) for p in pts], fill=BLUE_F, stroke=BLUE, width=1.6)
    q, r = (-1.75 + ox, 0.5), 0.17
    f.circle(q, r, stroke=ORANGE, width=1.6, dash='4 3', fill='#ffffff')
    f.dot(q, r=3, fill=ORANGE)
    f.text((q[0] + 0.05, q[1] - 0.06), 'q', size=14, color=ORANGE, anchor='start')
    f.text((0.2 + ox, 0.75), 'G', size=17, color=BLUE)
    return f.save('12-uniqueness/recovery',
                  'Left: the unit square E with a segment of length one attached, a closed connected '
                  'set with the area of E that is not E. Right: Gerver\'s sofa with a small open disk '
                  'about an interior point q removed, a closed subset of G of smaller area')


# ---- main -------------------------------------------------------------------------------------

def main():
    H1, K1 = example_cap(n=2)
    H, K = example_cap(n=4)
    capG = gerver_cap()
    check_frame()
    paths = [toy_selection(), dyadic_samples(capG), moves(H1, K1), sandwich(H, K),
             gap_figure(H, K), chain(), curvature(), lower_sequence(), rotation(),
             translation(capG), regular_closed(), recovery()]
    for p in paths:
        print(f'wrote {p}')


if __name__ == '__main__':
    main()
