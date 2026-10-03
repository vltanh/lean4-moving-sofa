#!/usr/bin/env python3
"""The figures of Chapter 10 (Gerver's sofa) and Appendix B (rigorous numerics), in
docs/proof/figures/10-gerver/ and docs/proof/figures/appendix-b/.

    python3 scripts/figures/fig_gerver.py

Every figure is computed from the definitions of `MovingSofaOptimality/Gerver/`: Romik's five phases
`x_i(t) = R_t (w₁(t), w₂(t)) + κ_i` (`GerverParams.x₁`, ..., `x₅`), written in the rotating frame of
`MovingSofaOptimality/Gerver/Frame.lean` (`gs_ph1`, ..., `gs_ph5`), with the parameters of gerver.py;
the contact curves `𝐀 = R_t (w₁ + 1, w₁') + κ`, `𝐁 = R_t (w₁, w₁') + κ`, `𝐂 = R_t (-w₂', w₂ + 1) + κ`,
`𝐃 = R_t (-w₂', w₂) + κ` (`gs_Phase.A`, ...); the reduced system `H` of
`MovingSofaOptimality/External/Romik/Num.lean` and its Newton-type map. The script checks with
`assert`s the facts that the captions state, and compares the numbers it draws with the generated
Lean files.
"""
import math
import os
import re
from fractions import Fraction as Fr
from pathlib import Path

import mpmath as mp
import numpy as np

import gerver
from sofa_figures import Figure, INK, FAINT, WALL, FLOOR, COLORS, FILLS, sb, sp

PI = math.pi
ROOT = Path(__file__).resolve().parents[2]
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
# One colour per phase of the rotation path.
PHASE_COLORS = [COLORS[6], COLORS[2], COLORS[1], COLORS[3], COLORS[4]]
# One colour per contact curve: the outer curves 𝐀, 𝐂 bound the cap, the inner curves 𝐁, 𝐃 and the
# path 𝐱 bound the niche.
CURVE_COLORS = {'A': BLUE, 'C': BLUE, 'B': GREEN, 'D': GREEN, 'x': ORANGE}
PHI, THETA = gerver.PHI, gerver.THETA
T = [0.0, PHI, THETA, PI / 2 - THETA, PI / 2 - PHI, PI / 2]   # the partition t₀ < ... < t₅
KAPPA = [gerver.k1, gerver.k2, gerver.k3, gerver.k4, gerver.k5]
# PLAIN_LABELS=1 writes subscripts inline, for previews in renderers without <tspan> support.
PLAIN = os.environ.get('PLAIN_LABELS') == '1'


def sub(base, s, after=''):
    return f'{base}{s}{after}' if PLAIN else sb(base, s, after)


def sup(base, s, after=''):
    return f'{base}{s}{after}' if PLAIN else sp(base, s, after)


# ---------------------------------------------------------------- the five phases (Frame.lean)

def frame(i, t):
    """(w₁, w₂, w₁', w₂', w₁'', w₂'') of phase i = 0, ..., 4 (`gs_ph1`, ..., `gs_ph5`)."""
    c, s = math.cos(t), math.sin(t)
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


def phase(t):
    """The phase of `GerverParams.path` at t (0-based)."""
    if t < PHI:
        return 0
    if t < THETA:
        return 1
    if t <= PI / 2 - THETA:
        return 2
    if t <= PI / 2 - PHI:
        return 3
    return 4


def rot(t, p):
    return gerver.rot(t, p)


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def curve(name, t, i=None):
    """The point of 𝐱 (name 'x'), 𝐀, 𝐁, 𝐂 or 𝐃 at time t, on phase i (default: the phase of t)."""
    i = phase(t) if i is None else i
    w1, w2, w1d, w2d, _, _ = frame(i, t)
    local = {'x': (w1, w2), 'A': (w1 + 1, w1d), 'B': (w1, w1d), 'C': (-w2d, w2 + 1),
             'D': (-w2d, w2)}[name]
    return add(rot(t, local), KAPPA[i])


def alpha(t, i=None):
    """α = ⟨𝐱', u_t⟩ = w₁' - w₂."""
    w = frame(phase(t) if i is None else i, t)
    return w[2] - w[1]


def beta(t, i=None):
    """β = ⟨𝐱', v_t⟩ = w₂' + w₁."""
    w = frame(phase(t) if i is None else i, t)
    return w[3] + w[0]


def rho(t, i=None):
    """(ρ_A, ρ_C) = (w₁'' + w₁ + 1, w₂'' + w₂ + 1)."""
    w = frame(phase(t) if i is None else i, t)
    return w[4] + w[0] + 1, w[5] + w[1] + 1


def dist(p, q):
    return math.hypot(p[0] - q[0], p[1] - q[1])


def check_phases():
    """Romik's equations at the phase boundaries, and the identities the chapter quotes."""
    for k in range(1, 5):
        t = T[k]
        for nm in 'x':
            assert dist(curve(nm, t, k - 1), curve(nm, t, k)) < 1e-12, (k, nm)
        # 𝐱 is C¹: α and β agree at the junctions.
        assert abs(alpha(t, k - 1) - alpha(t, k)) < 1e-12 and abs(beta(t, k - 1) - beta(t, k)) < 1e-12
    assert dist(curve('x', 0), (0, 0)) < 1e-12 and dist(curve('A', 0), (1, 0)) < 1e-12
    assert abs(curve('x', PI / 2)[1]) < 1e-12
    assert dist(curve('B', T[3], 3), curve('x', T[1])) < 1e-12        # Romik's (43)
    assert dist(curve('D', T[2], 1), curve('x', T[4])) < 1e-12        # Romik's (44)
    assert abs(curve('B', PI / 2)[1]) < 1e-12 and abs(curve('D', 0)[1]) < 1e-12
    for t in np.linspace(1e-6, PI / 2 - 1e-6, 400):
        assert alpha(t) < 0 < beta(t)
        ra, rc = rho(t)
        assert ra >= 0 and rc >= 0
    # Gerver's constants are -α(φ) and β(φ).
    assert abs(-alpha(PHI) - gerver.A) < 1e-12 and abs(beta(PHI) - gerver.B) < 1e-12


def sample(name, a, b, i, n=60):
    return [curve(name, t, i) for t in np.linspace(a, b, n)]


def pieces(n=60):
    """The 18 pieces of the boundary of Gerver's sofa, counterclockwise from 𝐀(0) = (1, 0):
    (curve, phase (1-based) or None for an edge, points)."""
    out = []
    for i in range(1, 5):
        out.append(('A', i + 1, sample('A', T[i], T[i + 1], i, n)))
    out.append(('top', None, [curve('A', PI / 2), curve('C', 0)]))
    for i in range(0, 4):
        out.append(('C', i + 1, sample('C', T[i], T[i + 1], i, n)))
    out.append(('left', None, [curve('C', PI / 2), curve('D', 0)]))
    for i in range(0, 2):
        out.append(('D', i + 1, sample('D', T[i], T[i + 1], i, n)))
    for i in (3, 2, 1):
        out.append(('x', i + 1, sample('x', T[i + 1], T[i], i, n)))
    for i in (3, 4):
        out.append(('B', i + 1, sample('B', T[i], T[i + 1], i, n)))
    out.append(('right', None, [curve('B', PI / 2), curve('A', 0)]))
    return out


def outline_exact(n=60):
    """The boundary of Gerver's sofa as a closed polygon, from its 18 pieces."""
    pts = []
    for _, _, ps in pieces(n):
        pts.extend(ps[:-1])
    return pts


def shoelace(pts):
    return 0.5 * sum(p[0] * q[1] - p[1] * q[0] for p, q in zip(pts, pts[1:] + pts[:1]))


def cap_outline(n=60):
    """The cap K: the region between the x-axis and 𝐀, the top edge and 𝐂."""
    pts = []
    for nm, _, ps in pieces(n)[:9]:
        pts.extend(ps[:-1])
    pts.append(curve('C', PI / 2))
    return pts


def niche_outline(n=60):
    """The niche: the region between the x-axis and 𝐃, 𝐱|[t₁, t₄] and 𝐁."""
    pts = []
    for nm, _, ps in pieces(n)[11:17]:
        pts.extend(ps[:-1])
    pts.append(curve('B', PI / 2))
    return pts


# ---------------------------------------------------------------- drawing helpers

def clip_polygon(pts, xmin, xmax, ymin, ymax):
    """Sutherland-Hodgman clipping of a polygon to a rectangle."""
    def clip(poly, inside, cut):
        out = []
        for k, p in enumerate(poly):
            q = poly[k - 1]
            if inside(p):
                if not inside(q):
                    out.append(cut(q, p))
                out.append(p)
            elif inside(q):
                out.append(cut(q, p))
        return out

    def cut_x(x0):
        return lambda p, q: (x0, p[1] + (q[1] - p[1]) * (x0 - p[0]) / (q[0] - p[0]))

    def cut_y(y0):
        return lambda p, q: (p[0] + (q[0] - p[0]) * (y0 - p[1]) / (q[1] - p[1]), y0)

    poly = list(pts)
    for inside, cut in [(lambda p: p[0] >= xmin, cut_x(xmin)), (lambda p: p[0] <= xmax, cut_x(xmax)),
                        (lambda p: p[1] >= ymin, cut_y(ymin)), (lambda p: p[1] <= ymax, cut_y(ymax))]:
        if not poly:
            break
        poly = clip(poly, inside, cut)
    return poly


def clip_segment(a, b, xmin, xmax, ymin, ymax):
    """Liang-Barsky clipping of the segment ab to a rectangle (None if it misses)."""
    t0, t1 = 0.0, 1.0
    dx, dy = b[0] - a[0], b[1] - a[1]
    for p, q in [(-dx, a[0] - xmin), (dx, xmax - a[0]), (-dy, a[1] - ymin), (dy, ymax - a[1])]:
        if p == 0:
            if q < 0:
                return None
        else:
            r = q / p
            if p < 0:
                t0 = max(t0, r)
            else:
                t1 = min(t1, r)
    if t0 > t1:
        return None
    return (a[0] + t0 * dx, a[1] + t0 * dy), (a[0] + t1 * dx, a[1] + t1 * dy)


def arrow(f, a, b, color=INK, width=1.3):
    f.line(a, b, stroke=color, width=width, arrow=True)


def save(f, name, title):
    path = f.save(name, title)
    print(f'wrote {path.relative_to(ROOT)}')
    return path


# ---------------------------------------------------------------- Chapter 10

def fig_phases(sofa):
    """Figure 10.1: the sofa and its rotation path, one colour per phase."""
    f = Figure(-2.42, 1.18, -0.44, 1.12, 175)
    f.polygon(sofa, fill=FILLS[0], stroke=BLUE, width=1.6)
    f.line((-2.4, 0), (1.15, 0), stroke=FAINT, width=1)
    for i in range(5):
        ts = np.linspace(T[i], T[i + 1], 80)
        f.polyline([curve('x', t, i) for t in ts], stroke=PHASE_COLORS[i], width=3.0)
    for k in range(1, 5):
        f.dot(curve('x', T[k]), r=3.4, fill=INK)
    f.dot(curve('x', 0), r=3.2, fill=PHASE_COLORS[0])
    f.dot(curve('x', PI / 2), r=3.2, fill=PHASE_COLORS[4])
    # Labels of the junctions, inside the niche, and of the ends below the axis.
    lab = {1: ('φ', (-0.05, 0.1), 'end'), 2: ('θ', (0.05, 0.08), 'start'),
           3: ('π/2 − θ', (-0.05, 0.08), 'end'), 4: ('π/2 − φ', (0.05, 0.1), 'start')}
    for k, (s, d, anchor) in lab.items():
        p = curve('x', T[k])
        f.text((p[0] + d[0], p[1] + d[1]), f'x({s})', size=14, anchor=anchor)
    p0, p5 = curve('x', 0), curve('x', PI / 2)
    f.text((p0[0] + 0.03, p0[1] - 0.09), 'x(0)', size=14, anchor='start')
    f.text((p5[0] - 0.03, p5[1] - 0.09), 'x(π/2)', size=14, anchor='end')
    # Legend in two rows, spaced by the estimated widths of its labels.
    names = ['[0, φ)', '[φ, θ)', '[θ, π/2 − θ]', '(π/2 − θ, π/2 − φ]', '(π/2 − φ, π/2]']
    for row, idx in enumerate([(0, 1, 2), (3, 4)]):
        x, y0 = -2.32, -0.25 - 0.13 * row
        for i in idx:
            label = f'phase {i + 1}: t ∈ {names[i]}'
            f.line((x, y0), (x + 0.14, y0), stroke=PHASE_COLORS[i], width=3.0)
            f.text((x + 0.18, y0), label, size=12.5, anchor='start', italic=False)
            x += 0.18 + len(label) * 0.5 * 12.5 / 175 + 0.2
        assert x < 1.2, x
    f.text((0.6, 0.5), 'G', size=17, color=BLUE)
    return save(f, '10-gerver/phases',
                "Gerver's sofa G with its rotation path x(t), drawn in five colours for the five "
                "phases [0, φ), [φ, θ), [θ, π/2 − θ], (π/2 − θ, π/2 − φ], (π/2 − φ, π/2]; the "
                "path starts at the origin, runs along the top of the niche, and ends at x(π/2) "
                "on the x-axis, and dots mark the four phase boundaries")


def hallway_at(f, dx, xmin, ymin, xmax=1.0, ymax=1.0, width=2.4):
    """The hallway L, shifted by (dx, 0), clipped to x ≥ xmin and y ≥ ymin."""
    s = lambda p: (p[0] + dx, p[1])
    f.polygon([s(p) for p in [(xmin, 0), (0, 0), (0, ymin), (1, ymin), (1, 1), (xmin, 1)]],
              fill=FLOOR, stroke='none', width=0)
    f.polyline([s(p) for p in [(xmin, 1), (1, 1), (1, ymin)]], stroke=WALL, width=width)
    f.polyline([s(p) for p in [(xmin, 0), (0, 0), (0, ymin)]], stroke=WALL, width=width)


CONTACTS = [('A', 'C', 'D'), ('A', 'C', 'D', 'x'), ('A', 'C', 'x'), ('A', 'B', 'C', 'x'),
            ('A', 'B', 'C')]


def hallway_coords(t, p):
    """The coordinates (⟨p - 𝐱(t), u_t⟩, ⟨p - 𝐱(t), v_t⟩) of p in the hallway at time t."""
    x = curve('x', t)
    d = (p[0] - x[0], p[1] - x[1])
    c, s = math.cos(t), math.sin(t)
    return (c * d[0] + s * d[1], -s * d[0] + c * d[1])


def fig_contacts(sofa):
    """Figure 10.2: the sofa in the hallway at one time of each phase, with its contact points."""
    times = [PHI / 2, (PHI + THETA) / 2, PI / 4, PI / 2 - (PHI + THETA) / 2, PI / 2 - PHI / 2]
    lo, hi, gap = -2.35, 1.1, 0.42
    w = hi - lo + gap
    f = Figure(lo, lo + 5 * w - gap, -2.75, 1.3, 47)
    for i, t in enumerate(times):
        dx = i * w
        hallway_at(f, dx, lo, -2.35)
        moved = gerver.place(t, sofa)
        # The moved sofa stays in the hallway.
        for X, Y in moved:
            assert X <= 1 + 1e-9 and Y <= 1 + 1e-9 and (X >= -1e-9 or Y >= -1e-9), (t, X, Y)
        f.polygon([(X + dx, Y) for X, Y in moved], fill=FILLS[0], stroke=BLUE, width=1.2)
        for nm in CONTACTS[i]:
            q = hallway_coords(t, curve(nm, t))
            expected = {'A': (1, alpha(t)), 'B': (0, alpha(t)), 'C': (-beta(t), 1),
                        'D': (-beta(t), 0), 'x': (0, 0)}[nm]
            assert dist(q, expected) < 1e-9, (nm, t)
            # The contact point lies on the boundary of the moved sofa.
            assert min(dist(q, m) for m in moved) < 0.02, (nm, t)
            f.dot((q[0] + dx, q[1]), r=3.6, fill=CURVE_COLORS[nm])
            off = {'A': (0.2, 0.0), 'B': (-0.2, 0.0), 'C': (0.0, 0.22), 'D': (0.0, -0.27),
                   'x': (-0.2, -0.2)}[nm]
            f.text((q[0] + dx + off[0], q[1] + off[1]), nm, size=14, color=CURVE_COLORS[nm])
        f.text((dx + (lo + hi) / 2, -2.58), f'phase {i + 1}', size=14, italic=False,
               color=PHASE_COLORS[i])
    return save(f, '10-gerver/contacts',
                "Gerver's sofa in the hallway at one time in each of the five phases. Phase 1: "
                "the sofa touches the walls at A, C and D; phase 2 at A, C, D and the inner corner "
                "x; phase 3 at A, C and x; phase 4 at A, B, C and x; phase 5 at A, B and C")


def normal_out(ps):
    """The outward unit normal of a counterclockwise boundary piece at its middle."""
    k = len(ps) // 2
    a, b = ps[max(k - 1, 0)], ps[min(k + 1, len(ps) - 1)]
    dx, dy = b[0] - a[0], b[1] - a[1]
    n = math.hypot(dx, dy)
    return (dy / n, -dx / n)


def polylen(ps):
    return sum(dist(p, q) for p, q in zip(ps, ps[1:]))


def fig_pieces(sofa):
    """Figure 10.3: the 18 boundary pieces of the sofa."""
    f = Figure(-2.45, 1.32, -0.36, 1.32, 175)
    f.polygon(sofa, fill=FILLS[0], stroke='none', width=0)
    ps = pieces(80)
    assert len(ps) == 18 and sum(1 for nm, _, _ in ps if nm in 'ABCDx') == 15
    tiny = []
    for nm, i, pts in ps:
        color = CURVE_COLORS.get(nm, INK)
        f.polyline(pts, stroke=color, width=3.0 if nm in 'ABCDx' else 2.0)
        if nm in 'ABCDx' and polylen(pts) < 0.03:
            tiny.append(nm + str(i))
    # The four short pieces have length φ/2 (ρ = 1/2 on the first and last phases).
    assert sorted(tiny) == ['A5', 'B5', 'C1', 'D1'], tiny
    for nm, i, pts in ps:
        if nm in 'ABCDx' and polylen(pts) < 0.03:
            assert abs(polylen(pts) - PHI / 2) < 1e-6
    for _, _, pts in ps:
        f.dot(pts[0], r=2.8, fill=INK)
    # Labels: outside the sofa, along the outward normal; the short pieces get leader lines.
    lead = {'A5': (0.0, 1.2), 'C1': (-1.23, 1.2), 'D1': (-1.62, -0.18), 'B5': (0.42, -0.18)}
    for nm, i, pts in ps:
        if nm not in 'ABCDx':
            continue
        key = nm + str(i)
        mid = pts[len(pts) // 2]
        color = CURVE_COLORS[nm]
        if key in lead:
            q = lead[key]
            f.line(mid, (q[0] + (-0.06 if q[0] > mid[0] else 0.06), q[1] + (0.04 if q[1] < mid[1] else -0.05)),
                   stroke=FAINT, width=1)
            f.text(q, sub(nm, str(i)), size=15, color=color)
            continue
        n = normal_out(pts)
        d = 0.13 if nm in 'AC' else 0.11
        f.text((mid[0] + d * n[0], mid[1] + d * n[1]), sub(nm, str(i)), size=15, color=color)
    a0, cpi = curve('A', 0), curve('C', PI / 2)
    f.text((a0[0] + 0.05, a0[1] - 0.12), sub('A', '1'), size=15, color=BLUE)
    f.text((cpi[0] - 0.05, cpi[1] - 0.12), sub('C', '5'), size=15, color=BLUE)
    f.text((-0.62, 0.86), 'G', size=17, color=BLUE)
    return save(f, '10-gerver/pieces',
                "The boundary of Gerver's sofa G in 18 pieces, separated by dots: the outer curves "
                "A (phases 2 to 5) and C (phases 1 to 4) in blue, the top edge from A(π/2) to C(0), "
                "the bottom edges on the x-axis, and around the niche the curves D (phases 1, 2) and "
                "B (phases 4, 5) in green and the rotation path x (phases 2 to 4) in orange. On "
                "phase 1 the curve A stays at the corner (1, 0), and on phase 5 the curve C stays at "
                "the opposite corner")


def H_np(ph, th):
    """The reduced system H = (H₁, H₂) of Num.lean (`rom_H1`, `rom_H2`), vectorized."""
    c, s, C, S = np.cos(ph), np.sin(ph), np.cos(th), np.sin(th)
    K = PI / 2 - 1.5 - th + th ** 2 / 4
    D = 2 * c - (2 + th - ph) * s
    Nb = c * (ph - 0.5 - c / 2) - s * (s / 2 - ph ** 2 / 4 + K + 1.5)
    U1 = -(c * (K - ph ** 2 / 4)) + s * (ph / 2 - 1) + 3 * C / 2 + S * (3 * th / 2 - 3)
    V1 = c * (2 + th - ph) - s - 3 * S
    U2 = -(s * (K - ph ** 2 / 4)) - c * (ph / 2 - 1) - S / 2 + C * (th / 2 - 1)
    V2 = s * (2 + th - ph) + c - C
    return D * U1 + Nb * V1, D * U2 + Nb * V2


def fig_box():
    """Figure 10.4: the box of `GerverParams.InBox`, the zero sets of H₁ and H₂, and the solution."""
    import contourpy
    u = lambda ph: (ph - 0.039) / 0.001
    w = lambda th: (th - 0.68) / 0.01
    f = Figure(-0.3, 1.22, -0.22, 1.1, 330)
    f.polygon([(0, 0), (1, 0), (1, 1), (0, 1)], fill='#f9fafb', stroke=INK, width=1.4)
    n = 241
    phs, ths = np.linspace(0.039, 0.04, n), np.linspace(0.68, 0.69, n)
    P, Q = np.meshgrid(phs, ths)
    h1, h2 = H_np(P, Q)
    curves = {}
    for k, (h, color, name) in enumerate([(h1, GREEN, '1'), (h2, PURPLE, '2')]):
        lines = contourpy.contour_generator(phs, ths, h).lines(0.0)
        assert len(lines) == 1, (name, len(lines))   # one arc of each zero set crosses the box
        pts = [(u(a), w(b)) for a, b in lines[0]]
        curves[name] = pts
        f.polyline(pts, stroke=color, width=2.4)
    sol = (u(PHI), w(THETA))
    # The solution: H vanishes there, and it is the only crossing of the two arcs in the box.
    r1, r2 = H_np(PHI, THETA)
    assert abs(r1) < 1e-13 and abs(r2) < 1e-13
    f.dot(sol, r=4.2, fill=ORANGE)
    f.text((sol[0] - 0.03, sol[1] + 0.07), '(φ, θ)', size=15, anchor='end', color=ORANGE)
    # Labels of the arcs, at their ends inside the box.
    e2 = max(curves['2'], key=lambda p: p[1])
    f.text((0.56, 0.12), sub('H', '1', ' = 0'), size=15, anchor='start', color=GREEN)
    f.text((e2[0] + 0.03, e2[1] - 0.05), sub('H', '2', ' = 0'), size=15, anchor='start', color=PURPLE)
    for a, lab in [(0, '0.039'), (0.5, '0.0395'), (1, '0.04')]:
        f.line((a, 0), (a, -0.02), stroke=INK, width=1)
        f.text((a, -0.07), lab, size=12.5, italic=False)
    for b, lab in [(0, '0.68'), (0.5, '0.685'), (1, '0.69')]:
        f.line((0, b), (-0.02, b), stroke=INK, width=1)
        f.text((-0.04, b), lab, size=12.5, italic=False, anchor='end')
    f.text((0.5, -0.16), 'φ', size=16)
    f.text((-0.22, 0.5), 'θ', size=16)
    return save(f, '10-gerver/box',
                "The box 0.039 ≤ φ ≤ 0.04, 0.68 ≤ θ ≤ 0.69 of the parameters, drawn with different "
                "scales on the two axes, with the zero sets of the two components H1 and H2 of the "
                "reduced system; they cross once, at Romik's solution (φ, θ) = (0.03918, 0.68130)")


def fig_cap(t=0.3):
    """Figure 10.5: the cap K, its niche, and the supporting hallway L_K(t) at a time of phase 2."""
    xmin, xmax, ymin, ymax = -2.55, 1.75, -1.25, 1.55
    f = Figure(xmin, xmax, ymin, ymax, 150)
    assert phase(t) == 1
    x = curve('x', t)
    u, v = (math.cos(t), math.sin(t)), (-math.sin(t), math.cos(t))
    P = lambda X, Y: (x[0] + X * u[0] + Y * v[0], x[1] + X * u[1] + Y * v[1])
    big = 9.0
    floor = [P(-big, 0), P(0, 0), P(0, -big), P(1, -big), P(1, 1), P(-big, 1)]
    f.polygon(clip_polygon(floor, xmin, xmax, ymin, ymax), fill=FLOOR, stroke='none', width=0)
    cap = cap_outline(80)
    niche = niche_outline(80)
    f.polygon(cap, fill=FILLS[0], stroke=BLUE, width=1.8)
    f.polygon(niche, fill=FILLS[1], stroke=ORANGE, width=1.4)
    # The walls: outer a(t) (X = 1) and c(t) (Y = 1), inner b(t) (X = 0, Y ≤ 0) and d(t) (Y = 0, X ≤ 0).
    for a, b in [(P(-big, 1), P(1, 1)), (P(1, 1), P(1, -big)), (P(-big, 0), P(0, 0)),
                 (P(0, 0), P(0, -big))]:
        seg = clip_segment(a, b, xmin, xmax, ymin, ymax)
        if seg:
            f.line(*seg, stroke=WALL, width=2.6)
    pts = {nm: curve(nm, t) for nm in 'ACDx'}
    # The contact points lie on their walls, and the walls support the cap.
    X = lambda p: (p[0] - x[0]) * u[0] + (p[1] - x[1]) * u[1]
    Y = lambda p: (p[0] - x[0]) * v[0] + (p[1] - x[1]) * v[1]
    assert abs(X(pts['A']) - 1) < 1e-12 and abs(Y(pts['C']) - 1) < 1e-12 and abs(Y(pts['D'])) < 1e-12
    assert X(pts['D']) < 0
    assert max(X(p) for p in cap) < 1 + 1e-6 and max(Y(p) for p in cap) < 1 + 1e-6
    offs = {'A': (0.17, -0.02, 'A(t)'), 'C': (-0.05, 0.17, 'C(t)'), 'D': (-0.02, -0.17, 'D(t)'),
            'x': (0.2, -0.13, 'x(t)')}
    for nm, (dx, dy, lab) in offs.items():
        p = pts[nm]
        f.dot(p, r=3.8, fill=CURVE_COLORS[nm])
        f.text((p[0] + dx, p[1] + dy), lab, size=14, color=CURVE_COLORS[nm])
    for X0, Y0, lab in [(1.0, -1.35, 'a(t)'), (-2.2, 1.0, 'c(t)'), (0.0, -1.0, 'b(t)'),
                        (-1.6, 0.0, 'd(t)')]:
        q = P(X0, Y0)
        f.text((q[0] + (0.17 if lab[0] in 'ab' else 0.0), q[1] + (0.0 if lab[0] in 'ab' else -0.14)),
               lab, size=14, color=WALL)
    f.text((-0.65, 0.88), 'K', size=17, color=BLUE)
    f.text((-0.62, 0.25), 'niche', size=13, italic=False, color=ORANGE)
    return save(f, '10-gerver/cap',
                "The cap K of Gerver's sofa (blue outline), its niche (orange), and the supporting "
                "hallway at a time t of phase 2, whose outer walls a(t), c(t) touch K at A(t) and "
                "C(t), whose inner wall d(t) touches the niche's boundary at D(t), and whose inner "
                "corner x(t) lies on the top of the niche")


def fig_principle():
    """Figure 10.6: Principle P: a half-plane of normal u_σ, σ ∈ [s, s + π/2], misses Q⁻(s)."""
    s, sig = 0.45, 0.45 + 0.6
    R = 1.25
    f = Figure(-1.45, 1.45, -1.35, 1.35, 150)
    us, vs, usig = (math.cos(s), math.sin(s)), (-math.sin(s), math.cos(s)), (math.cos(sig), math.sin(sig))
    # The quadrant Q⁻(s) = {X < 0, Y < 0} and the half-plane {⟨q, u_σ⟩ ≥ 0}, cut to a disk of radius R.
    disk = [(R * math.cos(a), R * math.sin(a)) for a in np.linspace(0, 2 * PI, 241)]
    def cut(poly, nx, ny):
        out = []
        for k, p in enumerate(poly):
            q = poly[k - 1]
            fp, fq = p[0] * nx + p[1] * ny, q[0] * nx + q[1] * ny
            if fp <= 0:
                if fq > 0:
                    lam = fq / (fq - fp)
                    out.append((q[0] + lam * (p[0] - q[0]), q[1] + lam * (p[1] - q[1])))
                out.append(p)
            elif fq <= 0:
                lam = fq / (fq - fp)
                out.append((q[0] + lam * (p[0] - q[0]), q[1] + lam * (p[1] - q[1])))
        return out
    quad = cut(cut(disk, *us), *vs)                           # X ≤ 0 and Y ≤ 0
    half = cut(disk, -usig[0], -usig[1])                      # ⟨q, u_σ⟩ ≥ 0
    for q in quad:
        assert q[0] * usig[0] + q[1] * usig[1] <= 1e-12       # the quadrant lies in ⟨q, u_σ⟩ ≤ 0
    f.polygon(half, fill=FILLS[2], stroke='none', width=0)
    f.polygon(quad, fill=FILLS[1], stroke='none', width=0)
    # The walls through x(s): the half-lines bounding the quadrant.
    f.line((0, 0), (-R * us[0], -R * us[1]), stroke=WALL, width=2.4)
    f.line((0, 0), (-R * vs[0], -R * vs[1]), stroke=WALL, width=2.4)
    a, b = (-R * usig[1], R * usig[0]), (R * usig[1], -R * usig[0])
    f.line(a, b, stroke=GREEN, width=1.4, dash='6 4')
    arrow(f, (0, 0), (0.75 * us[0], 0.75 * us[1]))
    arrow(f, (0, 0), (0.75 * vs[0], 0.75 * vs[1]))
    arrow(f, (0, 0), (0.75 * usig[0], 0.75 * usig[1]), color=GREEN, width=1.6)
    arc = [(0.42 * math.cos(a), 0.42 * math.sin(a)) for a in np.linspace(s, sig, 30)]
    f.polyline(arc, stroke=FAINT, width=1.2)
    m = (s + sig) / 2
    f.text((0.52 * math.cos(m), 0.52 * math.sin(m)), 'σ − s', size=12.5, italic=True)
    f.dot((0, 0), r=3.6, fill=ORANGE)
    f.text((-0.12, 0.01), 'x(s)', size=14, anchor='end')
    f.text((0.88 * us[0] + 0.02, 0.88 * us[1] - 0.06), sub('u', 's'), size=15)
    f.text((0.88 * vs[0] - 0.08, 0.88 * vs[1]), sub('v', 's'), size=15)
    f.text((0.9 * usig[0] + 0.08, 0.9 * usig[1] + 0.03), sub('u', 'σ'), size=15, color=GREEN)
    qc = (-0.62 * (us[0] + vs[0]), -0.62 * (us[1] + vs[1]))
    f.text(qc, sup('Q', '−', '(s)'), size=15, color=ORANGE)
    p = (0.45, 0.95)
    assert p[0] * usig[0] + p[1] * usig[1] >= 0
    f.dot(p, r=3.6, fill=INK)
    f.text((p[0] + 0.1, p[1] + 0.02), 'p', size=15, anchor='start')
    return save(f, '10-gerver/principle',
                "Principle P. At the point x(s), the quadrant Q⁻(s) (orange) lies between the two "
                "inner walls, opposite to the directions u_s and v_s. For a direction u_σ with σ "
                "between s and s + π/2, the closed half-plane of points p with ⟨p − x(s), u_σ⟩ ≥ 0 "
                "(green, bounded by the dashed line) does not meet Q⁻(s)")


def fig_niche():
    """Figure 10.7: the niche as the union of the quadrants Q⁻(s), below the envelope of the inner walls."""
    xmin, xmax, ymin, ymax = -1.62, 0.42, -0.05, 0.9
    f = Figure(xmin, xmax, ymin, ymax, 390)
    sofa = outline_exact(80)
    f.polygon(clip_polygon(sofa, xmin, xmax, ymin, ymax), fill=FILLS[0], stroke='none', width=0)
    niche = niche_outline(80)
    f.polygon(niche, fill=FILLS[1], stroke='none', width=0)
    f.line((xmin, 0), (xmax, 0), stroke=FAINT, width=1)
    # One quadrant Q⁻(s₀), cut at the x-axis.
    s0 = 0.45
    x0 = curve('x', s0)
    u0, v0 = (math.cos(s0), math.sin(s0)), (-math.sin(s0), math.cos(s0))
    hit = lambda d: (x0[0] - x0[1] * d[0] / d[1], 0.0)
    quad = [x0, hit((-v0[0], -v0[1])), hit((-u0[0], -u0[1]))]
    f.polygon(quad, fill='#fdba74', stroke='none', width=0, opacity=0.8)
    # The inner walls b(s) (direction -v_s) and d(s) (direction -u_s), from x(s) down to the x-axis.
    for s in np.linspace(0.05, PI / 2 - 0.05, 27):
        x = curve('x', s)
        if x[1] <= 0:
            continue
        for d in [(math.sin(s), -math.cos(s)), (-math.cos(s), -math.sin(s))]:
            end = (x[0] - x[1] * d[0] / d[1], 0.0)
            seg = clip_segment(x, end, xmin, xmax, ymin, ymax)
            if seg:
                f.line(*seg, stroke=FAINT, width=0.8)
    # Every point of the niche lies in some quadrant; the curves B, x, D bound the union.
    rng = np.random.default_rng(1)
    ss = np.linspace(1e-3, PI / 2 - 1e-3, 3000)
    xs = np.array([curve('x', s) for s in ss])
    def in_union(q):
        d = q - xs
        X = d[:, 0] * np.cos(ss) + d[:, 1] * np.sin(ss)
        Y = -d[:, 0] * np.sin(ss) + d[:, 1] * np.cos(ss)
        return bool(np.any((X < 0) & (Y < 0)))
    from matplotlib.path import Path as MPath
    npath = MPath(np.array(niche))
    border = np.array([q for _, _, pts in pieces(400)[10:17] for q in pts])
    checked = 0
    for q in rng.uniform([-1.5, 0.002], [0.3, 0.7], size=(400, 2)):
        if np.min(np.hypot(*(border - q).T)) < 3e-3:
            continue
        assert npath.contains_point(q) == in_union(q), q
        checked += 1
    assert checked > 350, checked
    for nm, i, pts in pieces(80)[10:17]:
        if nm in 'BDx':
            f.polyline(pts, stroke=CURVE_COLORS[nm], width=3.0)
    for nm, t, i, d in [('D', THETA / 2, 1, (-0.08, 0.04)), ('B', PI / 2 - THETA / 2, 3, (0.08, 0.04)),
                        ('x', PI / 4, 2, (0.0, 0.07))]:
        p = curve(nm, t, i)
        f.text((p[0] + d[0], p[1] + d[1]), nm, size=16, color=CURVE_COLORS[nm])
    f.dot(x0, r=3.6, fill=ORANGE)
    f.text((x0[0] + 0.08, x0[1] + 0.035), sub('x(s', '0', ')'), size=14)
    f.text((x0[0] + 0.02, 0.12), sup('Q', '−', '(s0)') if PLAIN else sp('Q', '−', '(s<tspan dy="4.5" font-size="10.2">0</tspan><tspan dy="-4.5">)</tspan>'), size=14)
    return save(f, '10-gerver/niche',
                "The niche of Gerver's sofa (orange) as the union of the quadrants Q⁻(s): grey "
                "segments show the inner walls b(s) and d(s) from x(s) down to the x-axis for many "
                "s, one quadrant is shaded darker, and the curves D, x and B bound the union from "
                "above: x is traced by the corners, D and B are the envelopes of the walls")


# ---------------------------------------------------------------- Appendix B

NUM = ROOT / 'MovingSofaOptimality' / 'External' / 'Romik' / 'Num.lean'
FIX = ROOT / 'MovingSofaOptimality' / 'External' / 'Romik' / 'Fix.lean'
LEAN_NUM = r'\(?(-?[\d.]+)\s*:\s*ℝ\)?'
# The rational matrix of the Newton-type map in Num.lean: rom_G1 = φ + (0.1481 H₁ + 0.2886 H₂),
# rom_G2 = θ + (2.7218 H₁ - 0.6267 H₂), that is G(z) = z - M H(z) with M ≈ DH(z*)⁻¹.
MNEG = ((Fr('0.1481'), Fr('0.2886')), (Fr('2.7218'), Fr('-0.6267')))


def lean_enclosure(text, name):
    """The interval [L, U] of the conclusion `... ∈ Icc L U` of the Lean theorem `name`."""
    start = re.search(r'theorem ' + re.escape(name) + r'\b', text).start()
    statement = text[start:text.index(':= by', start)]
    m = re.findall(r'∈\s+Icc\s+' + LEAN_NUM + r'\s+' + LEAN_NUM, statement)[-1]
    return Fr(m[0]), Fr(m[1])


def H_mp(ph, th):
    c, s, C, S = mp.cos(ph), mp.sin(ph), mp.cos(th), mp.sin(th)
    K = mp.pi / 2 - mp.mpf(3) / 2 - th + th ** 2 / 4
    D = 2 * c - (2 + th - ph) * s
    Nb = c * (ph - mp.mpf(1) / 2 - c / 2) - s * (s / 2 - ph ** 2 / 4 + K + mp.mpf(3) / 2)
    U1 = -(c * (K - ph ** 2 / 4)) + s * (ph / 2 - 1) + 3 * C / 2 + S * (3 * th / 2 - 3)
    V1 = c * (2 + th - ph) - s - 3 * S
    U2 = -(s * (K - ph ** 2 / 4)) - c * (ph / 2 - 1) - S / 2 + C * (th / 2 - 1)
    V2 = s * (2 + th - ph) + c - C
    return D * U1 + Nb * V1, D * U2 + Nb * V2


def G_mp(ph, th):
    h1, h2 = H_mp(ph, th)
    m = [[mp.mpf(str(float(x))) for x in row] for row in MNEG]
    return ph + m[0][0] * h1 + m[0][1] * h2, th + m[1][0] * h1 + m[1][1] * h2


def fig_contraction():
    """Figure B.1: G maps the square of radius 10⁻¹⁰ about z₀ into itself."""
    mp.mp.dps = 40
    r = mp.mpf('1e-10')
    z0 = (mp.mpf('0.0391773648'), mp.mpf('0.6813015094'))
    sc = lambda z: (float((z[0] - z0[0]) / r), float((z[1] - z0[1]) / r))
    g0 = sc(G_mp(*z0))
    zs = mp.findroot(lambda a, b: H_mp(a, b), z0)
    star = sc((zs[0], zs[1]))
    fix = FIX.read_text()
    bounds = []
    for name in ['rom_G1φ_bound', 'rom_G1θ_bound', 'rom_G2φ_bound', 'rom_G2θ_bound']:
        m = re.search(r'theorem ' + name + r'\b.*?\|\s*≤\s*([\d.]+)', fix, re.S)
        bounds.append(float(m.group(1)))
    assert bounds == [0.03, 0.012, 0.3, 0.16], bounds
    lip = (bounds[0] + bounds[1], bounds[2] + bounds[3])
    # The residual G(z₀) - z₀ that rom_Gz_z0 encloses, in units of r.
    m = re.search(r'theorem rom_Gz_z0.*?Icc \(0\.0391773648 - ([\d.]+) : ℝ\)\s*\(0\.0391773648 - ([\d.]+)\)'
                  r'.*?Icc \(0\.6813015094 - ([\d.]+) : ℝ\)\s*\(0\.6813015094 - ([\d.]+)\)', fix, re.S)
    res = [-float(Fr(x) / Fr('1e-10')) for x in m.groups()]
    assert res[0] <= g0[0] <= res[1] and res[2] <= g0[1] <= res[3], (res, g0)
    rect = [(g0[0] - lip[0], g0[1] - lip[1]), (g0[0] + lip[0], g0[1] - lip[1]),
            (g0[0] + lip[0], g0[1] + lip[1]), (g0[0] - lip[0], g0[1] + lip[1])]
    for q in rect:
        assert max(abs(q[0]), abs(q[1])) < 1, q
    edge = list(np.linspace(-1, 1, 9))
    square = ([(a, -1.0) for a in edge] + [(1.0, b) for b in edge[1:]] + [(a, 1.0) for a in edge[::-1][1:]]
              + [(-1.0, b) for b in edge[::-1][1:-1]])
    image = [sc(G_mp(z0[0] + mp.mpf(a) * r, z0[1] + mp.mpf(b) * r)) for a, b in square]
    for q in image:
        assert rect[0][0] <= q[0] <= rect[1][0] and rect[0][1] <= q[1] <= rect[2][1], q
    f = Figure(-1.3, 1.3, -1.42, 1.25, 160)
    f.polygon([(-1, -1), (1, -1), (1, 1), (-1, 1)], fill='#f9fafb', stroke=INK, width=1.4)
    f.polygon(rect, fill=FILLS[2], stroke=GREEN, width=1.3, dash='5 3')
    f.polygon(image, fill=ORANGE, stroke=ORANGE, width=1.2)
    f.dot((0, 0), r=3.4, fill=INK)
    f.text((0.08, 0.06), sub('z', '0'), size=15, anchor='start')
    f.dot(star, r=3.0, fill=ORANGE)
    f.text((star[0] + 0.1, star[1] - 0.12), 'z*', size=15, anchor='start', color=ORANGE)
    f.text((g0[0], rect[2][1] + 0.09), 'contains G(T)', size=13, color=GREEN, italic=True)
    for a in (-1, 0, 1):
        f.line((a, -1), (a, -1.04), stroke=INK, width=1)
        f.text((a, -1.12), str(a), size=12.5, italic=False)
        f.line((-1, a), (-1.04, a), stroke=INK, width=1)
        f.text((-1.08, a), str(a), size=12.5, italic=False, anchor='end')
    diam = max(dist(p, q) for p in image for q in image)
    assert diam < 1e-3, diam
    sub0 = (lambda v: f'{v}0') if PLAIN else (lambda v: sb(v, '0'))
    f.text((0, -1.3), f'(φ − {sub0("φ")}) / r', size=14)
    f.text((-1.0, 1.13), f'(θ − {sub0("θ")}) / r', size=14, anchor='start')
    return save(f, 'appendix-b/contraction',
                "The square T of radius r = 10⁻¹⁰ about z0 = (0.0391773648, 0.6813015094), in "
                "units of r. The interval bounds on the partial derivatives of G put its image in the "
                "dashed green rectangle around G(z0), inside the square; the true image is a speck "
                "of diameter below 0.001 r around the zero z* of H (orange dot)")


def decimal(x):
    """The exact decimal expansion of a rational with a terminating one."""
    neg, x = x < 0, abs(x)
    k = 0
    while (x * 10 ** k).denominator != 1:
        k += 1
    digits = str(int(x * 10 ** k)).rjust(k + 1, '0')
    out = digits[:-k] + '.' + digits[-k:] if k else digits
    return ('−' if neg else '') + out


def fig_enclosure():
    """Figure B.2: the interval chain of `rom_D_box`, recomputed and compared with Num.lean."""
    text = NUM.read_text()
    block = text[text.index('theorem rom_D_box'):]
    block = block[:block.index('exact h5')]
    steps = re.findall(r'have (h\d) := (iv_\w+) \(L := ' + LEAN_NUM + r'\) \(U := ' + LEAN_NUM + r'\)',
                       block)
    steps = {h: (lem, Fr(a), Fr(b)) for h, lem, a, b in steps}
    hyp = {h: (Fr(a), Fr(b)) for h, a, b in
           re.findall(r'\((h\w) : \w ∈ Icc \((-?[\d.]+) : ℝ\) \((-?[\d.]+) : ℝ\)\)', block)}
    final = lean_enclosure(text, 'rom_D_box')
    # Recompute the chain with outward rounding to 10 decimals, as scripts/romik/gen.py does.
    dn = lambda x: Fr(math.floor(x * 10 ** 10), 10 ** 10)
    up = lambda x: Fr(math.ceil(x * 10 ** 10), 10 ** 10)
    phi, th, c, s = hyp['hφ'], hyp['hθ'], hyp['hc'], hyp['hs']
    h1 = (dn(2 * c[0]), up(2 * c[1]))
    h2 = (dn(2 + th[0]), up(2 + th[1]))
    h3 = (dn(h2[0] - phi[1]), up(h2[1] - phi[0]))
    h4 = (dn(h3[0] * s[0]), up(h3[1] * s[1]))
    h5 = (dn(h1[0] - h4[1]), up(h1[1] - h4[0]))
    for h, iv in [('h1', h1), ('h2', h2), ('h3', h3), ('h4', h4), ('h5', h5)]:
        assert steps[h][1:] == iv, (h, steps[h], iv)
    assert final == h5
    # The true range of D on the box is inside the enclosure.
    vals = [2 * math.cos(a) - (2 + b - a) * math.sin(a) for a in np.linspace(0.039, 0.04, 21)
            for b in np.linspace(0.68, 0.69, 21)]
    assert float(h5[0]) <= min(vals) and max(vals) <= float(h5[1])
    fmt = lambda iv: f'[{decimal(iv[0])}, {decimal(iv[1])}]'
    nodes = {
        'D': ((3.15, 4.0), 'D = 2c − (2 + θ − φ) s', h5, f'h5 · {steps["h5"][0]}'),
        'h1': ((1.0, 2.75), '2c', h1, f'h1 · {steps["h1"][0]}'),
        'h4': ((4.7, 2.75), '(2 + θ − φ) s', h4, f'h4 · {steps["h4"][0]}'),
        'c': ((1.0, 1.5), 'c = cos φ', c, 'hc'),
        'h3': ((3.55, 1.5), '2 + θ − φ', h3, f'h3 · {steps["h3"][0]}'),
        's': ((6.05, 1.5), 's = sin φ', s, 'hs'),
        'h2': ((2.45, 0.25), '2 + θ', h2, f'h2 · {steps["h2"][0]}'),
        'phi': ((4.75, 0.25), 'φ', phi, 'hφ'),
        'th': ((2.45, -1.0), 'θ', th, 'hθ'),
    }
    edges = [('D', 'h1'), ('D', 'h4'), ('h1', 'c'), ('h4', 'h3'), ('h4', 's'), ('h3', 'h2'),
             ('h3', 'phi'), ('h2', 'th')]
    f = Figure(-0.25, 7.3, -1.55, 4.5, 100)
    W, Hh = 2.25, 0.62
    for a, b in edges:
        (xa, ya), (xb, yb) = nodes[a][0], nodes[b][0]
        f.line((xb, yb + Hh / 2), (xa, ya - Hh / 2 - 0.22), stroke=FAINT, width=1.3, arrow=True)
    for key, ((x, y), expr, iv, step) in nodes.items():
        leaf = key in ('c', 's', 'phi', 'th')
        f.polygon([(x - W / 2, y - Hh / 2), (x + W / 2, y - Hh / 2), (x + W / 2, y + Hh / 2),
                   (x - W / 2, y + Hh / 2)], fill=FILLS[2] if leaf else FILLS[0],
                  stroke=GREEN if leaf else BLUE, width=1.2)
        f.text((x, y + 0.13), expr, size=13.5)
        f.text((x, y - 0.14), fmt(iv), size=12, italic=False)
        f.text((x, y - Hh / 2 - 0.12), step, size=11, italic=False, color=FAINT)
    return save(f, 'appendix-b/enclosure',
                "The interval chain of the generated lemma rom_D_box: from enclosures of φ, θ, "
                "c = cos φ and s = sin φ on the box (green), five steps h1 to h5, each one interval "
                "lemma, enclose D = 2c − (2 + θ − φ)s in [1.8923884882, 1.8970660986]")


def fig_slack():
    """Figure B.3: true ranges of the partial derivatives of G on the box, their proved enclosures, and
    the bounds that make G a contraction."""
    text, fix = NUM.read_text(), FIX.read_text()
    names = ['rom_G1φ', 'rom_G1θ', 'rom_G2φ', 'rom_G2θ']
    encl = [lean_enclosure(text, n + '_box') for n in names]
    bnd = [float(re.search(r'theorem ' + n + r'_bound\b.*?\|\s*≤\s*([\d.]+)', fix, re.S).group(1))
           for n in names]
    # True ranges, by central differences on a grid of the box (float64; G is smooth).
    a, b = np.meshgrid(np.linspace(0.039, 0.04, 101), np.linspace(0.68, 0.69, 101))
    m = [[float(x) for x in row] for row in MNEG]
    def G(ph, th):
        h1, h2 = H_np(ph, th)
        return ph + m[0][0] * h1 + m[0][1] * h2, th + m[1][0] * h1 + m[1][1] * h2
    e = 1e-7
    d = {}
    for j, (da, db) in enumerate([(e, 0), (0, e)]):
        gp, gm = G(a + da, b + db), G(a - da, b - db)
        for i in range(2):
            d[(i, j)] = (gp[i] - gm[i]) / (2 * e)
    true = [d[(0, 0)], d[(0, 1)], d[(1, 0)], d[(1, 1)]]
    rows = []
    for k in range(4):
        lo, hi = float(true[k].min()), float(true[k].max())
        L, U = float(encl[k][0]), float(encl[k][1])
        assert L <= lo and hi <= U and max(-L, U) <= bnd[k], k
        # The caption: the enclosures are 5 to 17 times wider than the true ranges.
        assert 4.5 < (U - L) / (hi - lo) < 17.5, (k, (U - L) / (hi - lo))
        rows.append((lo, hi, L, U, bnd[k]))
    assert bnd[0] + bnd[1] <= 0.5 and bnd[2] + bnd[3] <= 0.5
    sx = 1000
    f = Figure(-0.47, 0.36, -0.045, 0.27, sx)
    labels = ['∂G₁/∂φ', '∂G₁/∂θ', '∂G₂/∂φ', '∂G₂/∂θ']
    if not PLAIN:
        labels = [f'∂G<tspan dy="4.5" font-size="10.2">{i}</tspan><tspan dy="-4.5">/∂{v}</tspan>'
                  for i, v in [(1, 'φ'), (1, 'θ'), (2, 'φ'), (2, 'θ')]]
    for k, (lo, hi, L, U, B) in enumerate(rows):
        y = 0.24 - 0.06 * k
        f.polygon([(L, y - 0.012), (U, y - 0.012), (U, y + 0.012), (L, y + 0.012)], fill=FILLS[0],
                  stroke=BLUE, width=1)
        f.polygon([(lo, y - 0.012), (hi, y - 0.012), (hi, y + 0.012), (lo, y + 0.012)], fill=ORANGE,
                  stroke=ORANGE, width=1)
        for sgn in (-1, 1):
            f.line((sgn * B, y - 0.02), (sgn * B, y + 0.02), stroke=INK, width=1.8)
        f.text((-0.44, y), labels[k], size=14, anchor='start')
        f.text((B + 0.008, y + 0.018), f'±{B:g}', size=11.5, anchor='start', italic=False)
    f.line((-0.32, -0.005), (0.32, -0.005), stroke=FAINT, width=1)
    for xv in (-0.3, -0.2, -0.1, 0, 0.1, 0.2, 0.3):
        f.line((xv, -0.005), (xv, -0.012), stroke=FAINT, width=1)
        f.text((xv, -0.03), f'{xv:g}', size=11.5, italic=False)
    return save(f, 'appendix-b/slack',
                "For each partial derivative of the Newton-type map G on the box: its true range "
                "(orange), the enclosure that interval arithmetic proves (light blue), and the bound "
                "used for the contraction (black ticks: 0.03, 0.012, 0.3, 0.16)")


def main():
    check_phases()
    sofa = outline_exact(80)
    area = shoelace(sofa)
    assert abs(area - 2.2195316688719) < 1e-5, area
    fig_phases(sofa)
    fig_contacts(sofa)
    fig_pieces(sofa)
    fig_box()
    fig_cap()
    fig_principle()
    fig_niche()
    fig_contraction()
    fig_enclosure()
    fig_slack()


if __name__ == '__main__':
    main()
