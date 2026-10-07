#!/usr/bin/env python3
"""The figures of Chapter 13 (the bridge to formal-conjectures), in docs/proof/figures/13-bridge/,
and of Appendix A (Gerver's four constants), in docs/proof/figures/appendix-a/.

    python3 scripts/figures/fig_bridge.py

Formal-conjectures' Gerver's sofa is computed from its own definitions
(`MovingSofaBridge/Defs.lean`): the radius `GerversSofa.r`, the integrals `GerversSofa.x`,
`GerversSofa.y` and the path `GerversSofa.p`, from Gerver's four constants (gerver.py). The script
checks the facts that the captions state: rotating formal-conjectures' path by the angle gives
Romik's path (gerver.path), the integrals are the coordinates of Romik's contact points, the moving
sets stay in the hallway, and the residuals of Appendix A vanish at Gerver's constants with the
signs the appendix proves.
"""
import math

import mpmath as mp
import numpy as np

import gerver as gv
from sofa_figures import Figure, INK, FAINT, WALL, FLOOR, COLORS, FILLS, GREY, sb

PI = math.pi
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
MONO = "ui-monospace, SFMono-Regular, Menlo, Consolas, 'DejaVu Sans Mono', monospace"
A, B, PHI, THETA = gv.A, gv.B, gv.PHI, gv.THETA
BREAKS = (PHI, THETA, PI / 2 - THETA, PI / 2 - PHI)
K31 = gv.k3[0]

# ---------------------------------------------------------------------------------------------
# Formal-conjectures' Gerver's sofa (`FormalConjectures.MovingSofa.GerversSofa`)
# ---------------------------------------------------------------------------------------------


def radius(a):
    """`GerversSofa.r`: the radius, piecewise in the angle, with the breakpoints in BREAKS."""
    if a <= PHI:
        return 0.5
    if a <= THETA:
        return (1 + A + a - PHI) / 2
    if a <= PI / 2 - THETA:
        return A + a - PHI
    if a <= PI / 2 - PHI:
        return B - (PI / 2 - a - PHI) * (1 + A) / 2 - (PI / 2 - a - PHI) ** 2 / 4
    return 0.0


def integral(w, a, b):
    """The integral of r(t) w(t) from a to b, split at the breakpoints of r."""
    if a == b:
        return 0.0
    sign = 1.0
    if a > b:
        a, b, sign = b, a, -1.0
    pts = [a] + [c for c in BREAKS if a < c < b] + [b]
    return sign * float(sum(mp.quad(lambda t: radius(float(t)) * w(float(t)), [lo, hi])
                            for lo, hi in zip(pts, pts[1:])))


def fc_x(a):
    """`GerversSofa.x`."""
    return 1 - integral(math.cos, a, PI / 2 - PHI)


def fc_y(a):
    """`GerversSofa.y`."""
    return integral(math.sin, a, PI / 2 - PHI)


X0 = fc_x(0)


def fc_path(a):
    """`GerversSofa.p`, in coordinates."""
    c, s = math.cos(a), math.sin(a)
    p1 = c - 1 if a <= PHI else fc_x(PI / 2 - a) * c + fc_y(PI / 2 - a) * s - 1
    if a <= PI / 2 - PHI:
        p2 = fc_y(a) * c - (4 * X0 - 2 - fc_x(a)) * s - 1
    else:
        p2 = -(4 * X0 - 3) * s - 1
    return (p1, p2)


def contact_C(a):
    """Romik's contact point C(a), from the integrals: (2 κ₃₁ − x(a), y(a))."""
    return (2 * K31 - fc_x(a), fc_y(a))


def contact_A(a):
    """Romik's contact point A(a), from the integrals: (x(π/2 − a), y(π/2 − a))."""
    return (fc_x(PI / 2 - a), fc_y(PI / 2 - a))


def check_formal_conjectures():
    """Formal-conjectures' path and contact points agree with Romik's (Section 13.5)."""
    assert abs(2 * K31 - (4 * X0 - 2)) < 1e-12
    h = 1e-6
    for a in np.linspace(0, PI / 2, 41):
        q, x = gv.rot(a, fc_path(a)), gv.path(a)
        assert abs(q[0] - x[0]) + abs(q[1] - x[1]) < 1e-9, (a, q, x)
        if min(abs(a - c) for c in BREAKS + (0, PI / 2)) > 1e-3:
            d = [(u - v) / (2 * h) for u, v in zip(gv.path(a + h), gv.path(a - h))]
            uu, vv = (math.cos(a), math.sin(a)), (-math.sin(a), math.cos(a))
            beta = d[0] * vv[0] + d[1] * vv[1]
            alpha = d[0] * uu[0] + d[1] * uu[1]
            C = (x[0] - beta * uu[0] + vv[0], x[1] - beta * uu[1] + vv[1])
            Ap = (x[0] + alpha * vv[0] + uu[0], x[1] + alpha * vv[1] + uu[1])
            for P, Q in ((C, contact_C(a)), (Ap, contact_A(a))):
                assert abs(P[0] - Q[0]) + abs(P[1] - Q[1]) < 1e-6, (a, P, Q)
    assert max(abs(v) for v in fc_path(0)) < 1e-12


# ---------------------------------------------------------------------------------------------
# Drawing helpers
# ---------------------------------------------------------------------------------------------


def esc(s):
    """The text s, escaped for SVG."""
    return s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')


def clip_polygon(pts, box):
    """Sutherland–Hodgman: the polygon pts clipped to the box (xmin, xmax, ymin, ymax)."""
    xmin, xmax, ymin, ymax = box

    def at_x(p, q, x):
        return (x, p[1] + (q[1] - p[1]) * (x - p[0]) / (q[0] - p[0]))

    def at_y(p, q, y):
        return (p[0] + (q[0] - p[0]) * (y - p[1]) / (q[1] - p[1]), y)

    edges = [(lambda p: p[0] >= xmin, lambda p, q: at_x(p, q, xmin)),
             (lambda p: p[0] <= xmax, lambda p, q: at_x(p, q, xmax)),
             (lambda p: p[1] >= ymin, lambda p, q: at_y(p, q, ymin)),
             (lambda p: p[1] <= ymax, lambda p, q: at_y(p, q, ymax))]
    out = list(pts)
    for inside, cut in edges:
        if not out:
            break
        cur, out = out, []
        for i, q in enumerate(cur):
            p = cur[i - 1]
            if inside(q):
                if not inside(p):
                    out.append(cut(p, q))
                out.append(q)
            elif inside(p):
                out.append(cut(p, q))
    return out


def clip_segment(p, q, box):
    """Liang–Barsky: the segment pq clipped to the box, or None."""
    xmin, xmax, ymin, ymax = box
    t0, t1 = 0.0, 1.0
    dx, dy = q[0] - p[0], q[1] - p[1]
    for num, den in ((p[0] - xmin, -dx), (xmax - p[0], dx), (p[1] - ymin, -dy), (ymax - p[1], dy)):
        if den == 0:
            if num < 0:
                return None
            continue
        r = num / den
        if den < 0:
            t0 = max(t0, r)
        else:
            t1 = min(t1, r)
    if t0 > t1:
        return None
    return (p[0] + t0 * dx, p[1] + t0 * dy), (p[0] + t1 * dx, p[1] + t1 * dy)


def clip_polyline(pts, box):
    """The polyline pts clipped to the box, as a list of polylines."""
    pieces, cur = [], []
    for p, q in zip(pts, pts[1:]):
        seg = clip_segment(p, q, box)
        if seg is None:
            if cur:
                pieces.append(cur)
                cur = []
            continue
        a, b = seg
        if cur and math.dist(cur[-1], a) < 1e-9:
            cur.append(b)
        else:
            if cur:
                pieces.append(cur)
            cur = [a, b]
    if cur:
        pieces.append(cur)
    return pieces


def moved_hallway(c, t, far=40.0):
    """The hallway c + R_t L: its floor, its outer walls and its inner walls."""
    def m(pts):
        return [gv.add(c, gv.rot(t, q)) for q in pts]
    floor = m([(-far, 0), (0, 0), (0, -far), (1, -far), (1, 1), (-far, 1)])
    outer = m([(-far, 1), (1, 1), (1, -far)])
    inner = m([(-far, 0), (0, 0), (0, -far)])
    return floor, outer, inner


def draw_hallway(f, c, t, box, floor=FLOOR, wall=WALL, width=2.6, dash=None, fill=True):
    """The hallway c + R_t L, clipped to the box: its floor (if fill) and its four walls."""
    fl, outer, inner = moved_hallway(c, t)
    if fill:
        f.polygon(clip_polygon(fl, box), fill=floor, stroke='none', width=0)
    for wall_pts in (outer, inner):
        for piece in clip_polyline(wall_pts, box):
            f.polyline(piece, stroke=wall, width=width, dash=dash)


def mono(f, c, s, size=12, anchor='middle', color=INK):
    """A label in a monospace font, for Lean names."""
    x, y = f.p(*c)
    f.add(f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size}" font-family="{MONO}" '
          f'fill="{color}" text-anchor="{anchor}" dominant-baseline="middle">{esc(s)}</text>')


def arc(c, r, a0, a1, n=60):
    """The arc of the circle of radius r about c from the angle a0 to a1, as a polyline."""
    return [(c[0] + r * math.cos(a), c[1] + r * math.sin(a)) for a in np.linspace(a0, a1, n)]


def arrowhead(f, tip, direction, size=0.09, color=INK):
    """A filled arrowhead at tip, pointing along direction (in figure units)."""
    d = math.hypot(*direction)
    ux, uy = direction[0] / d, direction[1] / d
    back = (tip[0] - size * ux, tip[1] - size * uy)
    left = (back[0] - 0.45 * size * uy, back[1] + 0.45 * size * ux)
    right = (back[0] + 0.45 * size * uy, back[1] - 0.45 * size * ux)
    f.polygon([tip, left, right], fill=color, stroke=color, width=0.8)


def sofa_outline():
    """Gerver's sofa as a polygon (gerver.py), checked to stay in the hallway as it moves."""
    pts = gv.outline(700, 8000)
    for t in np.linspace(0, PI / 2, 7):
        for x, y in gv.place(t, pts[::9]):
            assert x <= 1 + 1e-6 and y <= 1 + 1e-6 and (x >= -1e-6 or y >= -1e-6), (t, x, y)
    return pts


# ---------------------------------------------------------------------------------------------
# Chapter 13
# ---------------------------------------------------------------------------------------------


def conventions(sofa):
    """Figure 13.1: the hallway at the angle t, placed in the two conventions."""
    t = 0.7
    x, p = gv.path(t), fc_path(t)
    q = gv.rot(t, p)
    assert abs(q[0] - x[0]) + abs(q[1] - x[1]) < 1e-9
    box = (-2.55, 1.75, -1.2, 2.3)
    gap = 4.7
    f = Figure(box[0], box[1] + gap, box[2], box[3] + 0.4, 80)
    for k, title in enumerate(('Baek, Romik: rotate by t, then translate by x(t)',
                               'formal-conjectures: translate by p(t), then rotate by t')):
        dx = k * gap
        bx = (box[0] + dx, box[1] + dx, box[2], box[3])
        # The hallway x(t) + R_t L = R_t (L + p(t)) that touches the sofa.
        draw_hallway(f, (x[0] + dx, x[1]), t, bx)
        f.polygon([(u + dx, v) for u, v in sofa], fill=FILLS[0], stroke=BLUE, width=1.6)
        f.text(((box[0] + box[1]) / 2 + dx, box[3] + 0.22), esc(title), size=14, italic=False)
        if k == 0:
            # L rotated about O (dashed), then translated by x(t).
            draw_hallway(f, (0, 0), t, bx, wall=FAINT, width=1.4, dash='6 4', fill=False)
            f.line((0, 0), (x[0] * 0.9, x[1] * 0.9), stroke=ORANGE, width=2.0)
            arrowhead(f, x, x, size=0.14, color=ORANGE)
            f.text((-1.6, -0.8), sb('R', 't', ' L'), size=15, color=FAINT)
            f.text((-2.05, 1.95), sb('x(t) + R', 't', ' L'), size=15, color=WALL)
        else:
            # L translated by p(t) (dashed), then rotated about O by t.
            draw_hallway(f, (p[0] + dx, p[1]), 0, bx, wall=FAINT, width=1.4, dash='6 4',
                         fill=False)
            rad = math.hypot(*p)
            a0, a1 = math.atan2(p[1], p[0]), math.atan2(x[1], x[0])
            f.polyline(arc((dx, 0), rad, a0, a1 - 0.1), stroke=GREEN, width=2.0)
            arrowhead(f, (x[0] + dx, x[1]), (-math.sin(a1), math.cos(a1)), size=0.14,
                      color=GREEN)
            f.line((dx, 0), (p[0] + dx, p[1]), stroke=GREEN, width=2.0)
            f.dot((p[0] + dx, p[1]), r=3.4, fill=GREEN)
            f.text((p[0] + dx + 0.32, p[1] - 0.13), 'p(t)', size=15, color=GREEN)
            f.text((0.45 + dx, -1.08), 'L + p(t)', size=14, color=FAINT)
            f.text((-2.0 + dx, 1.95), sb('R', 't', '(L + p(t))'), size=15, color=WALL)
        f.dot((x[0] + dx, x[1]), r=3.4, fill=ORANGE)
        f.text((x[0] + dx - 0.36, x[1] + 0.1), 'x(t)', size=15, color=ORANGE)
        f.dot((dx, 0), r=2.8)
        f.text((dx - 0.17, -0.17), 'O', size=14)
    return f.save('13-bridge/conventions',
                  "Two panels with Gerver's sofa and the hallway at the angle t = 0.7 that touches "
                  "it. Left: the hallway L is rotated by t about the origin O (dashed), then "
                  "translated by Romik's inner corner x(t). Right: L is translated by "
                  "formal-conjectures' point p(t) (dashed), then rotated by t about O, which "
                  "carries p(t) to x(t). Both give the same hallway")


def lift_motion(s):
    """An example of a path in E(2) from the identity: a pennant slides along the middle line of
    the hallway and spins clockwise by five quarter turns. Returns the angle and the image of the
    pennant's centre at time s."""
    d = 5.6 * s
    centre = (-2.6 + d, 0.5) if d <= 3.1 else (0.5, 0.5 - (d - 3.1))
    angle = -2.5 * PI * (3 * s * s - 2 * s ** 3)
    return angle, centre


PENNANT = [(0.4, 0.0), (-0.26, 0.21), (-0.16, 0.0), (-0.26, -0.21)]


def angle_lift():
    """Figure 13.2: a path in E(2) from the identity, and the lift of its angle."""
    box = (-3.15, 1.25, -2.4, 1.3)
    gx, gw, ky = 2.15, 3.2, 0.29   # the graph: s in [0, 1] -> [gx, gx + gw], angle -> ky * angle
    f = Figure(box[0], gx + gw + 0.8, box[2], box[3], 78)
    draw_hallway(f, (0, 0), 0, box)
    # The pennant lies in the disk of radius 1/2 about its centre, and the centre moves along the
    # middle line of the hallway, so the pennant stays in the hallway at every angle.
    assert max(math.hypot(*q) for q in PENNANT) < 0.5
    for s in np.linspace(0, 1, 201):
        c = lift_motion(s)[1]
        assert ((abs(c[1] - 0.5) < 1e-12 and c[0] <= 0.5)
                or (abs(c[0] - 0.5) < 1e-12 and c[1] <= 0.5))
    n = 9
    for k in range(n):
        s = k / (n - 1)
        ang, c = lift_motion(s)
        pts = [gv.add(c, gv.rot(ang, q)) for q in PENNANT]
        op = 0.35 + 0.65 * k / (n - 1)
        f.polygon(pts, fill=FILLS[0], stroke=BLUE, width=1.3, opacity=op, stroke_opacity=op)
    f.text((-2.6, -0.22), 't = 0', size=13, color=BLUE)
    f.text((0.5 - 0.62, lift_motion(1)[1][1]), 't = 1', size=13, color=BLUE, anchor='end')
    # The graph of the lifted angle and of the principal argument of the first column.
    ss = np.linspace(0, 1, 400)
    lift = np.array([lift_motion(s)[0] for s in ss])
    arg = np.array([math.atan2(math.sin(a), math.cos(a)) for a in lift])
    assert abs(lift[-1] + 2.5 * PI) < 1e-12 and np.all(np.diff(lift) <= 1e-12)
    jumps = np.nonzero(np.abs(np.diff(arg)) > PI)[0]
    assert len(jumps) == 1   # the principal argument jumps once, where θ(s) = −π
    X = gx + gw * ss
    f.line((gx, 0), (gx + gw + 0.15, 0), stroke=INK, width=1.0, arrow=True)
    f.line((gx, -2.5 * PI * ky - 0.15), (gx, PI * ky + 0.3), stroke=INK, width=1.0, arrow=True)
    for m, lab in ((1, 'π'), (-1, '−π'), (-2, '−2π')):
        f.line((gx - 0.05, m * PI * ky), (gx + gw, m * PI * ky), stroke=GREY, width=0.8)
        f.text((gx - 0.1, m * PI * ky), lab, size=12, anchor='end', italic=False)
    f.text((gx - 0.1, 0), '0', size=12, anchor='end', italic=False)
    f.line((gx + gw, -0.05), (gx + gw, 0.05), stroke=INK, width=1.0)
    f.text((gx + gw, 0.17), '1', size=12, italic=False)
    f.text((gx + gw + 0.28, 0), 't', size=14)
    f.polyline(list(zip(X, ky * lift)), stroke=ORANGE, width=2.4)
    j = jumps[0]
    f.line((X[j], ky * arg[j]), (X[j + 1], ky * arg[j + 1]), stroke=FAINT, width=1.0, dash='1 3')
    lo = 0
    for k in [j, len(ss) - 1]:
        f.polyline(list(zip(X[lo:k + 1], ky * arg[lo:k + 1])), stroke=INK, width=1.4, dash='5 4')
        lo = k + 1
    f.dot((gx + gw, ky * lift[-1]), r=3, fill=ORANGE)
    f.text((gx + gw + 0.1, ky * lift[-1]), '−5π/2', size=12, anchor='start', italic=False,
           color=ORANGE)
    f.text((gx + 1.75, -1.62), 'ϑ(t)', size=15, color=ORANGE)
    f.text((gx + 2.05, 0.66), 'arg', size=14, italic=False)
    return f.save('13-bridge/angle-lift',
                  "Left: a continuous path of rigid motions m(t), t from 0 to 1, applied to a "
                  "pennant in the hallway: it slides along the horizontal side, turns the corner "
                  "and leaves along the vertical side, spinning clockwise by five quarter turns; "
                  "the pennant is drawn at nine times, darker as t grows. Right: the lifted "
                  "angle ϑ(t), a continuous function decreasing from 0 to −5π/2, and the "
                  "principal argument of the first column of m(t), dashed, which agrees with it "
                  "until it reaches −π and then jumps to π")


def half_disk(c, n=90):
    """The half-disk of radius 1 above the diameter centred at c."""
    return [(c[0] + math.cos(a), c[1] + math.sin(a)) for a in np.linspace(0, PI, n)]


def slide():
    """Figure 13.3: the motion of formal-conjectures built from a motion of Baek's."""
    c0 = (2.2, 0.0)
    sofa = half_disk((-c0[0], 0.0))       # the sofa S, in the horizontal side
    start = half_disk((0.0, 0.0))         # s + c(0), where Baek's motion starts
    later = [gv.rot(-PI / 4, q) for q in start]
    box = (-3.55, 1.3, -1.45, 1.35)
    f = Figure(box[0], box[1], box[2], box[3], 100)
    draw_hallway(f, (0, 0), 0, box)
    # Baek's motion of S: Φ_σ(q) = R_{−πσ/2}(q + c(0)); it starts at the translation by c(0).
    for sig in np.linspace(0, 1, 41):
        for q in sofa:
            u, v = gv.rot(-PI / 2 * sig, gv.add(q, c0))
            assert u <= 1 + 1e-12 and v <= 1 + 1e-12 and (u >= -1e-12 or v >= -1e-12), (sig, u, v)
    for u, v in sofa:   # S lies in the horizontal side, and so do the points of the slide
        assert u <= 1 and 0 <= v <= 1
    f.polygon(later, fill=FILLS[0], stroke=BLUE, width=1.2, opacity=0.4, stroke_opacity=0.55,
              dash='5 4')
    f.polygon(sofa, fill='none', stroke=BLUE, width=1.6, dash='6 4')
    f.polygon(start, fill=FILLS[0], stroke=BLUE, width=1.8, opacity=0.9)
    f.line((-c0[0], 0.42), (-0.08, 0.42), stroke=INK, width=1.5, arrow=True)
    f.text((-1.1, 0.58), 'c(0)', size=15)
    f.dot((-c0[0], 0.42), r=2.6)
    f.text((-2.2, 0.15), 'S', size=16, color=BLUE)
    f.text((0.38, 0.15), 'S + c(0)', size=15, color=BLUE)
    f.text((0.5, -1.2), sb('Φ', '1/2', '(S)'), size=15, color=BLUE)
    f.text((-3.3, 0.5), sb('H', 'L'), size=15, color=WALL)
    f.dot((0, 0), r=2.6)
    f.text((-0.15, -0.15), 'O', size=14)
    return f.save('13-bridge/slide',
                  "The hallway with a sofa S, a half-disk of radius 1, in its horizontal side "
                  "(dashed outline); the translate S + c(0), where a motion of Baek's paper "
                  "starts, against the inner corner O (solid); the arrow c(0) between them; and "
                  "the sofa halfway through that motion, turned by π/4 about O (faint)")


def radius_figure(sofa):
    """Figure 13.4: the radius r(α) of formal-conjectures and Romik's contact point C."""
    ka, kr = 3.55, 1.2          # the graph: α -> ka α, r -> kr r
    oy = 1.65                   # the height of the graph's axis
    dx = 3.1                    # the sofa is drawn shifted by dx, below the graph
    f = Figure(-0.75, ka * PI / 2 + 0.55, -0.4, oy + kr * 1.5 + 0.2, 100)
    f.line((0, oy), (ka * PI / 2 + 0.3, oy), stroke=INK, width=1.0, arrow=True)
    f.line((0, oy), (0, oy + kr * 1.5 + 0.08), stroke=INK, width=1.0, arrow=True)
    f.text((ka * PI / 2 + 0.42, oy), 'α', size=15)
    f.text((-0.1, oy + kr * 1.5 + 0.08), 'r', size=15, anchor='end')
    for val in (0.5, 1.0):
        f.line((-0.05, oy + kr * val), (0.05, oy + kr * val), stroke=INK, width=1.0)
        f.text((-0.1, oy + kr * val), f'{val:g}', size=12, anchor='end', italic=False)
    pieces = [(0, PHI), (PHI, THETA), (THETA, PI / 2 - THETA), (PI / 2 - THETA, PI / 2 - PHI),
              (PI / 2 - PHI, PI / 2)]
    for lo, hi in pieces:
        al = np.linspace(lo, hi, 60)
        rs = [radius(min(max(a, lo + 1e-12), hi - 1e-12)) for a in al]
        f.polyline([(ka * a, oy + kr * r) for a, r in zip(al, rs)], stroke=ORANGE, width=2.4)
    for c, lab, anchor in zip(BREAKS, ['φ', 'θ', 'π/2 − θ', 'π/2 − φ'],
                              ['middle', 'middle', 'middle', 'end']):
        top = max(radius(c - 1e-12), radius(c + 1e-12))
        f.line((ka * c, oy), (ka * c, oy + kr * top), stroke=FAINT, width=0.9, dash='3 3')
        f.text((ka * c + (0.04 if anchor == 'end' else 0), oy - 0.17), esc(lab), size=13,
               anchor=anchor)
    f.text((ka * PI / 2 + 0.03, oy - 0.17), 'π/2', size=13, anchor='start')
    f.text((-0.03, oy - 0.17), '0', size=12, italic=False, anchor='end')
    # r jumps at φ, θ and π/2 − φ, and is continuous at π/2 − θ (Gerver's fourth equation).
    for c in BREAKS:
        jump = abs(radius(c - 1e-12) - radius(c + 1e-12))
        assert (jump < 1e-9) == (c == PI / 2 - THETA), (c, jump)
    # The sofa, with the contact points C (orange) and A (green) on its outer boundary.
    def sh(q):
        return (q[0] + dx, q[1])
    f.polygon([sh(q) for q in sofa], fill=FILLS[0], stroke=BLUE, width=1.4)
    al = np.linspace(0, PI / 2 - PHI, 160)
    cs = [contact_C(a) for a in al]
    as_ = [contact_A(PI / 2 - a) for a in al]
    top, _, _ = gv.bounds(np.array([c[0] for c in cs]), 8000)
    assert np.max(np.abs(top - np.array([c[1] for c in cs]))) < 2e-3   # C traces the boundary
    assert math.dist(contact_C(PHI), contact_C(0)) < 0.025
    f.polyline([sh(q) for q in cs], stroke=ORANGE, width=3.0)
    f.polyline([sh(q) for q in as_], stroke=GREEN, width=3.0)
    for c in (0.0, THETA, PI / 2 - THETA, PI / 2 - PHI):
        f.dot(sh(contact_C(c)), r=3.3, fill=ORANGE)
    f.text(sh(gv.add(contact_C(0.0), (0.0, 0.16))), 'C(0)', size=14, color=ORANGE)
    f.text(sh(gv.add(contact_C(THETA), (-0.1, 0.06))), 'C(θ)', size=14, color=ORANGE,
           anchor='end')
    f.text(sh(gv.add(contact_C(PI / 2 - THETA), (-0.1, -0.03))), 'C(π/2 − θ)', size=14,
           color=ORANGE, anchor='end')
    f.text(sh(gv.add(contact_C(PI / 2 - PHI), (0.0, -0.18))), 'C(π/2 − φ)', size=14,
           color=ORANGE)
    f.text(sh((0.83, 0.6)), 'A', size=15, color=GREEN, anchor='start')
    return f.save('13-bridge/radius',
                  "Above: the graph of formal-conjectures' radius r(α) for α from 0 to π/2: the "
                  "constant 1/2 up to φ, then two increasing linear pieces, a quadratic piece "
                  "up to π/2 − φ, and 0 after it; r jumps at φ, θ and π/2 − φ and is continuous "
                  "at π/2 − θ. Below: Gerver's sofa with Romik's contact point C(α) on its upper "
                  "left boundary (orange), from C(0) on the top edge down to the corner "
                  "C(π/2 − φ), with dots at the breakpoints θ and π/2 − θ, and its mirror image "
                  "A on the upper right boundary (green)")


def box(f, c, w, h, lines, color, fill, size=12):
    x0, y0 = f.p(c[0] - w / 2, c[1] + h / 2)
    f.add(f'<rect x="{x0:.1f}" y="{y0:.1f}" width="{w * f.s:.1f}" height="{h * f.s:.1f}" '
          f'rx="6" fill="{fill}" stroke="{color}" stroke-width="1.4"/>')
    n = len(lines)
    for i, line in enumerate(lines):
        mono(f, (c[0], c[1] + (n - 1 - 2 * i) * 0.085), line, size=size)


def dependencies():
    """Figure 13.5: how the twelve theorems of the Challenge depend on each other."""
    f = Figure(0, 10.6, 0.05, 4.05, 92)
    w, h = 1.95, 0.42
    baek = {'gerver_params_unique': 0.95, 'gerver_sofa_area': 3.05,
            'gerver_params_exists': 5.15, 'gerver_sofa_optimal': 7.3, 'gerver_sofa_unique': 9.5}
    fc = {'ABφθSpec.existsUnique': (1.1, ['GerversSofa.', 'ABφθSpec.existsUnique']),
          'isMovingSofa_gerversSofa': (3.75, ['isMovingSofa_', 'gerversSofa']),
          'sofaConstant_eq_volume_gerversSofa': (6.4, ['sofaConstant_eq_', 'volume_gerversSofa']),
          'volume_eq_sofaConstant_iff_congruent_gerversSofa':
              (9.1, ['volume_eq_sofaConstant_iff_', 'congruent_gerversSofa'])}
    bridge = {'gerversSofa_eq': 3.75, 'isMovingSofa_iff': 6.4, 'sofaConstant_eq': 9.1}
    yb, yf, yr = 3.35, 1.95, 0.55
    wf, hf = 2.45, 0.5
    # Arrows: the proof of the head in baek/Solution.lean uses the tail.
    uses = {'isMovingSofa_gerversSofa': (['gerver_params_exists', 'gerver_sofa_optimal'],
                                         ['isMovingSofa_iff', 'gerversSofa_eq']),
            'sofaConstant_eq_volume_gerversSofa': (['gerver_params_exists', 'gerver_sofa_optimal'],
                                                   ['sofaConstant_eq', 'gerversSofa_eq']),
            'volume_eq_sofaConstant_iff_congruent_gerversSofa':
                (['gerver_params_exists', 'gerver_sofa_optimal', 'gerver_sofa_unique'],
                 ['isMovingSofa_iff', 'sofaConstant_eq', 'gerversSofa_eq'])}

    def landings(hx, tails, xs):
        """Landing points on a box edge, spread in the order of the tails."""
        order = sorted(tails, key=lambda t: xs[t])
        k = len(order)
        return {t: hx + (0.0 if k == 1 else -0.6 + 1.2 * i / (k - 1)) for i, t in enumerate(order)}
    for head, (from_baek, from_bridge) in uses.items():
        hx = fc[head][0]
        top = landings(hx, from_baek, baek)
        for tail in from_baek:
            f.line((baek[tail], yb - h / 2), (top[tail], yf + hf / 2 + 0.03), stroke=BLUE,
                   width=1.1, arrow=True)
        bottom = landings(hx, from_bridge, bridge)
        for tail in from_bridge:
            f.line((bridge[tail], yr + h / 2), (bottom[tail], yf - hf / 2 - 0.03), stroke=GREEN,
                   width=1.1, arrow=True)
    # Gerver's constants define formal-conjectures' Gerver's sofa, which the bridge compares.
    f.line((fc['ABφθSpec.existsUnique'][0], yf - hf / 2),
           (bridge['gerversSofa_eq'] - w / 2 - 0.03, yr + 0.02),
           stroke=FAINT, width=1.3, dash='5 4', arrow=True)
    for name, x in baek.items():
        box(f, (x, yb), w, h, [name], BLUE, FILLS[0])
    for name, (x, lines) in fc.items():
        box(f, (x, yf), wf, hf, lines, ORANGE, FILLS[1])
    for name, x in bridge.items():
        box(f, (x, yr), w, h, [name], GREEN, FILLS[2])
    f.text((0.0, yb + 0.4), 'Baek', size=14, anchor='start', color=BLUE, italic=False)
    f.text((0.0, yf + 0.43), 'FormalConjectures.MovingSofa', size=14, anchor='start',
           color=ORANGE, italic=False)
    f.text((0.0, yr + 0.4), 'Bridge', size=14, anchor='start', color=GREEN, italic=False)
    return f.save('13-bridge/dependencies',
                  "A diagram of the twelve theorems of the Challenge in three rows: Baek's five "
                  "above, formal-conjectures' four in the middle, the bridge's three below. Arrows "
                  "lead from a theorem to the theorems of formal-conjectures whose proofs in "
                  "baek/Solution.lean use it: gerver_params_exists and gerver_sofa_optimal to the three "
                  "theorems about Gerver's sofa, gerver_sofa_unique to the congruence theorem, "
                  "isMovingSofa_iff to the first and the third of them, sofaConstant_eq to the "
                  "second and the third, and gerversSofa_eq to all three; a dashed arrow leads from "
                  "ABφθSpec.existsUnique, which defines Gerver's constants, to gerversSofa_eq. "
                  "gerver_params_unique and gerver_sofa_area have no arrows")


# ---------------------------------------------------------------------------------------------
# Appendix A: the functions of `MovingSofaBridge.GerverConstants`, in the angles (φ, θ)
# ---------------------------------------------------------------------------------------------


def den(f, t):
    return 3 * math.cos(f) - math.cos(t)


def num(f, t):
    return (t - f) * math.cos(t) + 3 * math.sin(f) - math.sin(t) - math.cos(t) + 1


def slope(f, t):
    return 1 + (t - f) / 2


def offset(f, t):
    return PI / 2 - f - t + (t - f) / 2 + (t - f) ** 2 / 4


def reduced_q(f, t):
    """`reducedQ` = den · F."""
    frame_den = math.cos(f) - slope(f, t) * math.sin(f)
    frame_offset = math.sin(f) * (1 + offset(f, t)) + (1 - math.cos(f)) / 2
    return num(f, t) * frame_den - den(f, t) * frame_offset


def res_F(f, t):
    """`firstResidual`: Gerver's third equation with A and B expressed through the angles."""
    a = num(f, t) / den(f, t)
    b = a * slope(f, t) + offset(f, t)
    return a * math.cos(f) - (b + 1) * math.sin(f) + (math.cos(f) - 1) / 2


def res_G(f, t):
    """`secondResidual`: Gerver's second equation with A and B expressed through the angles."""
    a = num(f, t) / den(f, t)
    b = a * slope(f, t) + offset(f, t)
    return (-3 * (1 - a - (t - f)) * math.sin(t) + (a - 1) * math.sin(f)
            + (1 - 2 * b) * math.cos(f) + 3 * math.cos(t))


def res_H(f, t):
    """`separatingResidual` H = G + (9/10) F."""
    return res_G(f, t) + 0.9 * res_F(f, t)


def bisect(g, lo, hi, n=80):
    glo = g(lo)
    assert glo * g(hi) < 0
    for _ in range(n):
        mid = (lo + hi) / 2
        if (g(mid) < 0) == (glo < 0):
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def zero_F(t):
    """The zero of F(·, θ) on [0, min(θ, 1/20)]: F decreases strictly in φ there."""
    return bisect(lambda f: res_F(f, t), 0.0, min(t, 0.05))


def zero_H(f):
    """The zero of H(φ, ·) on [φ, π/4], if any: H decreases strictly in θ there."""
    if res_H(f, PI / 4) > 0:
        return None
    return bisect(lambda t: res_H(f, t), f, PI / 4)


def check_appendix():
    """The residuals vanish at Gerver's constants, and the signs of Appendix A hold on a grid."""
    assert abs(res_F(PHI, THETA)) < 1e-12 and abs(res_H(PHI, THETA)) < 1e-12
    assert abs(reduced_q(PHI, THETA)) < 1e-12
    assert reduced_q(0.05, PI / 4) < 0
    for f in np.linspace(0, 0.05, 11):
        ts = np.linspace(f, PI / 4, 41)
        F = [res_F(f, t) for t in ts]
        H = [res_H(f, t) for t in ts]
        assert all(b >= a - 1e-15 for a, b in zip(F, F[1:]))   # F increases in θ
        assert all(b < a for a, b in zip(H, H[1:]))             # H decreases strictly in θ
    for t in np.linspace(0.05, PI / 4, 21):
        fs = np.linspace(0, 0.05, 21)
        F = [res_F(f, t) for f in fs]
        H = [res_H(f, t) for f in fs]
        assert all(b < a for a, b in zip(F, F[1:]))             # F decreases strictly in φ
        assert all(b <= a + 1e-15 for a, b in zip(H, H[1:]))    # H decreases in φ


SX = 14.0   # the horizontal stretch of the strip 0 ≤ φ ≤ 1/20 in Figures A.2 and A.3


def strip_axes(f):
    """The strip {0 ≤ φ ≤ 1/20, φ ≤ θ ≤ π/4}, stretched horizontally by SX, with its axes."""
    w = SX * 0.05
    f.polygon([(0, 0), (w, 0.05), (w, PI / 4), (0, PI / 4)], fill='#fbfbfc', stroke=INK, width=1.2)
    f.line((0, 0), (0, PI / 4 + 0.07), stroke=INK, width=1.0, arrow=True)
    f.line((0, 0), (w + 0.09, 0), stroke=INK, width=1.0, arrow=True)
    f.text((w + 0.13, 0), 'φ', size=15, anchor='start')
    f.text((-0.03, PI / 4 + 0.09), 'θ', size=15, anchor='end')
    for val, lab in ((0.0, '0'), (0.02, '0.02'), (0.04, '0.04'), (0.05, '1/20')):
        f.line((SX * val, -0.012), (SX * val, 0.0), stroke=INK, width=1.0)
        f.text((SX * val, -0.04), lab, size=12, italic=False)
    for val, lab in ((0.2, '0.2'), (0.4, '0.4'), (0.6, '0.6'), (PI / 4, 'π/4')):
        f.line((-0.012, val), (0.0, val), stroke=INK, width=1.0)
        f.text((-0.022, val), lab, size=12, italic=False, anchor='end')


def triangle():
    """Figure A.1: the domain triangle, the regions of the steps, and the zero set of Q."""
    f = Figure(-0.13, 1.12, -0.1, 0.9, 470)
    q4 = PI / 4
    f.polygon([(0, 0), (q4, q4), (0, q4)], fill=FILLS[1], stroke='none', width=0)
    f.polygon([(0.5, 0.5), (q4, q4), (0.5, q4)], fill=GREY, stroke='none', width=0)
    f.polygon([(0, 0), (0.05, 0.05), (0.05, q4), (0, q4)], fill=FILLS[0], stroke='none', width=0)
    f.polygon([(0, 0), (q4, q4), (0, q4)], fill='none', stroke=INK, width=1.3)
    f.line((0.5, 0.5), (0.5, q4), stroke=INK, width=1.0, dash='4 3')
    f.line((0.05, 0.05), (0.05, q4), stroke=GREEN, width=2.6)
    # The two edges without solutions (§A.2).
    f.line((0, 0), (0, q4), stroke=PURPLE, width=3.0)
    f.line((0, 0), (q4, q4), stroke=PURPLE, width=3.0)
    ts = np.linspace(0.0, q4, 80)
    f.polyline([(zero_F(t), t) for t in ts[1:]], stroke=INK, width=1.6)
    # Q is negative on the part φ ≥ 1/20 of the triangle (checked on a grid).
    for x in np.linspace(0.05, q4, 30):
        for t in np.linspace(x, q4, 30):
            assert reduced_q(x, t) < 0, (x, t)
    f.dot((PHI, THETA), r=3.6, fill=INK)
    f.dot((0.05, q4), r=3.6, fill=GREEN)
    # Axes.
    f.line((0, 0), (q4 + 0.08, 0), stroke=INK, width=1.0, arrow=True)
    f.text((q4 + 0.11, 0), 'φ', size=15, anchor='start')
    for val, lab in ((0.05, '1/20'), (0.5, '1/2'), (q4, 'π/4')):
        f.line((val, -0.01), (val, 0.0), stroke=INK, width=1.0)
        f.text((val, -0.04), lab, size=12, italic=False)
    f.text((0, -0.04), '0', size=12, italic=False)
    f.text((-0.02, q4), 'π/4', size=12, italic=False, anchor='end')
    f.text((-0.02, 0.0), '0', size=12, italic=False, anchor='end')
    f.text((-0.03, 0.4), 'θ', size=15, anchor='end')
    # Labels, outside the thin strip.
    f.text((0.3, 0.6), '∂Q/∂φ &lt; 0', size=14, italic=False)
    f.text((0.08, 0.68), '(φ, θ)', size=13, anchor='start')
    f.line((0.62, 0.72), (0.81, 0.62), stroke=INK, width=1.0)
    f.text((0.82, 0.62), 'φ ≥ 1/2: no solution', size=13, italic=False, anchor='start')
    f.line((0.05, 0.84), (0.05, q4 + 0.01), stroke=GREEN, width=1.0)
    f.text((0.07, 0.86), 'Q(1/20, π/4) &lt; 0', size=13, italic=False, anchor='start',
           color=GREEN)
    zq = (zero_F(0.45), 0.45)
    f.line(zq, (0.16, 0.45), stroke=INK, width=1.0)
    f.text((0.17, 0.45), 'Q = 0', size=13, italic=False, anchor='start')
    f.line((0.05, 0.3), (0.43, 0.2), stroke=GREEN, width=1.0)
    f.text((0.44, 0.2), 'φ = 1/20: ∂Q/∂θ &gt; 0', size=13, italic=False, anchor='start',
           color=GREEN)
    f.line((0.025, 0.12), (0.43, 0.1), stroke=BLUE, width=1.0)
    f.text((0.44, 0.1), 'φ ≤ 1/20: the signs of §A.8', size=13, italic=False, anchor='start',
           color=BLUE)
    f.text((0.4, 0.34), 'φ = θ', size=13, italic=False, color=PURPLE, anchor='start')
    return f.save('appendix-a/triangle',
                  "The triangle 0 ≤ φ ≤ θ ≤ π/4 in the (φ, θ)-plane. Its edges φ = 0 and φ = θ "
                  "(purple) carry no solution. On the part φ ≤ 1/2 (orange) ∂Q/∂φ is negative, "
                  "and the corner φ ≥ 1/2 (grey) has no solution. On the segment φ = 1/20 "
                  "(green) Q increases in θ up to a negative value at θ = π/4. In the thin strip "
                  "φ ≤ 1/20 (blue) the partial derivatives of F and H have their signs; the zero "
                  "set of Q, a curve from the origin to the top edge, lies in it, and Gerver's "
                  "angles (φ, θ) are a point of it")


def zero_sets():
    """Figure A.2: the zero sets of F and H in the strip, which meet once."""
    f = Figure(-0.2, SX * 0.05 + 0.32, -0.08, PI / 4 + 0.13, 440)
    strip_axes(f)
    ts = np.linspace(0.0, PI / 4, 200)[1:]
    zf = [(SX * zero_F(t), t) for t in ts]
    fs = np.linspace(0.0, 0.05, 200)
    zh = [(SX * x, zero_H(x)) for x in fs if zero_H(x) is not None]
    f.polyline(zf, stroke=BLUE, width=2.2)
    f.polyline(zh, stroke=ORANGE, width=2.2)
    # The curves cross exactly once, at Gerver's angles.
    side = [res_H(zero_F(t), t) for t in ts]
    assert sum(1 for a, b in zip(side, side[1:]) if a * b < 0) == 1
    f.dot((SX * PHI, THETA), r=4, fill=INK)
    f.text((SX * PHI + 0.03, THETA - 0.035), '(φ, θ)', size=14, anchor='start')
    f.text((SX * zero_F(0.3) - 0.03, 0.31), 'F = 0', size=14, color=BLUE, anchor='end')
    f.text((SX * 0.0149, PI / 4 + 0.03), 'H = 0', size=14, color=ORANGE, anchor='start')
    f.text((SX * 0.005, 0.66), 'F &gt; 0', size=13, color=BLUE, italic=False, anchor='start')
    f.text((SX * 0.033, 0.4), 'F &lt; 0', size=13, color=BLUE, italic=False)
    f.text((SX * 0.03, 0.757), 'H &lt; 0', size=13, color=ORANGE, italic=False)
    f.text((SX * 0.033, 0.5), 'H &gt; 0', size=13, color=ORANGE, italic=False)
    return f.save('appendix-a/zero-sets',
                  "The strip 0 ≤ φ ≤ 1/20, φ ≤ θ ≤ π/4, stretched horizontally. The zero set of F "
                  "(blue) rises from the origin to the top edge, with F positive to its left; "
                  "the zero set of H (orange) falls from the top edge to the right edge, with H "
                  "positive below it. They cross at one point, Gerver's angles (φ, θ)")


def uniqueness_argument():
    """Figure A.3: why no second solution lies higher."""
    f = Figure(-0.2, SX * 0.05 + 0.32, -0.08, PI / 4 + 0.13, 440)
    strip_axes(f)
    ts = np.linspace(0.0, PI / 4, 200)[1:]
    f.polyline([(SX * zero_F(t), t) for t in ts], stroke=BLUE, width=1.2, opacity=0.45)
    fs = np.linspace(0.0, 0.05, 200)
    f.polyline([(SX * x, zero_H(x)) for x in fs if zero_H(x) is not None], stroke=ORANGE,
               width=1.2, opacity=0.45)
    t2 = 0.735
    assert res_F(PHI, t2) > 0 and res_H(PHI, t2) < 0
    assert all(res_F(x, t2) > 0 for x in np.linspace(0, PHI, 50))
    assert all(res_H(x, t2) < 0 for x in np.linspace(PHI, 0.05, 50))
    w = SX * 0.05
    f.line((0, t2), (SX * PHI, t2), stroke=BLUE, width=2.8)
    f.line((SX * PHI, t2), (w, t2), stroke=ORANGE, width=2.8)
    f.line((SX * PHI, THETA), (SX * PHI, t2 - 0.012), stroke=INK, width=1.6, arrow=True)
    f.dot((SX * PHI, THETA), r=4, fill=INK)
    f.dot((SX * PHI, t2), r=3.4, fill=INK)
    f.text((SX * PHI + 0.03, THETA - 0.035), '(φ, θ)', size=14, anchor='start')
    f.text((SX * PHI - 0.03, t2 + 0.025), "(φ, θ′)", size=14, anchor='end')
    f.text((SX * PHI / 2, t2 - 0.03), 'F &gt; 0', size=13, color=BLUE, italic=False)
    f.text(((SX * PHI + w) / 2 + 0.005, t2 - 0.03), 'H &lt; 0', size=13, color=ORANGE, italic=False)
    f.text((w + 0.02, t2), "θ′", size=14, anchor='start')
    return f.save('appendix-a/uniqueness',
                  "The stretched strip with the zero sets of F and H drawn faint. From Gerver's "
                  "angles (φ, θ) an arrow rises to a higher level θ′, where F is positive and "
                  "H negative. On the horizontal line at height θ′, F is positive left of φ "
                  "(blue part) and H is negative right of φ (orange part), so no point of that "
                  "line is a zero of both")


def main():
    check_formal_conjectures()
    check_appendix()
    sofa = sofa_outline()
    paths = [conventions(sofa), angle_lift(), slide(), radius_figure(sofa), dependencies(),
             triangle(), zero_sets(), uniqueness_argument()]
    for path in paths:
        print(f'wrote {path.relative_to(path.parents[4])}')


if __name__ == '__main__':
    main()
