#!/usr/bin/env python3
"""Draw the figures of the paper, as PDF files in docs/paper/figures/.

    python3 docs/paper/figures/make_figures.py

Every figure is computed from the definitions of the formalization, with the geometry of
scripts/figures/ (gerver.py: Gerver's sofa from Gerver's four constants and Romik's equations;
fig_uniqueness.py and fig_injectivity.py: polygon caps, niches and the supporting hallway). The
facts that a caption states are checked by `assert`s there and here.
"""
import math
import sys
from pathlib import Path

import numpy as np
import matplotlib

matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Circle

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / 'scripts' / 'figures'))
import gerver  # noqa: E402
import fig_injectivity as fi  # noqa: E402
import fig_uniqueness as fu  # noqa: E402

PI = math.pi
INK, FAINT, WALL = '#1f2937', '#9ca3af', '#374151'
BLUE, ORANGE, GREEN, PURPLE = '#2563eb', '#ea580c', '#16a34a', '#9333ea'
BLUE_F, ORANGE_F, GREY_F, GREEN_F, PURPLE_F = '#dbeafe', '#fed7aa', '#e5e7eb', '#dcfce7', '#f3e8ff'

plt.rcParams.update({
    'font.family': 'serif', 'mathtext.fontset': 'cm', 'font.size': 8.5, 'pdf.fonttype': 42,
    'axes.linewidth': 0.6, 'savefig.bbox': 'tight', 'savefig.pad_inches': 0.02,
})


# ---- drawing helpers ---------------------------------------------------------------------------

def canvas(w, h, ncols=1, ratios=None):
    fig, axes = plt.subplots(1, ncols, figsize=(w, h), squeeze=False,
                             gridspec_kw={'width_ratios': ratios} if ratios else None)
    axes = axes[0]
    for ax in axes:
        ax.set_aspect('equal')
        ax.axis('off')
    return fig, axes if ncols > 1 else axes[0]


def poly(ax, pts, fc='none', ec=INK, lw=1.0, ls='-', alpha=1.0, z=2):
    ax.add_patch(Polygon(list(pts), closed=True, fc=fc, ec=ec, lw=lw, ls=ls, alpha=alpha, zorder=z,
                         joinstyle='round'))


def line(ax, pts, color=INK, lw=1.0, ls='-', z=3, cap='round'):
    xs, ys = zip(*pts)
    ax.plot(xs, ys, color=color, lw=lw, ls=ls, zorder=z, solid_capstyle=cap, dash_capstyle=cap)


def arrow(ax, a, b, color=INK, lw=1.0, z=5, style='-|>', ms=6, both=False):
    ax.annotate('', xy=b, xytext=a, zorder=z,
                arrowprops=dict(arrowstyle='<|-|>' if both else style, color=color, lw=lw,
                                shrinkA=0, shrinkB=0, mutation_scale=ms))


def text(ax, xy, s, color=INK, ha='center', va='center', size=8.5, z=6, **kw):
    ax.text(xy[0], xy[1], s, color=color, ha=ha, va=va, fontsize=size, zorder=z, **kw)


def dot(ax, p, r=2.2, color=INK, z=6):
    ax.plot([p[0]], [p[1]], 'o', ms=r * 2, color=color, zorder=z, mec='none')


def save(fig, name):
    path = HERE / f'{name}.pdf'
    fig.savefig(path)
    plt.close(fig)
    print('wrote', path.relative_to(HERE.parents[2]))


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


def hallway_frame(t, pts):
    """The points `pts` given in the frame of the hallway at time t, in the sofa's coordinates."""
    return [add(gerver.path(t), mul(p[0], uvec(t)), mul(p[1], vvec(t))) for p in pts]


# ---- Gerver's sofa and its cap -----------------------------------------------------------------

SOFA = gerver.outline(900, 9000)
CAP = fu.hull(SOFA)
NICHE = fi.gerver_niche()
A_END = gerver.path(PI / 2)[0]


def fig_intro():
    fig, (a1, a2) = canvas(6.3, 2.35, 2, [1.35, 1.0])
    # Left: the hallway and three positions of the sofa.
    xmin, ymin = -3.45, -2.55
    poly(a1, [(xmin, 0), (0, 0), (0, ymin), (1, ymin), (1, 1), (xmin, 1)], fc='#f3f4f6', ec='none')
    line(a1, [(xmin, 1), (1, 1), (1, ymin)], color=WALL, lw=2.0)
    line(a1, [(xmin, 0), (0, 0), (0, ymin)], color=WALL, lw=2.0)
    for t, style in ((0.0, 'dashed'), (PI / 4, 'solid'), (PI / 2, 'dashed')):
        pts = gerver.place(t, SOFA)
        if style == 'solid':
            poly(a1, pts, fc=BLUE_F, ec=BLUE, lw=1.3, alpha=0.95, z=5)
        else:
            poly(a1, pts, fc=BLUE_F, ec=BLUE, lw=0.9, ls=(0, (4, 2)), alpha=0.5, z=4)
    dot(a1, (0, 0), 2.0)
    text(a1, (0.14, 0.17), r'$O$', size=8, ha='left')
    text(a1, (-2.35, 1.27), r'$t=0$', color=BLUE, size=8)
    text(a1, (-0.55, 1.62), r'$t=\pi/4$', color=BLUE, size=8)
    text(a1, (1.12, -1.3), r'$t=\pi/2$', color=BLUE, size=8, ha='left')
    a1.set_xlim(xmin - 0.05, 1.85)
    a1.set_ylim(ymin - 0.05, 1.9)
    # Right: the sofa, its niche and the path of the inner corner.
    xs = np.linspace(A_END - 1.0, 1.0, 400)
    top, bottom, inside = gerver.bounds(xs, 6000)
    poly(a2, SOFA, fc=BLUE_F, ec=BLUE, lw=1.3)
    poly(a2, NICHE, fc=ORANGE_F, ec='none', z=3)
    path = [gerver.path(t) for t in np.linspace(0, PI / 2, 400)]
    line(a2, path, color=ORANGE, lw=1.5, z=4)
    line(a2, [(A_END - 1.05, 0), (1.05, 0)], color=FAINT, lw=0.5, ls=':', z=1)
    line(a2, [(A_END - 1.05, 1), (1.05, 1)], color=FAINT, lw=0.5, ls=':', z=1)
    text(a2, (-1.75, 0.62), r'$G$', color=BLUE, size=10)
    text(a2, (-0.62, 0.17), r'niche', color=ORANGE, size=7.5)
    dot(a2, (0, 0), 1.8, ORANGE)
    dot(a2, (A_END, 0), 1.8, ORANGE)
    text(a2, (0.12, -0.18), r'$\mathbf{x}(0)$', color=ORANGE, size=7.5, ha='left')
    text(a2, (A_END - 0.02, -0.18), r'$\mathbf{x}(\pi/2)$', color=ORANGE, size=7.5, ha='center')
    a2.set_xlim(A_END - 1.1, 1.12)
    a2.set_ylim(-0.3, 1.12)
    save(fig, 'fig-intro')


def fig_cap():
    """A cap, its niche and a supporting hallway (Section 2)."""
    t = 0.62
    fig, ax = canvas(4.7, 3.1)
    poly(ax, CAP, fc=BLUE_F, ec=BLUE, lw=1.2, z=2)
    poly(ax, NICHE, fc=ORANGE_F, ec=ORANGE, lw=0.9, z=3)
    big = 2.4
    arm1 = hallway_frame(t, [(-big, 0), (1, 0), (1, 1), (-big, 1)])
    arm2 = hallway_frame(t, [(0, -big), (1, -big), (1, 1), (0, 1)])
    for arm in (arm1, arm2):
        poly(ax, arm, fc=GREY_F, ec='none', alpha=0.55, z=1)
    line(ax, hallway_frame(t, [(-big, 1), (1, 1), (1, -big)]), color=WALL, lw=1.8, z=5)
    line(ax, hallway_frame(t, [(-big, 0), (0, 0), (0, -big)]), color=WALL, lw=1.8, z=5)
    x, y = gerver.path(t), add(gerver.path(t), uvec(t), vvec(t))
    dot(ax, x, 2.2, ORANGE)
    dot(ax, y, 2.2, INK)
    text(ax, add(x, (0.1, 0.14)), r'$\mathbf{x}_K(t)$', color=ORANGE, ha='left', size=8)
    text(ax, add(y, (0.1, 0.1)), r'$\mathbf{y}_K(t)$', ha='left', size=8)
    # Labels of the walls, along the walls and outside the hallway.
    td = math.degrees(t)

    def wall_label(p_frame, off, s, rot):
        q = hallway_frame(t, [p_frame])[0]
        text(ax, add(q, off), s, color=WALL, size=8, rotation=rot, rotation_mode='anchor')

    wall_label((-1.9, 1), mul(0.17, vvec(t)), r'$c_K(t)$', td)
    wall_label((-1.55, 0), mul(-0.17, vvec(t)), r'$d_K(t)$', td)
    wall_label((1, -1.9), mul(0.17, uvec(t)), r'$a_K(t)$', td - 90)
    wall_label((0, -1.6), mul(-0.17, uvec(t)), r'$b_K(t)$', td - 90)
    text(ax, (-0.78, 0.65), r'$K$', color=BLUE, size=11)
    text(ax, (-0.62, 0.17), r'$\mathcal{N}(K)$', color=ORANGE, size=8)
    q = hallway_frame(t, [(-0.55, -0.55)])[0]
    text(ax, add(q, (0.0, -0.05)), r'$Q^-_K(t)$', color=PURPLE, size=8)
    ax.set_xlim(-3.15, 2.0)
    ax.set_ylim(-1.75, 2.1)
    save(fig, 'fig-cap')


# ---- Section 5: pushing a side -----------------------------------------------------------------

def fig_moves():
    H, K = fu.example_cap(n=2)
    omega = H.omega
    t = omega / 2
    eps = 0.14
    fig, (a1, a2) = canvas(6.4, 2.35, 2)
    N, edges = H.niche()
    for ax in (a1, a2):
        poly(ax, fu.parallelogram(omega), ec=FAINT, lw=0.7, ls=(0, (3, 2)), z=1)
        poly(ax, K, fc=BLUE_F, ec=BLUE, lw=1.2, z=2)
        poly(ax, N, fc=ORANGE_F, ec=ORANGE, lw=1.0, z=3)
        dot(ax, (0, 0), 1.6)
        text(ax, (0.1, -0.15), r'$O$', size=7.5, ha='left')
    text(a1, (0.2, 0.78), r'$K$', color=BLUE, size=10)
    # Left: raise the height at the floating normal t = omega/2.
    Hp = H.raised(t, eps)
    Kp, Np = Hp.cap(), Hp.niche()[0]
    sig, tau = fu.edge_length(K, t), H.tau(edges, 'b', t)
    assert sig > 0.1 and tau > 0.1
    small = 1e-3
    Hs = H.raised(t, small)
    dK = (fu.area(Hs.cap()) - fu.area(K)) / small
    dN = (fu.area(Hs.niche()[0]) - fu.area(N)) / small
    assert abs(dK - sig) < 0.01 and abs(dN - tau) < 0.01
    poly(a1, Kp, ec=GREEN, lw=1.2, ls=(0, (4, 2)), z=4)
    poly(a1, Np, ec=PURPLE, lw=1.0, ls=(0, (4, 2)), z=4)
    for a, b in zip(K, K[1:] + K[:1]):
        d = fu.sub(b, a)
        if abs(d[1] / fu.norm(d) - math.cos(t)) < 1e-7 and abs(-d[0] / fu.norm(d) - math.sin(t)) < 1e-7:
            line(a1, [a, b], color=BLUE, lw=3.0, z=5)
            mid = mul(0.5, add(a, b))
            arrow(a1, mid, add(mid, mul(0.3, uvec(t))), color=GREEN, lw=1.0)
            text(a1, (2.55, 0.2), r'$\sigma_K(t)$', color=BLUE, size=8, ha='left')
            text(a1, add(mid, mul(0.3, uvec(t)), (0.13, 0.05)), r'$\varepsilon$', color=GREEN, size=8)
    for p0, p1, tag in edges:
        if tag == ('b', t):
            line(a1, [p0, p1], color=ORANGE, lw=3.0, z=5)
            mid = mul(0.5, add(p0, p1))
            text(a1, (0.95, -0.27), r'$\tau_K(t)$', color=ORANGE, size=8)
            line(a1, [(0.95, -0.16), mid], color=ORANGE, lw=0.6, z=5)
    text(a1, (2.15, 0.85), r'$K^{+}$', color=GREEN, size=9)
    # Right: raise the pinned height at pi/2.
    Hq = H.raised('top', eps)
    Kq, Nq = Hq.cap(), Hq.niche()[0]
    poly(a2, Kq, ec=GREEN, lw=1.2, ls=(0, (4, 2)), z=4)
    poly(a2, Nq, ec=PURPLE, lw=1.0, ls=(0, (4, 2)), z=4)
    for y in (eps, 1 + eps):
        line(a2, [(-1.7, y), (2.0, y)], color=GREEN, lw=0.7, ls=':', z=3)
    top = [p for p in K if abs(p[1] - 1) < 1e-9]
    line(a2, [(min(top)[0], 1), (max(top)[0], 1)], color=BLUE, lw=3.0, z=5)
    text(a2, (0.5 * (min(top)[0] + max(top)[0]), 0.8), r'$\sigma_K(\pi/2)$', color=BLUE, size=8)
    text(a2, (1.0, 0.45), r'$K$', color=BLUE, size=10)
    arrow(a2, (1.7, 1), (1.7, 1 + eps), color=GREEN, lw=1.0)
    arrow(a2, (1.7, 0), (1.7, eps), color=GREEN, lw=1.0)
    text(a2, (1.84, 1.07), r'$\varepsilon$', color=GREEN, size=8)
    text(a2, (1.84, 0.07), r'$\varepsilon$', color=GREEN, size=8)
    text(a2, (-1.35, 1.28), r"$K'$", color=GREEN, size=9)
    for ax in (a1, a2):
        ax.set_xlim(-1.75, 3.2)
        ax.set_ylim(-0.4, 1.5)
    save(fig, 'fig-moves')


def fig_rotate():
    omega = 1.1
    beta = PI / 2 - omega
    c = fu.c_omega(omega)
    para = fu.parallelogram(omega)
    o = (c, 1.0)
    p1, p2 = mul(c, uvec(0)), mul(c, vvec(omega))
    assert fu.norm(fu.sub(p1, fu.sub(o, vvec(0)))) < 1e-12 and fu.norm(fu.sub(p2, fu.sub(o, uvec(omega)))) < 1e-12
    X = [p1, para[1], para[2], para[3], p2]
    for tt in np.linspace(omega, PI / 2, 401):
        w = max(fu.dot(p, uvec(tt)) for p in X) - min(fu.dot(p, uvec(tt)) for p in X)
        assert abs(w - max(math.sin(tt), math.cos(tt - omega))) < 1e-12 and w <= 1 + 1e-12
    fig, (a1, a2) = canvas(6.3, 2.0, 2, [1.15, 1.45])
    poly(a1, para, ec=FAINT, lw=0.8, ls=(0, (3, 2)), z=1)
    poly(a1, X, fc=BLUE_F, ec=BLUE, lw=1.2, z=2)
    poly(a1, [(0, 0), p1, p2], fc=ORANGE_F, ec=ORANGE, lw=1.2, z=3)
    dot(a1, (0, 0), 1.8)
    text(a1, (0.0, -0.2), r'$O$', size=8)
    dot(a1, o, 1.8)
    text(a1, (o[0] + 0.06, o[1] + 0.1), r'$o_\omega$', size=8, ha='left')
    text(a1, (-0.01, 0.3), r'$\Delta_\omega$', color=ORANGE, size=8, ha='right')
    text(a1, (0.85, 0.52), r'$P_\omega\setminus\Delta_\omega$', color=BLUE, size=8.5)
    a1.set_xlim(-2.1, 2.35)
    a1.set_ylim(-0.35, 1.3)
    # Right: three copies of the strip with the pentagon turned by rho = psi, psi/2, 0.
    cx = sum(p[0] for p in X) / len(X)
    xs0 = 0.0
    for k, (phi, col, lab, fill) in enumerate(((beta, GREEN, r'$\rho=\psi$', GREEN_F),
                                               (beta / 2, PURPLE, r'$\rho=\psi/2$', PURPLE_F),
                                               (0.0, BLUE, r'$\rho=0$', BLUE_F))):
        y0 = -1.35 * k
        poly(a2, [(-2.45, y0), (2.3, y0), (2.3, y0 + 1), (-2.45, y0 + 1)], fc='#f3f4f6', ec='none', z=0)
        line(a2, [(-2.45, y0), (2.3, y0)], color=INK, lw=1.0)
        line(a2, [(-2.45, y0 + 1), (2.3, y0 + 1)], color=INK, lw=1.0)
        R = [(math.cos(phi) * (p[0] - cx) - math.sin(phi) * p[1],
              math.sin(phi) * (p[0] - cx) + math.cos(phi) * p[1]) for p in X]
        lo = min(q[1] for q in R)
        assert max(q[1] for q in R) - lo <= 1 + 1e-12
        poly(a2, [(q[0], q[1] - lo + y0) for q in R], fc=fill, ec=col, lw=1.2, z=2)
        text(a2, (2.45, y0 + 0.5), lab, color=col, size=8, ha='left')
    a2.set_xlim(-2.5, 3.7)
    a2.set_ylim(-2.75, 1.1)
    save(fig, 'fig-rotate')


# ---- Section 7: the inner wall near the corner, and the curvature bound ------------------------

def fig_wall():
    data = fi.polygon_cap_data()
    t, d = fi.T_MID, fi.DELTA
    box = (-1.6, 1.4, -1.2, 1.2)
    fig, ax = canvas(4.4, 3.5)
    big = 5.0
    floor = [(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)]
    poly(ax, fi.clip_box(floor, box), fc='#f3f4f6', ec='none', z=0)
    P = [fi.place_frame(t, p) for p in data['P']]
    poly(ax, fi.clip_box(P, box), fc=BLUE_F, ec='none', alpha=0.6, z=1)
    for k in range(1, fi.N_STEPS):
        s = k * fi.DELTA
        x = fi.xpath(s)
        quad = [x, fi.add(x, fi.mul(-big, fi.uvec(s))),
                fi.add(x, fi.mul(-big, fi.uvec(s)), fi.mul(-big, fi.vvec(s))),
                fi.add(x, fi.mul(-big, fi.vvec(s)))]
        quad = fi.clip_halfplane(quad, (0, -1), 0.0)
        poly(ax, fi.clip_box([fi.place_frame(t, p) for p in quad], box), fc=ORANGE_F, ec='none', z=2)
    seg = fi.clip_segment(fi.place_frame(t, (-5.0, 0.0)), fi.place_frame(t, (5.0, 0.0)), box)
    line(ax, seg, color=FAINT, lw=0.8, z=3)
    line(ax, [(box[0], 1), (1, 1), (1, box[2])], color=WALL, lw=1.9, z=5)
    line(ax, [(box[0], 0), (0, 0), (0, box[2])], color=WALL, lw=1.9, z=5)
    for s, color in ((t - d, PURPLE), (t + d, GREEN)):
        for key, ls in (('d', (0, (5, 3))), ('b', (0, (1.5, 2.5)))):
            seg = fi.line_in_box(*data['L'][s][key], box)
            if seg:
                line(ax, seg, color=color, lw=1.0, ls=ls, z=4)
    p, Bm, Bp = data['p'], data['Bm'], data['Bp']
    line(ax, [p, (0, 0)], color=ORANGE, lw=3.4, z=5)
    line(ax, [Bp, Bm], color=ORANGE, lw=3.4, z=5)
    for pt in (p, (0, 0), Bm, Bp):
        dot(ax, pt, 2.0)
    text(ax, add(p, (0.1, 0.0)), r'$p$', size=8, ha='left')
    text(ax, (0.12, 0.12), r'$\mathbf{x}_K(t)$', size=8, ha='left')
    text(ax, add(Bm, (0.1, 0.08)), r'$B_-$', size=8, ha='left')
    text(ax, add(Bp, (0.1, -0.07)), r'$B_+$', size=8, ha='left')
    text(ax, (0.1, -0.2), r'first kind', color=ORANGE, size=7.5, ha='left')
    text(ax, (-0.08, -0.86), r'second kind', color=ORANGE, size=7.5, ha='right')
    # Labels of the dashed lines, placed on the boundary of the box.
    for s, color, name in ((t - d, PURPLE, r't-\delta'), (t + d, GREEN, r't+\delta')):
        for key in ('d', 'b'):
            ends = fi.line_in_box(*data['L'][s][key], box)
            if key == 'd':
                end = min(ends, key=lambda e: e[0])
                pos, ha = (end[0] + 0.05, end[1] + (0.1 if s < t else -0.1)), 'left'
            else:
                end = max(ends, key=lambda e: e[1])
                pos, ha = (end[0] + (0.06 if s > t else -0.06), end[1] - 0.09), ('left' if s > t else 'right')
            text(ax, pos, rf'${key}_K({name})$', size=7, color=color, ha=ha)
    text(ax, (0.1, -1.12), r'$b_K(t)$', size=8, color=WALL, ha='left')
    text(ax, (-1.5, 0.1), r'$d_K(t)$', size=8, color=WALL, ha='left')
    ax.set_xlim(box[0], box[1])
    ax.set_ylim(box[2], box[3])
    save(fig, 'fig-wall')


def fig_curvature():
    """The curvature bound for Gerver's cap, a maximizing cap: r(t) <= k0(g(t))."""
    g = gerver
    ts = np.linspace(0, PI / 2, 3001)[:-1]
    rows = []
    for t in ts:
        a, b, ap = fu.gerver_frame(t)
        rows.append((t, 1 + b + ap, fu.k0(1 + b), b))
    for t, r, k, b in rows:
        assert r <= k + 1e-12
    fig, ax = plt.subplots(figsize=(4.5, 2.0))
    T = np.array([r[0] for r in rows])
    R = np.array([r[1] for r in rows])
    Kv = np.array([r[2] for r in rows])
    ax.fill_between(T, R, Kv, color=ORANGE_F, lw=0)
    phases = [(0, g.PHI), (g.PHI, PI / 2 - g.THETA), (PI / 2 - g.THETA, PI / 2 - g.PHI), (PI / 2 - g.PHI, PI / 2)]
    for lo, hi in phases:
        m = (T >= lo) & (T < hi)
        ax.plot(T[m], R[m], color=BLUE, lw=1.6)
    ax.plot(T, Kv, color=ORANGE, lw=1.2, ls=(0, (5, 3)))
    for t, lab, ha in ((g.PHI, r'$t_1$', 'left'), (g.THETA, r'$t_2$', 'center'),
                       (PI / 2 - g.THETA, r'$t_3$', 'center'), (PI / 2 - g.PHI, r'$t_4$', 'right')):
        ax.axvline(t, color=FAINT, lw=0.6, ls=':')
        ax.text(t, -0.07, lab, ha=ha, va='top', fontsize=8)
    ax.set_xlim(0, PI / 2)
    ax.set_ylim(0, 1.55)
    ax.set_xticks([PI / 2])
    ax.set_xticklabels([r'$\pi/2$'])
    ax.tick_params(axis='x', pad=11)
    ax.set_yticks([0.5, 1.0, 1.5])
    ax.spines[['top', 'right']].set_visible(False)
    ax.text(0.95, 1.1, r'$k_0(g_{K_G}(t))$', color=ORANGE, fontsize=8.5)
    ax.text(1.18, 0.62, r'$r(t)$', color=BLUE, fontsize=8.5)
    ax.set_xlabel(r'$t$', fontsize=8.5, labelpad=1)
    save(fig, 'fig-curvature')


def fig_translate():
    a, t = 0.55, 0.65
    K2 = [(p[0] + a, p[1]) for p in CAP]
    assert abs(fu.support(K2, t) - fu.support(CAP, t) - a * math.cos(t)) < 1e-12
    fig, (ax, bx) = plt.subplots(2, 1, figsize=(4.4, 3.7), gridspec_kw={'height_ratios': [1.55, 1.0]})
    ax.set_aspect('equal')
    ax.axis('off')
    poly(ax, CAP, fc=BLUE_F, ec=BLUE, lw=1.2)
    poly(ax, K2, ec=GREEN, lw=1.2, ls=(0, (5, 3)), z=4)
    text(ax, (-0.8, 0.45), r'$K_G$', color=BLUE, size=10)
    text(ax, (0.12, -0.14), r'$K_G+(s,0)$', color=GREEN, size=8.5)
    for poly_, col in ((CAP, BLUE), (K2, GREEN)):
        q = max(poly_, key=lambda p: fu.dot(p, uvec(t)))
        line(ax, [add(q, mul(-0.4, vvec(t))), add(q, mul(0.7, vvec(t)))], color=col, lw=1.0, ls=(0, (4, 2)), z=5)
    q = max(CAP, key=lambda p: fu.dot(p, uvec(t)))
    q1 = add(q, mul(0.26, vvec(t)))
    q2 = add(q1, mul(a * math.cos(t), uvec(t)))
    arrow(ax, q1, q2, color=INK, lw=0.9, both=True)
    text(ax, add(mul(0.5, add(q1, q2)), (-0.06, 0.2)), r'$s\cos t$', size=8.5, ha='right')
    ax.set_xlim(-2.4, 1.9)
    ax.set_ylim(-0.3, 1.5)
    ts = np.linspace(0, PI, 300)
    bx.plot(ts, a * np.cos(ts), color=ORANGE, lw=1.8)
    bx.axhline(0, color=INK, lw=0.6)
    bx.set_xlim(0, PI)
    bx.set_xticks([0, PI / 2, PI])
    bx.set_xticklabels(['0', r'$\pi/2$', r'$\pi$'])
    bx.set_yticks([])
    bx.spines[['top', 'right', 'left']].set_visible(False)
    bx.set_xlabel(r'$t$', fontsize=8.5, labelpad=1)
    bx.text(1.95, 0.3, r'$h_{K}(t)-h_{K_G}(t)=s\cos t$', color=ORANGE, fontsize=8.5)
    save(fig, 'fig-translate')


def fig_recovery():
    D, X, B = fu.envelope()
    gamma = D + X + B
    a, b = D[0][0], B[-1][0]
    assert abs(D[0][1]) < 1e-9 and abs(B[-1][1]) < 1e-9 and a < b
    hmax = max(p[1] for p in gamma)
    hpath = max(gerver.path(t)[1] for t in np.linspace(0, PI / 2, 20001))
    assert abs(hmax - hpath) < 1e-5 and hpath < 0.67
    for corner in ((a, 0), (b, 0), (a, 1), (b, 1)):
        assert fu.inside(CAP, corner, tol=1e-6), corner
    fig, (a1, a2) = canvas(6.3, 2.2, 2, [1.45, 1.0])
    poly(a1, CAP, fc=BLUE_F, ec=BLUE, lw=1.2)
    poly(a1, NICHE, fc=ORANGE_F, ec='none', z=3)
    poly(a1, [(a, 0), (b, 0), (b, 1), (a, 1)], ec=INK, lw=0.8, ls=(0, (4, 3)), z=4)
    line(a1, gamma, color=ORANGE, lw=1.8, z=5)
    line(a1, [(A_END - 1.25, 1), (1.2, 1)], color=FAINT, lw=0.5, ls=':', z=1)
    line(a1, [(a - 0.15, hmax), (b + 0.15, hmax)], color=ORANGE, lw=0.6, ls=':', z=5)
    text(a1, (b + 0.17, hmax), f'{hmax:.3f}', color=ORANGE, size=7, ha='left')
    for pt, nm in (((a, 1), '$(a,1)$'), ((b, 1), '$(b,1)$')):
        dot(a1, pt, 1.8)
        text(a1, (pt[0], pt[1] + 0.12), nm, size=7.5)
    text(a1, (a, -0.13), r'$a$', size=8)
    text(a1, (b, -0.13), r'$b$', size=8)
    text(a1, (-0.62, 0.46), r'$\Gamma$', color=ORANGE, size=10)
    text(a1, (-2.0, 0.5), r'$K_G$', color=BLUE, size=11)
    p = gerver.path(1.05)
    dot(a1, p, 1.8)
    arrow(a1, p, (p[0], p[1] + 0.2), color=INK, lw=0.9)
    text(a1, (p[0] + 0.06, p[1] - 0.06), r'$p$', size=8, ha='left')
    a1.set_xlim(-2.4, 1.35)
    a1.set_ylim(-0.3, 1.25)
    # Right: why the closure of the interior is needed.
    sq = [(0, 0), (1, 0), (1, 1), (0, 1)]
    poly(a2, sq, fc=BLUE_F, ec=BLUE, lw=1.2)
    line(a2, [(1, 0), (2, 0)], color=BLUE, lw=2.4)
    text(a2, (0.5, 0.5), r'$X$', color=BLUE, size=9)
    text(a2, (1.5, 0.17), r'$Y\setminus X$', color=BLUE, size=7.5)
    text(a2, (1.0, -0.22), r'$X\subset Y$ closed, $\abs{X}=\abs{Y}$, $X\ne Y$'.replace(r'\abs{X}', '|X|').replace(r'\abs{Y}', '|Y|'), size=7)
    a2.set_xlim(-0.15, 2.2)
    a2.set_ylim(-0.4, 1.2)
    save(fig, 'fig-recovery')


def main():
    fi.check_gerver()
    fu.check_frame()
    fig_intro()
    fig_cap()
    fig_moves()
    fig_rotate()
    fig_wall()
    fig_curvature()
    fig_translate()
    fig_recovery()


if __name__ == '__main__':
    main()
