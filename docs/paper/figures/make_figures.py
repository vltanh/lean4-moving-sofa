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
BLUE, ORANGE, GREEN, PURPLE, TEAL = '#2563eb', '#ea580c', '#16a34a', '#9333ea', '#0d9488'
BLUE_F, ORANGE_F, GREY_F, GREEN_F, PURPLE_F, TEAL_F = '#dbeafe', '#fed7aa', '#e5e7eb', '#dcfce7', '#f3e8ff', '#ccfbf1'

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
    fig, a1 = canvas(3.6, 2.35)
    # The hallway and three positions of the sofa.
    xmin, ymin = -3.45, -2.55
    poly(a1, [(xmin, 0), (0, 0), (0, ymin), (1, ymin), (1, 1), (xmin, 1)], fc='#f3f4f6', ec='none')
    line(a1, [(xmin, 1), (1, 1), (1, ymin)], color=WALL, lw=2.0)
    line(a1, [(xmin, 0), (0, 0), (0, ymin)], color=WALL, lw=2.0)
    # The two end positions underneath, the middle one on top.
    positions = ((0.0, GREEN, GREEN_F, 0.6, 4), (PI / 2, PURPLE, PURPLE_F, 0.6, 5), (PI / 3, BLUE, BLUE_F, 0.9, 6))
    for t, ec, fc, alpha, z in positions:
        poly(a1, gerver.place(t, SOFA), fc=fc, ec=ec, lw=1.2, alpha=alpha, z=z)
    dot(a1, (0, 0), 2.0)
    text(a1, (-0.1, -0.1), r'$O$', size=8, ha='right', va='top')
    text(a1, ((-2.22 + 1) / 2, 1.27), r'$t=0$', color=GREEN, size=8)
    arrow(a1, (-0.95, -1.35), (0.5, -1.3), color=BLUE, lw=0.7, ms=5, z=8)
    text(a1, (-1.0, -1.35), r'$t=\pi/3$', color=BLUE, size=8, ha='right')
    text(a1, (1.12, (-2.22 + 1) / 2), r'$t=\pi/2$', color=PURPLE, size=8, ha='left')
    a1.set_xlim(xmin - 0.05, 1.85)
    a1.set_ylim(ymin - 0.05, 1.9)
    save(fig, 'fig-intro')


def fig_capniche():
    """Gerver's cap, its niche, the path of the inner corner and one position of the hallway (Section 1)."""
    t = PI / 4
    fig, ax = canvas(5.6, 3.0)

    def body(a, lw_scale=1.0):
        poly(a, CAP, fc=BLUE_F, ec=BLUE, lw=1.2 * lw_scale, z=2)
        poly(a, NICHE, fc=ORANGE_F, ec=ORANGE, lw=0.8 * lw_scale, z=3)
        path = [gerver.path(s) for s in np.linspace(0, PI / 2, 400)]
        line(a, path, color=ORANGE, lw=1.4 * lw_scale, ls=(0, (3, 1.5)), z=4)

    body(ax)
    big = 2.4
    hall = hallway_frame(t, [(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)])
    poly(ax, hall, fc=GREY_F, ec='none', alpha=0.5, z=1)
    line(ax, hallway_frame(t, [(-big, 1), (1, 1), (1, -big)]), color=FAINT, lw=0.8, z=5)
    line(ax, hallway_frame(t, [(-big, 0), (0, 0), (0, -big)]), color=FAINT, lw=0.8, z=5)
    dot(ax, gerver.path(t), 2.2, ORANGE)
    text(ax, (-1.75, 0.62), r'$K$', color=BLUE, size=11)
    text(ax, (-0.43, 0.2), r'$\mathcal{N}(K)$', color=ORANGE, size=7.5)
    zoom = (-0.1, 0.26, -0.015, 0.13)
    ins = ax.inset_axes([2.2, -0.45, 1.6, 1.6 * (zoom[3] - zoom[2]) / (zoom[1] - zoom[0])],
                        transform=ax.transData)
    body(ins, 0.8)
    ins.set_xlim(zoom[0], zoom[1])
    ins.set_ylim(zoom[2], zoom[3])
    ins.set_aspect('equal')
    ins.set_xticks([])
    ins.set_yticks([])
    for sp in ins.spines.values():
        sp.set_color(FAINT)
        sp.set_linewidth(0.6)
    ax.indicate_inset_zoom(ins, edgecolor=FAINT, lw=0.6)
    ax.set_xlim(-3.15, 3.85)
    ax.set_ylim(-1.25, 2.1)
    save(fig, 'fig-capniche')


BALANCE_THETAS = [PI / 8, PI / 4, 5 * PI / 12]


def max_polygon_heights():
    """A maximum polygon cap for the angles BALANCE_THETAS (rotation angle pi/2): its support values at the
    six floating normals, found by maximizing the polygon sofa area numerically (Nelder-Mead, from Gerver's
    support values). It is unique up to horizontal translation. Checked: it is balanced, and small changes
    of any height do not increase the sofa area."""
    thetas = BALANCE_THETAS
    floating = thetas + [s + PI / 2 for s in thetas]
    h_max = dict(zip(floating, [1.03672319606303, 1.0351611703967196, 1.020969850477072,
                                1.6347829945151837, 2.1236105529249607, 2.5964105238222475]))
    H = fu.Heights(PI / 2, thetas, lambda s: h_max.get(s, 1.0))
    K = H.cap()
    N, edges = H.niche()
    a_max = polygon_sofa_area(H)
    for t_ in thetas:
        assert abs(fu.edge_length(K, t_) - H.tau(edges, 'b', t_)) < 1e-3, t_
        assert abs(fu.edge_length(K, t_ + PI / 2) - H.tau(edges, 'd', t_)) < 1e-3, t_
    for s_ in floating:
        for d in (1e-3, -1e-3):
            assert polygon_sofa_area(H.raised(s_, d)) <= a_max + 1e-9, (s_, d)
    return H


def polygon_sofa_area(H):
    return fu.area(H.cap()) - fu.area(H.niche()[0])


def draw_copies(ax, H, big=4.0):
    """The copies of the hallway at the angles of H, the start and end strip, the polygon cap and its niche.
    Each copy shades the region inside its two outer walls in translucent blue, and so does the strip
    0 <= y <= 1 of the start and end positions; the cap, inside all of them, is darkest."""
    K = H.cap()
    N, _ = H.niche()
    regions = [fu.halfplanes([(uvec(s_), H.h[s_]), (uvec(s_ + PI / 2), H.h[s_ + PI / 2])], big=8.0)
               for s_ in H.thetas]
    regions.append(fu.halfplanes([((0.0, 1.0), 1.0), ((0.0, -1.0), 0.0)], big=8.0))
    for r in regions:
        poly(ax, r, fc=BLUE, ec='none', alpha=0.11, z=1)
    poly(ax, K, fc='none', ec=BLUE, lw=1.2, z=2)
    poly(ax, N, fc=ORANGE_F, ec=ORANGE, lw=1.0, z=3)
    for s_ in H.thetas:
        line(ax, hallway_frame_h(H, s_, [(-big, 1), (1, 1), (1, -big)]), color=FAINT, lw=0.6, z=4)
        line(ax, hallway_frame_h(H, s_, [(-big, 0), (0, 0), (0, -big)]), color=FAINT, lw=0.6, z=4)
        dot(ax, hallway_frame_h(H, s_, [(0, 0)])[0], 1.6, ORANGE)
    return K


def fig_placements():
    """Three placements of the copies at the same three angles, and their polygon caps and niches (Section 1):
    copies close in (small cap), copies far out (large niche), and a maximum polygon cap."""
    thetas = BALANCE_THETAS
    placements = [fu.Heights(PI / 2, thetas, lambda s: 1 + 0.3 * abs(math.cos(s))),
                  fu.Heights(PI / 2, thetas, lambda s: 1 + 1.4 * abs(math.cos(s))),
                  max_polygon_heights()]
    areas = [polygon_sofa_area(H) for H in placements]
    assert areas[2] > max(areas[:2]) + 0.2
    fig, axes = canvas(6.4, 2.0, 3)
    half = 2.75
    for ax, H, a in zip(axes, placements, areas):
        K = draw_copies(ax, H)
        xc = 0.5 * (min(p[0] for p in K) + max(p[0] for p in K))
        ax.set_xlim(xc - half, xc + half)
        ax.set_ylim(-0.12, 2.6)
        ax.set_title(f'sofa area ${a:.2f}$', fontsize=8, pad=2)
    save(fig, 'fig-placements')


def fig_balance():
    """Gerver's balancing argument on a maximum polygon cap (Section 1)."""
    H = max_polygon_heights()
    K = H.cap()
    N, edges = H.niche()
    t, eps = PI / 8, 0.15
    fig, (a1, a2) = canvas(6.4, 1.9, 2)
    # Left: the six pairs of equal sides. Each slanted side of the cap and the side of the niche on the
    # parallel inner wall of the same copy are drawn thick in the same colour.
    big = 4.0
    hall = [(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)]
    for t_ in H.thetas:
        poly(a1, hallway_frame_h(H, t_, hall), fc=GREY_F, ec='none', alpha=0.3, z=0.5)
        line(a1, hallway_frame_h(H, t_, [(-big, 1), (1, 1), (1, -big)]), color=FAINT, lw=0.6, z=4)
        line(a1, hallway_frame_h(H, t_, [(-big, 0), (0, 0), (0, -big)]), color=FAINT, lw=0.6, z=4)
        dot(a1, hallway_frame_h(H, t_, [(0, 0)])[0], 1.6, ORANGE)
    poly(a1, K, fc=BLUE_F, ec=BLUE, lw=1.0, z=2)
    poly(a1, N, fc=ORANGE_F, ec=ORANGE, lw=0.8, z=3)
    pair_colors = ('#db2777', '#0891b2', '#ca8a04', '#4b5563', '#0d9488', '#92400e')
    pairs = [(t_, 'b', t_) for t_ in H.thetas] + [(t_ + PI / 2, 'd', t_) for t_ in H.thetas]
    for (normal, kind, base), col in zip(pairs, pair_colors):
        for a_, b_ in zip(K, K[1:] + K[:1]):
            d_ = fu.sub(b_, a_)
            if fu.norm(d_) > 1e-9 and abs(fu.dot(mul(1 / fu.norm(d_), d_), vvec(normal)) - 1) < 1e-7:
                line(a1, [a_, b_], color=col, lw=2.4, z=5)
        for p0_, p1_, tag in edges:
            if tag == (kind, base):
                line(a1, [p0_, p1_], color=col, lw=2.4, z=5)
    Hp = H.raised(t, eps)
    Kp, Np = Hp.cap(), Hp.niche()[0]
    sig, tau = fu.edge_length(K, t), H.tau(edges, 'b', t)
    assert sig > 0.1 and abs(sig - tau) < 1e-3
    small = 1e-4
    Hs = H.raised(t, small)
    dK = (fu.area(Hs.cap()) - fu.area(K)) / small
    dN = (fu.area(Hs.niche()[0]) - fu.area(N)) / small
    assert abs(dK - sig) < 0.01 and abs(dN - tau) < 0.01, (dK, sig, dN, tau)
    # The copy at the angle t (light grey) and the same copy moved by eps in the direction u_t (dashed): this
    # moves the outer wall with normal t and the parallel inner wall, and leaves the other two walls in place.
    big = 4.0
    hall = [(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)]
    poly(a2, hallway_frame_h(H, t, hall), fc=GREY_F, ec='none', alpha=0.6, z=0.5)
    for HH, ls in ((H, '-'), (Hp, (0, (3, 2)))):
        line(a2, hallway_frame_h(HH, t, [(-big, 1), (1, 1), (1, -big)]), color=FAINT, lw=0.8, ls=ls, z=4)
        line(a2, hallway_frame_h(HH, t, [(-big, 0), (0, 0), (0, -big)]), color=FAINT, lw=0.8, ls=ls, z=4)
    dot(a2, hallway_frame_h(H, t, [(0, 0)])[0], 1.8, ORANGE)
    p0 = hallway_frame_h(H, t, [(1, 0.55)])[0]
    arrow(a2, p0, add(p0, mul(eps, uvec(t))), color=FAINT, lw=0.8, ms=4, z=6)
    text(a2, add(p0, mul(eps + 0.12, uvec(t)), (0.0, 0.03)), r'$\varepsilon$', color=FAINT, size=8)
    # The strips gained by the cap (green) and by the niche (purple) show from under K and N.
    poly(a2, Kp, fc=GREEN_F, ec=GREEN, lw=0.8, z=1.5)
    poly(a2, K, fc=BLUE_F, ec=BLUE, lw=1.2, z=2)
    poly(a2, Np, fc=PURPLE_F, ec=PURPLE, lw=0.8, z=2.5)
    poly(a2, N, fc=ORANGE_F, ec=ORANGE, lw=1.0, z=3)
    for a, b in zip(K, K[1:] + K[:1]):
        d = fu.sub(b, a)
        if fu.norm(d) > 1e-9 and abs(fu.dot(mul(1 / fu.norm(d), d), vvec(t)) - 1) < 1e-7:
            line(a2, [a, b], color=BLUE, lw=2.2, z=5)
    for p0_, p1_, tag in edges:
        if tag == ('b', t):
            line(a2, [p0_, p1_], color=ORANGE, lw=2.2, z=5)
    xlo, xhi = min(p[0] for p in K), max(p[0] for p in K)
    for ax in (a1, a2):
        ax.set_xlim(xlo - 0.35, xhi + 0.55)
        ax.set_ylim(-0.12, 2.1)
    save(fig, 'fig-balance')


def hallway_frame_h(H, t, pts):
    """Points given in the frame of the copy of the hallway at the angle t whose outer walls touch the
    polygon cap with the heights H (its inner corner is x(t) = (h(t)-1) u_t + (h(t+π/2)-1) v_t)."""
    x = add(mul(H.h[t] - 1, uvec(t)), mul(H.h[t + PI / 2] - 1, vvec(t)))
    return [add(x, mul(p[0], uvec(t)), mul(p[1], vvec(t))) for p in pts]


def fig_turn():
    """Step (3a) of Section 1, in the fixed hallway, for an actual monotone sofa: a polygon cap K with
    rotation angle omega < pi/2 (fu.example_cap) minus its niche, whose niche contains the triangle at O.
    A copy of the sofa turned by pi/2 - omega starts in the horizontal side (1), turns back inside it (2),
    and then follows the sofa's own movement through the supporting hallways, shown halfway (3) and at the
    end (4). omega = 1.1 (about 63 degrees) is in the range of the argument."""
    omega = 1.1
    beta = PI / 2 - omega
    H, K = fu.example_cap(omega, 0.6, 4)
    N, _ = H.niche()
    c = fu.c_omega(omega)
    tri = [(0.0, 0.0), (c, 0.0), mul(c, vvec(omega))]
    # The triangle lies in the niche: its vertices lie in the closed quarter-plane behind one inner corner.
    assert any(all(fu.dot(p, uvec(t)) <= H.h[t] - 1 + 1e-9 and fu.dot(p, vvec(t)) <= H.h[t + PI / 2] - 1 + 1e-9
                   for p in tri) for t in H.thetas)
    # The sofa K \ N as one polygon: the niche's roof from left to right, then the rest of the boundary of K.
    i0 = min(range(len(K)), key=lambda k: fu.norm(K[k]))
    assert fu.norm(K[i0]) < 1e-9 and fu.area(K) > 0
    m = (len(N)) // 2
    roof = N[m:][::-1]
    roof = sorted({(round(q[0], 12), round(q[1], 12)) for q in roof}, key=lambda q: q[0])
    sofa = roof + [K[(i0 + k) % len(K)] for k in range(1, len(K))]
    assert abs(fu.area(sofa) - (fu.area(K) - fu.area(N))) < 1e-6

    def rot(a, pts):
        return [(math.cos(a) * p[0] - math.sin(a) * p[1], math.sin(a) * p[0] + math.cos(a) * p[1]) for p in pts]

    def corner(t):
        return add(mul(fu.support(K, t) - 1, uvec(t)), mul(fu.support(K, t + PI / 2) - 1, vvec(t)))

    def moved(t, pts):
        """The sofa's own movement: at the angle t it sits in the hallway whose outer walls touch K."""
        x = corner(t)
        return rot(-t, [sub(p, x) for p in pts])

    def in_hallway(pts):
        dense = []
        for a, b in zip(pts, pts[1:] + pts[:1]):
            dense += [add(a, mul(k / 40, sub(b, a))) for k in range(40)]
        return all(q[0] <= 1 + 1e-9 and q[1] <= 1 + 1e-9 and (q[1] >= -1e-9 or q[0] >= -1e-9) and
                   (q[1] >= -1e-9 or q[0] <= 1 + 1e-9) for q in dense)

    def placed_in_side(a, pts, right):
        """pts turned by a, on the floor of the horizontal side, with the right end of the sofa at x = right."""
        R = rot(a, sofa)
        dy, dx = -min(q[1] for q in R), right - max(q[0] for q in R)
        return [(q[0] + dx, q[1] + dy) for q in rot(a, pts)]

    own = [(moved(0.0, sofa), PURPLE, PURPLE_F), (moved(omega / 2, sofa), BLUE, BLUE_F),
           (moved(omega, sofa), WALL, GREY_F)]
    start_right = max(q[0] for q in own[0][0])
    width = max(q[0] for q in sofa) - min(q[0] for q in sofa)
    gap = 0.35
    # One hallway: the extra turn in the horizontal side (green, teal), ending in the sofa's starting position
    # (purple), then the sofa's own movement around the corner (blue halfway, grey at the end).
    turn = [(placed_in_side(beta, sofa, start_right - 2 * (width + gap)),
             placed_in_side(beta, tri, start_right - 2 * (width + gap)), GREEN, GREEN_F),
            (placed_in_side(beta / 2, sofa, start_right - (width + gap)),
             placed_in_side(beta / 2, tri, start_right - (width + gap)), TEAL, TEAL_F)]
    # The finished position slid down the vertical side, below the corner.
    end = own[2][0]
    drop = max(q[1] for q in end) - min(q[1] for q in end) + 0.3
    down = [(q[0], q[1] - drop) for q in end]
    own = own + [(down, WALL, GREY_F)]
    for pts, _, _ in own:
        assert in_hallway(pts)
    for pts, _, _, _ in turn:
        assert in_hallway(pts)
    for k in range(41):
        a = beta * k / 40
        R = rot(a, sofa)
        assert max(q[1] for q in R) - min(q[1] for q in R) <= 1 + 1e-9
    pts_all = [q for pts, _, _ in own for q in pts] + [q for pts, _, _, _ in turn for q in pts]
    xmax = 1.25
    xmin, ymin = min(q[0] for q in pts_all) - 0.25, min(q[1] for q in pts_all) - 0.25
    fig, ax = canvas(6.3, 6.3 * (1.25 - ymin) / (xmax - xmin))
    poly(ax, [(xmin, 0), (0, 0), (0, ymin), (1, ymin), (1, 1), (xmin, 1)], fc='#f3f4f6', ec='none', z=0)
    line(ax, [(xmin, 1), (1, 1), (1, ymin)], color=WALL, lw=1.4)
    line(ax, [(xmin, 0), (0, 0), (0, ymin)], color=WALL, lw=1.4)
    for pts, tp, col, fill in turn:
        poly(ax, pts, fc=fill, ec=col, lw=1.2, alpha=0.7, z=2)
        poly(ax, tp, fc=ORANGE_F, ec=ORANGE, lw=0.8, z=3)
    for k, (pts, col, fill) in enumerate(own):
        poly(ax, pts, fc=fill, ec=col, lw=1.2, alpha=0.55, z=2)
    poly(ax, moved(0.0, tri), fc=ORANGE_F, ec=ORANGE, lw=0.8, z=3)
    ax.set_xlim(xmin, xmax)
    ax.set_ylim(ymin, 1.25)
    save(fig, 'fig-turn')


def fig_mamikon():
    """One term of Baek's functional Q for Gerver's cap (Section 1): the segment from the point where the
    cap touches an outer wall to the outer corner of the hallway sweeps, as t runs over [phi, pi/2 - phi],
    a region of area (1/2) int rho(t)^2 dt (Mamikon's theorem)."""
    phi = 0.0391773648

    def contact(t):
        u = uvec(t)
        return max(CAP, key=lambda p: p[0] * u[0] + p[1] * u[1])

    def corner(t):
        return add(mul(fu.support(CAP, t), uvec(t)), mul(fu.support(CAP, t + PI / 2), vvec(t)))

    ts = np.linspace(phi, PI / 2 - phi, 2000)
    A = [contact(t) for t in ts]
    Y = [corner(t) for t in ts]
    rho = np.array([fu.dot(sub(Y[i], A[i]), vvec(t)) for i, t in enumerate(ts)])
    swept = A + Y[::-1]
    assert abs(0.5 * np.trapezoid(rho ** 2, ts) - abs(fu.area(swept))) < 1e-3
    fig, ax = canvas(4.6, 3.0)
    poly(ax, swept, fc=PURPLE_F, ec='none', z=1)
    poly(ax, CAP, fc=BLUE_F, ec=BLUE, lw=1.2, z=2)
    line(ax, Y, color=PURPLE, lw=1.2, ls=(0, (3, 1.5)), z=3)
    for t in np.linspace(phi, PI / 2 - phi, 9)[1:-1]:
        line(ax, [contact(t), corner(t)], color=FAINT, lw=0.6, z=3)
    t = 0.75
    a_, y_ = contact(t), corner(t)
    # The copy of the hallway at the angle t, placed against K: its outer corner is y_.
    x_ = sub(y_, add(uvec(t), vvec(t)))
    big = 5.0

    def frame(pts):
        return [add(x_, mul(p[0], uvec(t)), mul(p[1], vvec(t))) for p in pts]

    poly(ax, frame([(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)]), fc=GREY_F, ec='none',
         alpha=0.6, z=0.5)
    line(ax, frame([(-big, 1), (1, 1), (1, -big)]), color=FAINT, lw=0.8, z=1.5)
    line(ax, frame([(-big, 0), (0, 0), (0, -big)]), color=FAINT, lw=0.8, z=1.5)
    line(ax, [a_, y_], color=PURPLE, lw=1.6, z=4)
    dot(ax, a_, 1.8, INK)
    dot(ax, y_, 1.8, PURPLE)
    text(ax, add(mul(0.5, add(a_, y_)), mul(0.18, uvec(t))), r'$\varrho(t)$', color=PURPLE, size=8)
    text(ax, (-1.6, 0.45), r'$K$', color=BLUE, size=10)
    ys = [q[1] for q in Y]
    xs = [q[0] for q in Y] + [p[0] for p in CAP]
    ax.set_xlim(min(xs) - 0.1, max(xs) + 0.1)
    ax.set_ylim(-0.1, max(ys) + 0.1)
    save(fig, 'fig-mamikon')


def fig_cap():
    """A cap, its niche and a supporting hallway (Section 2)."""
    t = 0.62
    fig, ax = canvas(4.7, 3.1)
    poly(ax, CAP, fc=BLUE_F, ec=BLUE, lw=1.2, z=2)
    poly(ax, NICHE, fc=ORANGE_F, ec=ORANGE, lw=0.9, z=3)
    big = 2.4
    hall = hallway_frame(t, [(-big, 0), (0, 0), (0, -big), (1, -big), (1, 1), (-big, 1)])
    poly(ax, hall, fc=GREY_F, ec='none', alpha=0.55, z=1)
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
    assert hmax < 1 and hpath < 1
    for corner in ((a, 0), (b, 0), (a, 1), (b, 1)):
        assert fu.inside(CAP, corner, tol=1e-6), corner
    # One panel with axes of 2.63 x 1.09 inches; the paper includes it at half the text width.
    fig, a1 = canvas(3.39, 1.6)
    poly(a1, CAP, fc=BLUE_F, ec=BLUE, lw=1.2)
    poly(a1, NICHE, fc=ORANGE_F, ec='none', z=3)
    poly(a1, [(a, 0), (b, 0), (b, 1), (a, 1)], ec=INK, lw=0.8, ls=(0, (4, 3)), z=4)
    line(a1, gamma, color=ORANGE, lw=1.8, z=5)
    line(a1, [(A_END - 1.25, 1), (1.2, 1)], color=FAINT, lw=0.5, ls=':', z=1)
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
    save(fig, 'fig-recovery')


def main():
    fi.check_gerver()
    fu.check_frame()
    fig_intro()
    fig_capniche()
    fig_placements()
    fig_balance()
    fig_turn()
    fig_mamikon()
    fig_cap()
    fig_moves()
    fig_rotate()
    fig_wall()
    fig_curvature()
    fig_translate()
    fig_recovery()


if __name__ == '__main__':
    main()
