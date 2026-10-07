#!/usr/bin/env python3
"""The figures of Chapter 1, in baek/proof/figures/01-introduction/: Gerver's sofa in the hallway,
and an animation of its motion around the corner.

    python3 scripts/figures/fig_intro.py

The sofa is the shape of Romik's rotation path (gerver.py); at time t it is placed by
q ↦ R_{-t}(q - x(t)), which maps it into the hallway L.
"""
import math
from pathlib import Path

import numpy as np

import gerver
from sofa_figures import Figure, OUT, FAINT, WALL, FLOOR, COLORS, FILLS, hallway

PI = math.pi
BLUE, ORANGE = COLORS[0], COLORS[1]


def sofa(m=900, n=20000):
    pts = gerver.outline(m, n)
    # The polygon must be inside the hallway at every sampled time.
    for t in np.linspace(0, PI / 2, 9):
        for x, y in gerver.place(t, pts[::7]):
            assert x <= 1 + 1e-6 and y <= 1 + 1e-6 and (x >= -1e-6 or y >= -1e-6), (t, x, y)
    return pts


def in_hallway(pts):
    """The hallway with the sofa halfway through its turn, and outlined at the start and the end."""
    xmin, ymin = -3.35, -2.45
    f = Figure(xmin, 1.35, ymin, 1.3, 120)
    hallway(f, xmin, ymin)
    for t in (0, PI / 2):
        f.polygon(gerver.place(t, pts), fill=FILLS[0], stroke=BLUE, width=1.2, opacity=0.4,
                  stroke_opacity=0.7, dash='6 4')
    f.polygon(gerver.place(PI / 4, pts), fill=FILLS[0], stroke=BLUE, width=2.0, opacity=0.95)
    # The corner, and the labels of the two sides of the hallway.
    f.dot((0, 0), r=3)
    f.text((-2.9, 0.5), 'H', size=17, color=WALL)
    f.text((0.5, -2.05), 'V', size=17, color=WALL)
    f.text((-0.17, -0.17), 'o', size=14)
    path = f.save('01-introduction/hallway',
                  "Gerver's sofa in the hallway of unit width: the solid sofa is halfway through its "
                  "turn, and dashed outlines show it at the start, in the horizontal side H, and "
                  "at the end, in the vertical side V")
    return path


def sofa_parts(pts):
    """Gerver's sofa alone, with its rotation path."""
    f = Figure(-2.4, 1.15, -0.25, 1.15, 150)
    f.polygon(pts, fill=FILLS[0], stroke=BLUE, width=2.0)
    xs = [gerver.path(t) for t in np.linspace(0, PI / 2, 300)]
    f.polyline(xs, stroke=ORANGE, width=2.0)
    f.dot(gerver.path(0), r=3.2, fill=ORANGE)
    f.dot(gerver.path(PI / 2), r=3.2, fill=ORANGE)
    f.text((0.08, -0.13), 'x(0)', size=14, color=ORANGE)
    q = gerver.path(PI / 2)
    f.text((q[0], q[1] - 0.13), 'x(π/2)', size=14, color=ORANGE)
    f.line((-2.35, 0), (1.1, 0), stroke=FAINT, width=1)
    f.line((-2.35, 1), (1.1, 1), stroke=FAINT, width=1, dash='4 3')
    f.text((1.12, 1), '1', size=13, italic=False, anchor='start', color=FAINT)
    f.text((1.12, 0), '0', size=13, italic=False, anchor='start', color=FAINT)
    return f.save('01-introduction/gerver-sofa',
                  "Gerver's sofa, of area 2.2195, between the lines y = 0 and y = 1, with the "
                  "rotation path x(t) of Romik's description: it starts at the origin and ends "
                  "at x(π/2), on the bottom edge of the sofa")


def supporting_hallway(pts, t=PI / 4):
    """The sofa's frame: the hallway turned by t about the sofa, x(t) + R_t L, contains the sofa."""
    xmin, xmax, ymin, ymax = -2.75, 1.45, -1.25, 2.25
    f = Figure(xmin, xmax, ymin, ymax, 120)
    x = gerver.path(t)

    def moved(q):
        return gerver.add(x, gerver.rot(t, q))

    far = 8
    floor = [moved(q) for q in [(-far, 0), (0, 0), (0, -far), (1, -far), (1, 1), (-far, 1)]]
    f.polygon(floor, fill=FLOOR, stroke='none', width=0)
    # The sofa lies in the turned hallway.
    for q in pts[::5]:
        X, Y = gerver.rot(-t, (q[0] - x[0], q[1] - x[1]))
        assert X <= 1 + 1e-6 and Y <= 1 + 1e-6 and (X >= -1e-6 or Y >= -1e-6), (X, Y)
    f.polygon(pts, fill=FILLS[0], stroke=BLUE, width=2.0)
    f.polyline([moved(q) for q in [(-far, 1), (1, 1), (1, -far)]], stroke=WALL, width=2.6)
    f.polyline([moved(q) for q in [(-far, 0), (0, 0), (0, -far)]], stroke=WALL, width=2.6)
    f.polyline([gerver.path(s) for s in np.linspace(0, PI / 2, 300)], stroke=ORANGE, width=2.0)
    y = moved((1, 1))
    f.dot(x, r=3.4, fill=ORANGE)
    f.dot(y, r=3.4)
    f.text((x[0], x[1] - 0.3), 'x(π/4)', size=15, color=ORANGE)
    f.text((y[0] + 0.12, y[1] + 0.05), 'y(π/4)', size=15, anchor='start')
    # Each wall is labelled beside it, outside the hallway's floor.
    for q, label in [((1, -0.25), 'a'), ((-0.25, 1), 'c'), ((0, -1.45), 'b'), ((-1.45, 0), 'd')]:
        p = moved(q)
        n = gerver.rot(t, (0.3 if label in 'ab' else 0, 0.3 if label in 'cd' else 0))
        side = 1 if label in 'ac' else -1
        f.text((p[0] + side * n[0], p[1] + side * n[1]), f'{label}(π/4)', size=15)
    f.text((-1.75, 0.5), 'G', size=17, color=BLUE)
    return f.save('01-introduction/supporting-hallway',
                  "Gerver's sofa G in its frame, inside the hallway turned by π/4 about it: the "
                  "outer walls a and c touch the sofa, the inner walls b and d meet at the inner "
                  "corner x(π/4), which lies on the rotation path, and y(π/4) is the outer corner")


def animation(pts, name='01-introduction/gerver-moving.gif', size=480, frames=(24, 72, 24)):
    """The sofa slides in along H, turns the corner, and leaves along V."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import Polygon
    from PIL import Image

    xmin, xmax, ymin, ymax = -3.35, 1.35, -2.75, 1.35
    slide = 1.6
    poses = []
    n_in, n_turn, n_out = frames
    for k in range(n_in):
        s = slide * (1 - k / n_in)
        poses.append([(x - s, y) for x, y in gerver.place(0, pts)])
    for k in range(n_turn + 1):
        poses.append(gerver.place(PI / 2 * k / n_turn, pts))
    for k in range(1, n_out + 1):
        s = slide * k / n_out
        poses.append([(x, y - s) for x, y in gerver.place(PI / 2, pts)])
    images = []
    for q in poses:
        fig = plt.figure(figsize=(size / 100, size / 100 * (ymax - ymin) / (xmax - xmin)), dpi=100)
        ax = fig.add_axes([0, 0, 1, 1])
        ax.set_xlim(xmin, xmax)
        ax.set_ylim(ymin, ymax)
        ax.set_aspect('equal')
        ax.axis('off')
        ax.add_patch(Polygon([(xmin, 0), (0, 0), (0, ymin), (1, ymin), (1, 1), (xmin, 1)],
                             closed=True, facecolor=FLOOR, edgecolor='none'))
        ax.plot([xmin, 1, 1], [1, 1, ymin], color=WALL, lw=2.6, solid_capstyle='butt')
        ax.plot([xmin, 0, 0], [0, 0, ymin], color=WALL, lw=2.6, solid_capstyle='butt')
        ax.add_patch(Polygon(q, closed=True, facecolor=FILLS[0], edgecolor=BLUE, lw=1.8))
        fig.canvas.draw()
        rgba = np.asarray(fig.canvas.buffer_rgba())
        images.append(Image.fromarray(rgba[:, :, :3].copy()))
        plt.close(fig)
    # Hold the first and last frames.
    durations = [40] * len(images)
    durations[0] = durations[-1] = 700
    pal = images[len(images) // 2].quantize(colors=48, method=Image.Quantize.MEDIANCUT)
    frames_q = [im.quantize(palette=pal, dither=Image.Dither.NONE) for im in images]
    path = OUT / name
    path.parent.mkdir(parents=True, exist_ok=True)
    frames_q[0].save(path, save_all=True, append_images=frames_q[1:], duration=durations,
                     loop=0, optimize=True, disposal=1)
    return path


def main():
    pts = sofa()
    for p in (in_hallway(pts), sofa_parts(pts), supporting_hallway(pts), animation(pts)):
        print(f'wrote {p.relative_to(OUT.parents[2])} ({p.stat().st_size // 1024} KiB)')


if __name__ == '__main__':
    main()
