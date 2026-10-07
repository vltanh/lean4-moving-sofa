#!/usr/bin/env python3
"""Drawing helpers for the figures of baek/proof/, written as SVG files in baek/proof/figures/.

The palette, the serif labels and the `Figure` class follow the figures of
lean4-squares-in-circles, by the same author, so that the two texts look alike. Each chapter's
figures are drawn by its own module, fig_<chapter>.py; `python3 scripts/figures/make_all.py` runs
them all. Every figure is computed from the definitions of the formalization (gerver.py).
"""
import math
from pathlib import Path

OUT = Path(__file__).resolve().parents[2] / 'baek' / 'proof' / 'figures'

INK = '#1f2937'
FAINT = '#9ca3af'
WALL = '#374151'
FLOOR = '#f3f4f6'
COLORS = ['#2563eb', '#ea580c', '#16a34a', '#9333ea', '#db2777', '#0891b2', '#ca8a04']
FILLS = ['#dbeafe', '#ffedd5', '#dcfce7', '#f3e8ff', '#fce7f3', '#cffafe', '#fef9c3']
GREY = '#e5e7eb'
SERIF = "Georgia, 'Times New Roman', serif"


class Figure:
    """A figure of the region [xmin, xmax] x [ymin, ymax], drawn at `scale` pixels per unit."""

    def __init__(self, xmin, xmax, ymin, ymax, scale, pad=18):
        self.xmin, self.ymax, self.s, self.pad = xmin, ymax, scale, pad
        self.w = (xmax - xmin) * scale + 2 * pad
        self.h = (ymax - ymin) * scale + 2 * pad
        self.items = []

    def p(self, x, y):
        return (self.pad + (x - self.xmin) * self.s, self.pad + (self.ymax - y) * self.s)

    def add(self, item):
        self.items.append(item)

    def _points(self, pts):
        return ' '.join(f'{x:.1f},{y:.1f}' for x, y in (self.p(*q) for q in pts))

    def polygon(self, pts, fill='none', stroke=INK, width=1.5, dash=None, opacity=1,
                stroke_opacity=1):
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        if stroke_opacity != 1:
            extra += f' stroke-opacity="{stroke_opacity}"'
        self.add(f'<polygon points="{self._points(pts)}" fill="{fill}" stroke="{stroke}" '
                 f'stroke-width="{width}" fill-opacity="{opacity}" '
                 f'stroke-linejoin="round"{extra}/>')

    def polyline(self, pts, stroke=INK, width=1.5, dash=None, opacity=1, arrow=False):
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        if opacity != 1:
            extra += f' stroke-opacity="{opacity}"'
        if arrow:
            extra += ' marker-end="url(#arrow)"'
        self.add(f'<polyline points="{self._points(pts)}" fill="none" stroke="{stroke}" '
                 f'stroke-width="{width}" stroke-linejoin="round" stroke-linecap="round"{extra}/>')

    def line(self, a, b, stroke=INK, width=1.2, dash=None, arrow=False):
        (x1, y1), (x2, y2) = self.p(*a), self.p(*b)
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        if arrow:
            extra += ' marker-end="url(#arrow)"'
        self.add(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                 f'stroke="{stroke}" stroke-width="{width}" stroke-linecap="round"{extra}/>')

    def circle(self, c, r, stroke=FAINT, width=1.2, dash=None, fill='none'):
        x, y = self.p(*c)
        extra = f' stroke-dasharray="{dash}"' if dash else ''
        self.add(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r * self.s:.1f}" fill="{fill}" '
                 f'stroke="{stroke}" stroke-width="{width}"{extra}/>')

    def dot(self, c, r=3.2, fill=INK):
        x, y = self.p(*c)
        self.add(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="{fill}"/>')

    def text(self, c, s, size=15, anchor='middle', color=INK, italic=True, dx=0, dy=0):
        x, y = self.p(*c)
        style = ' font-style="italic"' if italic else ''
        self.add(f'<text x="{x + dx:.1f}" y="{y + dy:.1f}" font-size="{size}" '
                 f'font-family="{SERIF}" fill="{color}" text-anchor="{anchor}" '
                 f'dominant-baseline="middle"{style}>{s}</text>')

    def svg(self, title):
        out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w:.0f}" '
               f'height="{self.h:.0f}" viewBox="0 0 {self.w:.0f} {self.h:.0f}" '
               f'role="img" aria-label="{title}">',
               f'<title>{title}</title>',
               '<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" '
               'markerUnits="userSpaceOnUse" markerWidth="11" markerHeight="11" '
               f'orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="{INK}"/>'
               '</marker></defs>',
               '<rect width="100%" height="100%" fill="#ffffff"/>']
        return '\n'.join(out + self.items + ['</svg>']) + '\n'

    def save(self, name, title):
        path = OUT / f'{name}.svg'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(self.svg(title))
        return path


def hallway(f, xmin, ymin, floor=FLOOR, wall=WALL, width=3.0):
    """The hallway L = H ∪ V, clipped to x >= xmin and y >= ymin: the floor, then the walls."""
    f.polygon([(xmin, 0), (0, 0), (0, ymin), (1, ymin), (1, 1), (xmin, 1)],
              fill=floor, stroke='none', width=0)
    f.polyline([(xmin, 1), (1, 1), (1, ymin)], stroke=wall, width=width)
    f.polyline([(xmin, 0), (0, 0), (0, ymin)], stroke=wall, width=width)


def sb(base, sub, after='', size=15):
    """Text with a subscript, as SVG markup (shifted with dy, which every renderer supports)."""
    d = 0.3 * size
    out = f'{base}<tspan dy="{d:.1f}" font-size="{0.68 * size:.1f}">{sub}</tspan>'
    if after:
        out += f'<tspan dy="{-d:.1f}">{after}</tspan>'
    return out


def sp(base, sup, after='', size=15):
    """Text with a superscript, as SVG markup."""
    d = 0.35 * size
    out = f'{base}<tspan dy="{-d:.1f}" font-size="{0.68 * size:.1f}">{sup}</tspan>'
    if after:
        out += f'<tspan dy="{d:.1f}">{after}</tspan>'
    return out
