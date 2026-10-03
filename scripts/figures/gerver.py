#!/usr/bin/env python3
"""The geometry of Gerver's sofa, computed from the definitions of the formalization.

Gerver's four constants A, B, phi, theta solve the system `ABφθSpec` of formal-conjectures
(`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec` in `ChallengeDefs.lean`); they are found here
by Newton's method in 40-digit arithmetic. Romik's parameters are rebuilt from them by the formulas
of `MovingSofaBridge.GerverConstants.toRomik`, and Romik's rotation path is glued from the five
phases `Baek.GerverParams.x₁`, ..., `x₅`. Gerver's sofa is the shape of that path
(`Baek.shapeOfPath`):

    S = H ∩ ⋂_{t ∈ [0, π/2]} (x(t) + R_t L) ∩ (x(π/2) + R_{π/2} V).

A point q lies in x(t) + R_t L when its coordinates (⟨q - x(t), u_t⟩, ⟨q - x(t), v_t⟩) in the
frame of the moved hallway lie in L = {X ≤ 1, Y ≤ 1, X ≥ 0 or Y ≥ 0}. The two outer walls bound
y from above, and the inner corner removes the points below a roof; so every vertical line meets
S in an interval [bottom(x), top(x)], computed here on a grid of angles. `python3 gerver.py`
prints the constants and checks the area against Gerver's value 2.21953...
"""
import math

import mpmath as mp
import numpy as np

mp.mp.dps = 40
PI = math.pi


def gerver_constants():
    """Gerver's constants (A, B, phi, theta), the solution of `ABφθSpec`."""
    def system(A, B, f, t):
        return [A * (mp.cos(t) - mp.cos(f)) - 2 * B * mp.sin(f)
                + (t - f - 1) * mp.cos(t) - mp.sin(t) + mp.cos(f) + mp.sin(f),
                A * (3 * mp.sin(t) + mp.sin(f)) - 2 * B * mp.cos(f)
                + 3 * (t - f - 1) * mp.sin(t) + 3 * mp.cos(t) - mp.sin(f) + mp.cos(f),
                A * mp.cos(f) - (mp.sin(f) + mp.mpf(1) / 2 - mp.cos(f) / 2 + B * mp.sin(f)),
                (A + mp.pi / 2 - f - t) - (B - (t - f) * (1 + A) / 2 - (t - f) ** 2 / 4)]
    sol = mp.findroot(system, (0.0944, 1.3992, 0.0392, 0.6813))
    return tuple(float(v) for v in sol)


A, B, PHI, THETA = gerver_constants()


def rot(t, p):
    c, s = math.cos(t), math.sin(t)
    return (c * p[0] - s * p[1], s * p[0] + c * p[1])


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


# Romik's parameters, rebuilt from Gerver's constants (`GerverConstants.toRomik`).
a1 = ((A + 0.5) * math.sin(PHI) + (B + 1) * math.cos(PHI)) / 2
b1 = (PHI - 1 - A) / 2
b2 = B - 0.5 - b1 * PHI + PHI ** 2 / 4
k1 = (1 - a1, 0.25)
k2 = add(k1, rot(PHI, (-B / 2, 0.25)))
k3 = add(k2, rot(THETA, (0.5, (1 - A - (THETA - PHI)) / 2)))
a2, c1, c2 = -0.25, PI / 2 + A - PHI - 1, A - PHI - 1
d1, d2 = PI / 4 - b1, b2 + PI / 4 * (2 * b1 - PI / 4)
e1, e2 = a1, 0.25
k4 = (2 * k3[0] - k2[0], k2[1])
k5 = (2 * k3[0] - 1 + a1, 0.25)


def path(t):
    """Romik's rotation path x(t), glued from the phases x₁, ..., x₅ (`GerverParams.path`)."""
    c, s = math.cos(t), math.sin(t)
    if t < PHI:
        return add(rot(t, (a1 * c + a2 * s - 1, -a2 * c + a1 * s - 0.5)), k1)
    if t < THETA:
        return add(rot(t, (-t * t / 4 + b1 * t + b2, t / 2 - b1 - 1)), k2)
    if t <= PI / 2 - THETA:
        return add(rot(t, (c1 - t, c2 + t)), k3)
    if t <= PI / 2 - PHI:
        return add(rot(t, (-t / 2 + d1 - 1, -t * t / 4 + d1 * t + d2)), k4)
    return add(rot(t, (e1 * c + e2 * s - 0.5, -e2 * c + e1 * s - 1)), k5)


def angles(n):
    """n + 1 angles in [0, π/2], with the four phase boundaries among them."""
    ts = set(np.linspace(0, PI / 2, n + 1).tolist())
    ts.update([PHI, THETA, PI / 2 - THETA, PI / 2 - PHI])
    return np.array(sorted(ts))


def bounds(xs, n=6000):
    """top(x) and bottom(x) of Gerver's sofa on the vertical lines xs."""
    xs = np.asarray(xs, dtype=float)
    ts = angles(n)
    X = np.array([path(t) for t in ts])
    top = np.minimum(np.ones_like(xs), np.inf)
    roof = np.zeros_like(xs)
    for t, (p1, p2) in zip(ts, X):
        c, s = math.cos(t), math.sin(t)
        # Outer walls: <q - x, u_t> <= 1 and <q - x, v_t> <= 1, upper bounds on y for t in (0, π/2).
        if s > 1e-15:
            top = np.minimum(top, p2 + (1 - (xs - p1) * c) / s)
        if c > 1e-15:
            top = np.minimum(top, p2 + (1 + (xs - p1) * s) / c)
        # Inner corner: the points with <q - x, u_t> < 0 and <q - x, v_t> < 0 lie below the roof.
        if s > 1e-15 and c > 1e-15:
            g = np.minimum(p2 - (xs - p1) * c / s, p2 + (xs - p1) * s / c)
        elif s <= 1e-15:  # t = 0: below y = p2, left of x = p1
            g = np.where(xs < p1, p2, -np.inf)
        else:  # t = π/2: below y = p2, right of x = p1
            g = np.where(xs > p1, p2, -np.inf)
        roof = np.maximum(roof, g)
    # The final position: x(π/2) + R_{π/2} V, that is X(π/2).y <= y <= X(π/2).y + 1 and
    # x >= X(π/2).x - 1, with H: 0 <= y <= 1 and x <= 1.
    q1, q2 = path(PI / 2)
    top = np.minimum(top, min(1.0, q2 + 1))
    bottom = np.maximum(roof, max(0.0, q2))
    inside = (xs <= 1) & (xs >= q1 - 1) & (top > bottom)
    return top, bottom, inside


def outline(m=1600, n=6000):
    """The boundary of Gerver's sofa as a closed polygon, counterclockwise."""
    q1, _ = path(PI / 2)
    lo, hi = q1 - 1, 1.0
    xs = np.linspace(lo, hi, m + 1)
    top, bottom, inside = bounds(xs, n)
    idx = np.nonzero(inside)[0]
    xs, top, bottom = xs[idx], top[idx], bottom[idx]
    upper = list(zip(xs[::-1], top[::-1]))
    lower = list(zip(xs, bottom))
    return lower + upper


def area(m=4000, n=6000):
    q1, _ = path(PI / 2)
    xs = np.linspace(q1 - 1, 1.0, m + 1)
    top, bottom, inside = bounds(xs, n)
    h = np.where(inside, top - bottom, 0.0)
    return float(np.trapezoid(h, xs))


def place(t, pts):
    """The sofa's points moved to time t: q ↦ R_{-t}(q - x(t)), which maps S into the hallway L."""
    p = path(t)
    c, s = math.cos(t), math.sin(t)
    out = []
    for x, y in pts:
        dx, dy = x - p[0], y - p[1]
        out.append((c * dx + s * dy, -s * dx + c * dy))
    return out


if __name__ == '__main__':
    print(f'A = {A:.12f}, B = {B:.12f}, phi = {PHI:.12f}, theta = {THETA:.12f}')
    print(f'x(0) = {path(0)}, x(pi/2) = {path(PI / 2)}')
    a = area()
    print(f'area = {a:.6f} (Gerver: 2.21953...)')
    assert abs(a - 2.21953) < 2e-4, a
