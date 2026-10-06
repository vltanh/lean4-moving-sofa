"""Polygonal upper caps parametrised by edge lengths at fixed normal angles.

A cap U lies in the strip 0<=y<=1, has bottom on y=0, and its upper boundary is
the polyline starting at (x_r, 0) and taking edges of length sig[i] in the
directions v(theta_i) = (-sin theta_i, cos theta_i), theta_0 < ... in [0, pi].
Constraints: sum_{theta_i<pi/2} sig cos = 1 (touch y=1), sum sig cos = 0
(return to y=0).  Width W = sum sig sin.

The niche, monotone sofa T_U and ambidextrous envelope are evaluated
fiberwise with a dense grid of hallway angles (the continuum of hallways is
approximated from inside, so computed sofa areas are slight over-estimates).
"""
import numpy as np
from numpy import sin, cos, pi

L = pi / 2


def vertices(theta, sig, xr=0.0):
    v = np.stack([-sin(theta), cos(theta)], axis=1) * sig[:, None]
    P = np.vstack([[xr, 0.0], np.array([xr, 0.0]) + np.cumsum(v, axis=0)])
    return P


def support(P, ang):
    """h(ang) for the convex hull of the vertex set P (plus the bottom edge,
    which is inside the hull already)."""
    return (P[:, 0][None, :] * cos(ang)[:, None] +
            P[:, 1][None, :] * sin(ang)[:, None]).max(axis=1)


def top_profile_from_vertices(P, x):
    """upper boundary of the polygon (upper hull) at abscissae x."""
    # vertices are ordered right->left along the upper boundary
    xs = P[::-1, 0]
    ys = P[::-1, 1]
    # remove duplicates in x keeping max y
    order = np.argsort(xs, kind="stable")
    xs, ys = xs[order], ys[order]
    return np.interp(x, xs, ys)


class Grid:
    def __init__(self, nt=600, nx=1200):
        self.t = np.linspace(0, L, nt + 2)[1:-1]
        self.st = sin(self.t)
        self.ct = cos(self.t)
        self.nx = nx


def cap_fibers(P, grid, x):
    """top a(x) and niche roof alpha(x) (>=0) of the cap with vertices P."""
    t = grid.t
    f = support(P, t)
    g = support(P, t + L)
    st, ct = grid.st[None, :], grid.ct[None, :]
    Rt = (f[None, :] - 1 - x[:, None] * ct) / st
    Lt = (g[None, :] - 1 + x[:, None] * st) / ct
    F = np.minimum(Rt, Lt).max(axis=1)
    a = top_profile_from_vertices(P, x)
    return a, np.maximum(F, 0.0), F


def psi(theta, sig, grid, return_parts=False):
    P = vertices(theta, sig)
    xr, xl = P[0, 0], P[-1, 0]
    x = np.linspace(xl, xr, grid.nx)
    a, al, F = cap_fibers(P, grid, x)
    W = xr - xl
    T = np.trapezoid(np.maximum(a - al, 0), x)
    if return_parts:
        return dict(x=x, a=a, alpha=al, F=F, W=W, T=T, U=np.trapezoid(a, x),
                    P=P)
    return T - W / 2


def pair_area(theta, sig, theta2, sig2, shift, grid, return_parts=False):
    """area of T_U cap rho(T_U') where U' is translated by `shift` in x."""
    P = vertices(theta, sig)
    Q = vertices(theta2, sig2, xr=shift)
    xl = max(P[-1, 0], Q[-1, 0])
    xr = min(P[0, 0], Q[0, 0])
    if xr <= xl:
        return 0.0
    x = np.linspace(xl, xr, grid.nx)
    a, al, _ = cap_fibers(P, grid, x)
    a2, al2, _ = cap_fibers(Q, grid, x)
    top = np.minimum(a, 1 - al2)
    bot = np.maximum(al, 1 - a2)
    ell = np.maximum(top - bot, 0)
    area = np.trapezoid(ell, x)
    if return_parts:
        return dict(x=x, a=a, al=al, a2=a2, al2=al2, ell=ell, area=area,
                    clip=np.trapezoid(np.minimum(al, 1 - a2) +
                                      np.minimum(al2, 1 - a), x))
    return area


def candidate_polygon(n):
    """edge lengths approximating the candidate's upper boundary with n
    interior normals per quarter, plus the vertical end edges and the face."""
    import cand
    # normals: 0 (vertical edge), interior, pi/2 (face), interior, pi
    q = (np.arange(n) + 0.5) / n * L
    theta = np.concatenate([[0.0], q, [L], q + L, [pi]])
    # curvature measure of h_* on each cell: integrate h+h'' = d(h') + h dt
    # use exact one-sided derivatives numerically on cell boundaries
    edges = np.concatenate([[0.0], np.arange(1, n) / n * L, [L],
                            L + np.arange(1, n) / n * L, [pi]])

    def hs(th):
        return cand.h_star_upper(np.atleast_1d(th))[0]

    def dh(th, side):
        e = 1e-7
        if side > 0:
            return (hs(th + e) - hs(th)) / e
        return (hs(th) - hs(th - e)) / e

    sig = []
    # vertical edge at 0: from (x_r,0) up to the support point at 0+:
    sig.append(dh(0.0, +1) - 0.0)  # h'(0+) = y-coordinate of the contact
    # interior cells of the first quarter
    cells = np.concatenate([np.arange(n + 1) / n * L])
    for i in range(n):
        lo, hi = cells[i], cells[i + 1]
        tt = np.linspace(lo, hi, 201)
        hv = cand.h_star_upper(tt)
        mass = (dh(hi, -1) - dh(lo, +1)) + np.trapezoid(hv, tt)
        sig.append(mass)
    # face at pi/2
    sig.append(dh(L, +1) - dh(L, -1))
    for i in range(n):
        lo, hi = L + cells[i], L + cells[i + 1]
        tt = np.linspace(lo, hi, 201)
        hv = cand.h_star_upper(tt)
        mass = (dh(hi, -1) - dh(lo, +1)) + np.trapezoid(hv, tt)
        sig.append(mass)
    sig.append(-dh(pi, -1))  # vertical edge at pi down to y=0
    sig = np.maximum(np.array(sig), 0.0)
    return theta, sig


def normalize(theta, sig):
    """scale the rising edges (theta<pi/2) to reach height exactly 1 and the
    falling edges (theta>pi/2) to return exactly to 0."""
    sig = np.asarray(sig, float).copy()
    up = theta < L - 1e-12
    dn = theta > L + 1e-12
    hu = np.sum(sig[up] * cos(theta[up]))
    hd = -np.sum(sig[dn] * cos(theta[dn]))
    if hu > 0:
        sig[up] /= hu
    if hd > 0:
        sig[dn] /= hd
    return sig
