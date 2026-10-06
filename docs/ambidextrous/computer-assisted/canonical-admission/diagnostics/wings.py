"""Canonical two-wing data for a convex body K in the strip 0<=y<=1.

Floating-point diagnostics only (finite angle and x grids).

Depth of q below the support line of K with normal n_theta:
    Phi_theta(q) = h_K(theta) - q . n_theta .
Ambidextrous envelope (both quarter turns, tight walls):
    T(K) = { q in K : no t in [0,L] u [pi,3L] with Phi_t(q)>1 and Phi_{t+L}(q)>1 }.
Canonical wings:
    R = { q in K : Phi_theta(q) <= 1 for theta in [-L,-beta] u [beta,L] },
    D = { q in K : Phi_theta(q) <= 1 for theta in [L,pi-beta] u [pi+beta,3L] }.
Core curve and functional as in TW.3 / CS.3 (actual inward vertices).
"""
import numpy as np
from numpy import pi, sin, cos
from shapely.geometry import Polygon, box
from shapely import affinity

Y = float(np.real([r for r in np.roots([4, 0, 3, -1]) if abs(np.imag(r)) < 1e-12][0]))
beta = float(np.arctan(Y))
L = pi / 2
bb = L - beta
M = 1 + 4 * Y**2 + np.arctan(Y)


def n(t):
    return np.stack([np.cos(t), np.sin(t)], axis=-1)


def support(P, t):
    """support of polygon vertex array P (m,2) at angles t (any shape)."""
    t = np.asarray(t, dtype=float)
    return (P[:, 0][None, :] * np.cos(t).reshape(-1, 1)
            + P[:, 1][None, :] * np.sin(t).reshape(-1, 1)).max(axis=1).reshape(t.shape)


def halfplane(nrm, c, big=50.0):
    """polygon {p : p.nrm >= c} clipped to a big box."""
    nx, ny = nrm
    # point on line and direction
    p0 = np.array([nx, ny]) * c
    d = np.array([-ny, nx])
    q = np.array([nx, ny])
    pts = [p0 + big * d, p0 - big * d, p0 - big * d + big * q, p0 + big * d + big * q]
    return Polygon(pts)


def canonical_wings(Kpoly, nth=721):
    P = np.array(Kpoly.exterior.coords)[:-1]
    R = Kpoly
    D = Kpoly
    thR = np.concatenate([np.linspace(beta, L, nth), np.linspace(-L, -beta, nth)])
    thD = np.concatenate([np.linspace(L, pi - beta, nth), np.linspace(pi + beta, 3 * L, nth)])
    hR = support(P, thR)
    hD = support(P, thD)
    for t, h in zip(thR, hR):
        R = R.intersection(halfplane((cos(t), sin(t)), h - 1))
        if R.is_empty:
            break
    for t, h in zip(thD, hD):
        D = D.intersection(halfplane((cos(t), sin(t)), h - 1))
        if D.is_empty:
            break
    return R, D


def verts(poly):
    return np.array(poly.exterior.coords)[:-1]


def line_intersection(n1, c1, n2, c2):
    A = np.array([n1, n2])
    return np.linalg.solve(A, np.array([c1, c2]))


def core_curve(Rv, Dv, nt=2001):
    t = np.linspace(beta, bb, nt)
    r = support(Rv, t)
    d = support(Dv, t + L)
    zm = (r - 1)[:, None] * n(t) + (d - 1)[:, None] * n(t + L)
    # reflected supports: h^rho(t) = h(-t) + sin t
    rr = support(Rv, -t) + np.sin(t)
    dr = support(Dv, -(t + L)) + np.sin(t + L)
    w = (rr - 1)[:, None] * n(t) + (dr - 1)[:, None] * n(t + L)
    zp = np.stack([w[:, 0], 1 - w[:, 1]], axis=1)
    return t, zm, zp


def inward_vertices(Rv, Dv):
    c, s = cos(beta), sin(beta)
    r1 = support(Rv, np.array([pi - beta]))[0]
    r2 = support(Rv, np.array([pi + beta]))[0]
    d1 = support(Dv, np.array([beta]))[0]
    d2 = support(Dv, np.array([-beta]))[0]
    IR = np.array([-(r1 + r2) / (2 * c), (r1 - r2) / (2 * s)])
    ID = np.array([(d1 + d2) / (2 * c), (d1 - d2) / (2 * s)])
    return IR, ID


def gamma_polygon(Rv, Dv, nt=2001):
    t, zm, zp = core_curve(Rv, Dv, nt)
    IR, ID = inward_vertices(Rv, Dv)
    G = np.vstack([IR[None, :], zm, ID[None, :], zp[::-1]])
    return G, (t, zm, zp, IR, ID)


def signed_area_cw(G):
    x, y = G[:, 0], G[:, 1]
    a = 0.5 * np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y)
    return -a


def winding_cw(G, Q, chunk=2000):
    """clockwise winding number of closed polygon G around points Q."""
    out = np.zeros(len(Q), dtype=int)
    x0, y0 = G[:, 0], G[:, 1]
    x1, y1 = np.roll(x0, -1), np.roll(y0, -1)
    for i in range(0, len(Q), chunk):
        qx = Q[i:i + chunk, 0][:, None]
        qy = Q[i:i + chunk, 1][:, None]
        up = (y0[None, :] <= qy) & (y1[None, :] > qy)
        dn = (y0[None, :] > qy) & (y1[None, :] <= qy)
        cr = (x1 - x0)[None, :] * (qy - y0[None, :]) - (qx - x0[None, :]) * (y1 - y0)[None, :]
        w = np.sum(up & (cr > 0), axis=1) - np.sum(dn & (cr < 0), axis=1)
        out[i:i + chunk] = -w
    return out


def depth_table(P, Q, th):
    """Phi_theta(q) for points Q (k,2) and angles th (m,)."""
    h = support(P, th)
    return h[None, :] - (Q[:, 0][:, None] * np.cos(th)[None, :]
                         + Q[:, 1][:, None] * np.sin(th)[None, :])


def envelope_mask(P, Q, nt=721):
    """True where q in K survives both niches (tight walls, full turns)."""
    t = np.linspace(0, L, nt)
    t2 = np.linspace(pi, 3 * L, nt)
    ok = np.ones(len(Q), dtype=bool)
    chunk = max(1, int(2e7 // nt))
    for i in range(0, len(Q), chunk):
        Qc = Q[i:i + chunk]
        for tt in (t, t2):
            D1 = depth_table(P, Qc, tt)
            D2 = depth_table(P, Qc, tt + L)
            bad = np.any((D1 > 1) & (D2 > 1), axis=1)
            ok[i:i + chunk] &= ~bad
    return ok


def in_poly_mask(poly, Q):
    from shapely import contains_xy
    return contains_xy(poly, Q[:, 0], Q[:, 1])


def analyze(Kpoly, ngrid=500, nth=721, verbose=True):
    P = verts(Kpoly)
    R, D = canonical_wings(Kpoly, nth)
    out = {}
    if R.is_empty or D.is_empty:
        out["empty_wing"] = True
        return out
    Rv, Dv = verts(R), verts(D)
    G, (t, zm, zp, IR, ID) = gamma_polygon(Rv, Dv)
    core = signed_area_cw(G)
    What = R.area + D.area + core
    xmin, ymin, xmax, ymax = Kpoly.bounds
    xs = np.linspace(xmin, xmax, ngrid)
    ys = np.linspace(0, 1, int(ngrid / (xmax - xmin)) + 2)
    XX, YY = np.meshgrid(xs, ys)
    Q = np.stack([XX.ravel(), YY.ravel()], axis=1)
    dA = (xs[1] - xs[0]) * (ys[1] - ys[0])
    inK = in_poly_mask(Kpoly, Q)
    Tm = np.zeros(len(Q), dtype=bool)
    Tm[inK] = envelope_mask(P, Q[inK], nt=nth)
    inR = in_poly_mask(R, Q)
    inD = in_poly_mask(D, Q)
    w = winding_cw(G, Q)
    rest = Tm & ~inR & ~inD
    out.update(
        T=Tm.sum() * dA, R=R.area, D=D.area, core=core, What=What,
        rest=rest.sum() * dA,
        bad_rest=(rest & (w < 1)).sum() * dA,
        neg=(w < 0).sum() * dA,
        overlapRD=R.intersection(D).area,
        Rbounds=R.bounds, Dbounds=D.bounds,
        IR=IR, ID=ID,
    )
    # cut slacks
    def width(V, th):
        return support(V, np.array([th]))[0] + support(V, np.array([th + pi]))[0]
    out["slack"] = (1 - width(Rv, beta), 1 - width(Rv, -beta),
                    1 - width(Dv, beta), 1 - width(Dv, -beta))
    out["grid"] = (Q, Tm, inR, inD, w)
    out["curves"] = (G, t, zm, zp)
    if verbose:
        print("|T|=%.5f  What=%.5f (R %.4f D %.4f core %.4f)  rest=%.5f bad_rest=%.2e neg=%.2e"
              % (out["T"], What, R.area, D.area, core, out["rest"], out["bad_rest"], out["neg"]))
        print("  R y-range [%.4f,%.4f]  D y-range [%.4f,%.4f]  slacks %s  M=%.5f"
              % (R.bounds[1], R.bounds[3], D.bounds[1], D.bounds[3],
                 np.round(out["slack"], 4), M))
    return out


# ------------------------------------------------------------ test bodies
def body_from_support(hfun, nv=1500):
    """polygon from support function on [0,2pi) via vertices of tangent lines."""
    th = np.linspace(0, 2 * pi, nv, endpoint=False)
    h = hfun(th)
    # vertices: intersection of consecutive support lines
    t1, t2 = th, np.roll(th, -1)
    h1, h2 = h, np.roll(h, -1)
    det = np.sin(t2 - t1)
    x = (h1 * np.sin(t2) - h2 * np.sin(t1)) / det
    y = (h2 * np.cos(t1) - h1 * np.cos(t2)) / det
    poly = Polygon(np.stack([x, y], axis=1)).buffer(0)
    return poly


def candidate_hull(nv=2000):
    import sys
    import cand
    def h(th):
        th = np.mod(th, 2 * pi)
        out = np.empty_like(th)
        up = th <= pi
        out[up] = cand.h_star_upper(th[up])
        # lower half by rho-symmetry: h(-t) = h(t) - sin t for t in [0,pi]
        tt = 2 * pi - th[~up]
        out[~up] = cand.h_star_upper(tt) - np.sin(tt)
        return out
    return body_from_support(h, nv)


if __name__ == "__main__":
    K = candidate_hull()
    print("candidate hull area %.5f, bounds %s" % (K.area, np.round(K.bounds, 4)))
    analyze(K)
