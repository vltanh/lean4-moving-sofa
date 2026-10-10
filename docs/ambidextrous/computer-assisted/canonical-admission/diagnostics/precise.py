"""Higher-resolution fiber computations for T(K), canonical wings, What.

All floating point; diagnostics only.
"""
import numpy as np
from numpy import pi, sin, cos
from shapely.geometry import Polygon, MultiPoint, LineString
import wings as W

L = pi / 2
beta, bb, M = W.beta, W.bb, W.M


def hK(P, t):
    return W.support(P, t)


def roofs(P, x, nt=6000):
    """lower roof F(x) and upper roof Frho(x) (depth from y=1)."""
    t = np.linspace(0, L, nt + 2)[1:-1]
    f = hK(P, t)
    g = hK(P, t + L)
    st, ct = np.sin(t), np.cos(t)
    F = np.full(len(x), -np.inf)
    Fr = np.full(len(x), -np.inf)
    # reflected supports: h^rho(t) = h(-t) + sin t
    fr = hK(P, -t) + st
    gr = hK(P, -(t + L)) + np.sin(t + L)
    for i0 in range(0, len(x), 400):
        xx = x[i0:i0 + 400][:, None]
        Rt = (f[None, :] - 1 - xx * ct[None, :]) / st[None, :]
        Lt = (g[None, :] - 1 + xx * st[None, :]) / ct[None, :]
        F[i0:i0 + 400] = np.minimum(Rt, Lt).max(axis=1)
        Rt = (fr[None, :] - 1 - xx * ct[None, :]) / st[None, :]
        Lt = (gr[None, :] - 1 + xx * st[None, :]) / ct[None, :]
        Fr[i0:i0 + 400] = np.minimum(Rt, Lt).max(axis=1)
    return F, Fr


def fibers(poly, x):
    """[lo, hi] of vertical fibers of a convex polygon."""
    lo = np.full(len(x), np.nan)
    hi = np.full(len(x), np.nan)
    xmin, ymin, xmax, ymax = poly.bounds
    for i, xv in enumerate(x):
        if xv <= xmin or xv >= xmax:
            continue
        seg = poly.intersection(LineString([(xv, ymin - 1), (xv, ymax + 1)]))
        if seg.is_empty:
            continue
        b = seg.bounds
        lo[i], hi[i] = b[1], b[3]
    return lo, hi


def T_fibers(K, x, nt=6000):
    P = W.verts(K)
    b, a = fibers(K, x)
    F, Fr = roofs(P, x, nt)
    lo = np.maximum(b, F)
    hi = np.minimum(a, 1 - Fr)
    return lo, hi


def interval_minus(lo, hi, cuts):
    """length of [lo,hi] minus union of intervals in cuts (list of (l,h))."""
    if not (hi > lo):
        return 0.0
    segs = sorted([(max(l, lo), min(h, hi)) for (l, h) in cuts
                   if not (np.isnan(l) or np.isnan(h)) and min(h, hi) > max(l, lo)])
    tot = 0.0
    cur = lo
    for l, h in segs:
        if l > cur:
            tot += l - cur
        cur = max(cur, h)
    if hi > cur:
        tot += hi - cur
    return tot


def saturate(K, x, iters=6, nt=4000, tol=1e-6):
    """K <- conv(T(K)) repeatedly (fiber representation)."""
    for it in range(iters):
        lo, hi = T_fibers(K, x, nt)
        ok = hi > lo + 1e-12
        pts = np.concatenate([np.stack([x[ok], lo[ok]], 1), np.stack([x[ok], hi[ok]], 1)])
        K2 = MultiPoint(pts).convex_hull
        d = K.area - K2.area
        K = K2
        if d < tol:
            break
    return K


def full_analysis(K, nx=3000, nt=6000, nth=1441, verbose=True):
    P = W.verts(K)
    R, D = W.canonical_wings(K, nth)
    Rv, Dv = W.verts(R), W.verts(D)
    G, (t, zm, zp, IR, ID) = W.gamma_polygon(Rv, Dv, nt=4001)
    core = W.signed_area_cw(G)
    What = R.area + D.area + core
    xmin, _, xmax, _ = K.bounds
    x = np.linspace(xmin, xmax, nx + 2)[1:-1]
    dx = x[1] - x[0]
    lo, hi = T_fibers(K, x, nt)
    Tlen = np.maximum(hi - lo, 0)
    rlo, rhi = fibers(R, x)
    dlo, dhi = fibers(D, x)
    rest = np.array([interval_minus(lo[i], hi[i], [(rlo[i], rhi[i]), (dlo[i], dhi[i])])
                     for i in range(len(x))])
    Tarea = Tlen.sum() * dx
    restarea = rest.sum() * dx
    # contact velocity at the four junctions, from wing supports
    eps = 1e-5
    def pr(tt):
        r = lambda s: W.support(Rv, np.array([s]))[0]
        d = lambda s: W.support(Dv, np.array([s]))[0]
        rp = (r(tt + eps) - r(tt - eps)) / (2 * eps)
        return rp - d(tt + L) + 1
    p_beta = pr(beta)
    out = dict(T=Tarea, What=What, R=R.area, D=D.area, core=core, rest=restarea,
               p_beta=p_beta, Rb=R.bounds, Db=D.bounds, IR=IR, ID=ID, K=K, Rpoly=R, Dpoly=D,
               G=G)
    if verbose:
        print("|T|=%.6f What=%.6f  What-|T|=%+.6f  M-What=%.6f | rest=%.6f core=%.6f rest-core=%+.6f | p(beta)=%+.4f"
              % (Tarea, What, What - Tarea, M - What, restarea, core, restarea - core, p_beta))
        print("   R y[%.4f,%.4f]  D y[%.4f,%.4f]  K area %.5f W=%.4f"
              % (R.bounds[1], R.bounds[3], D.bounds[1], D.bounds[3], K.area, xmax - xmin))
    return out


if __name__ == "__main__":
    K = W.candidate_hull(3000)
    full_analysis(K)
