"""Romik's ambidextrous candidate, from the exact support formulas of note 14,
and a fiberwise area calculator for two-turn bodies.

Sofa frame: strip 0<=y<=1.  An *upper cap* U is described by its support
function h on [0, pi] (h(pi/2)=1).  Its right-turn niche is the union over
t in (0, pi/2) of the open quadrants
    { p : p.mu_t < h(t)-1, p.nu_t < h(t+pi/2)-1 },  mu=(cos,sin), nu=(-sin,cos),
intersected with y>=0.  T_U = U minus niche is Baek's monotone sofa.
The ambidextrous envelope of a pair (U, U') is T_U  cap  rho(T_U'),
rho(x,y)=(x,1-y).
"""
import numpy as np
from numpy import sin, cos, pi, arctan, sqrt

# ---------------------------------------------------------------- constants
Y = np.roots([4, 0, 3, -1])
Y = float(np.real(Y[np.argmin(abs(np.imag(Y)))]))
beta = arctan(Y)
L = pi / 2
b = L - beta
s, c = sin(beta), cos(beta)
A = 1 / (4 * s)
k = 1 - 4 * A / 3
T = 1.5 * (pi / 4 - beta)
R = c / cos(T)
M = 1 + 4 * Y**2 + arctan(Y)


def fg_star(t):
    """(f_*(t), g_*(t)) for t in [0, L] (vectorised)."""
    t = np.asarray(t, dtype=float)
    f = np.empty_like(t)
    g = np.empty_like(t)
    m1 = t <= beta
    m3 = t >= b
    m2 = ~(m1 | m3)
    tt = t[m1]
    f[m1] = cos(tt) + 0.5 * sin(tt)
    g[m1] = (2 * A - 1) * sin(tt) + 0.5 * cos(tt) + 0.5
    tt = t[m2]
    f[m2] = R * cos(tt / 2 + pi / 8) + k * cos(tt) + 0.5 * sin(tt)
    g[m2] = R * sin(tt / 2 + pi / 8) - k * sin(tt) + 0.5 * cos(tt)
    tt = t[m3]
    f[m3] = (1 - 2 * A / 3) * cos(tt) + 0.5 * sin(tt) + 0.5
    g[m3] = (8 * A / 3 - 1) * sin(tt) + 0.5 * cos(tt)
    return f, g


def h_star_upper(theta):
    """support function of the candidate on [0, pi]."""
    theta = np.asarray(theta, dtype=float)
    out = np.empty_like(theta)
    lo = theta <= L
    out[lo] = fg_star(theta[lo])[0]
    out[~lo] = fg_star(theta[~lo] - L)[1]
    return out


# ---------------------------------------------------------------- fibers
def top_profile(theta, h, x):
    """a(x) = min(1, min_theta (h(theta) - x cos theta)/sin theta) over
    interior normals; theta grid strictly inside (0, pi)."""
    st = sin(theta)[None, :]
    ct = cos(theta)[None, :]
    vals = (h[None, :] - x[:, None] * ct) / st
    return np.minimum(1.0, vals.min(axis=1))


def roof_profile(t, f, g, x):
    """signed roof F(x) = sup_t min(R_t(x), L_t(x)) over interior t."""
    st = sin(t)[None, :]
    ct = cos(t)[None, :]
    Rt = (f[None, :] - 1 - x[:, None] * ct) / st
    Lt = (g[None, :] - 1 + x[:, None] * st) / ct
    return np.minimum(Rt, Lt).max(axis=1)


def cap_data(hfun, nt=4000, nx=6000):
    """Return x grid, top a(x), niche roof alpha(x)>=0, width, extents."""
    t = np.linspace(0, L, nt + 2)[1:-1]
    f = hfun(t)
    g = hfun(t + L)
    th = np.linspace(0, pi, 2 * nt + 2)[1:-1]
    hth = hfun(th)
    xr = float(hfun(np.array([0.0]))[0])
    xl = -float(hfun(np.array([pi]))[0])
    x = np.linspace(xl, xr, nx)
    a = top_profile(th, hth, x)
    a = np.maximum(a, 0.0)
    F = roof_profile(t, f, g, x)
    return dict(x=x, a=a, F=F, alpha=np.maximum(F, 0.0), xl=xl, xr=xr,
                W=xr - xl)


def trap(y, x):
    return float(np.trapezoid(y, x))


if __name__ == "__main__":
    print("Y=%.15f beta=%.15f A=%.15f R=%.15f" % (Y, beta, A, R))
    print("M = 1+4Y^2+atan Y = %.15f" % M)
    print("W = 8A/3 = %.15f, face 4A/3 = %.15f" % (8 * A / 3, 4 * A / 3))
    d = cap_data(h_star_upper, nt=3000, nx=8001)
    x, a, al = d["x"], d["a"], d["alpha"]
    TU = trap(a - al, x)
    U = trap(a, x)
    print("|U*| = %.9f  |N(U*)| = %.9f  |T_U*| = %.9f  W = %.9f" %
          (U, trap(al, x), TU, d["W"]))
    print("Psi(U*) = |T|-W/2 = %.9f ; 2 Psi = %.9f ; M = %.9f" %
          (TU - d["W"] / 2, 2 * TU - d["W"], M))
    # ambidextrous envelope with U' = U*
    top = np.minimum(a, 1 - al)
    bot = np.maximum(al, 1 - a)
    E = trap(np.maximum(top - bot, 0), x)
    clip = trap(np.minimum(al, 1 - a), x)
    print("|E(U*,U*)| = %.9f   clipping = %.3e   max niche height = %.6f" %
          (E, clip, al.max()))
