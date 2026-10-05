"""Exposed-wall shape derivatives for sampled hallway intersections.

This is a local nonconvex objective, not Baek's concave majorant. Derivatives
hold where the active edge assignment and largest component do not change.
"""
from __future__ import annotations
import numpy as np
from shapely.geometry import Polygon
from shapely.ops import unary_union
from geometry import Motion, largest_component, normals
try:
    from numba import njit
except ImportError:
    def njit(*args, **kwargs):
        return lambda f: f

@njit(cache=True)
def clip(vertices, normal, rhs):
    if len(vertices) == 0:
        return np.empty((0, 2))
    out = np.empty((len(vertices)+2, 2))
    k = 0
    px, py = vertices[-1]
    dp = px*normal[0]+py*normal[1]-rhs
    for i in range(len(vertices)):
        cx, cy = vertices[i]
        dc = cx*normal[0]+cy*normal[1]-rhs
        if (dp <= 0) != (dc <= 0):
            f = dp/(dp-dc)
            out[k, 0], out[k, 1] = px+(cx-px)*f, py+(cy-py)*f
            k += 1
        if dc <= 0:
            out[k, 0], out[k, 1] = cx, cy
            k += 1
        px, py, dp = cx, cy, dc
    return out[:k]

@njit(cache=True)
def cap_polygon(rect, ns, offsets):
    cap = rect.copy()
    for i in range(len(ns)):
        cap = clip(cap, ns[i], offsets[i]+1.)
        if len(cap) < 3:
            break
    return cap

@njit(cache=True)
def assign_edges(vertices, ns, offsets, tol):
    """Accumulate signed active-wall lengths, using both edge endpoints."""
    lengths = np.zeros(len(ns))
    missed = 0.0
    tied = 0.0
    for e in range(len(vertices)-1):
        a, b = vertices[e], vertices[e+1]
        length = np.sqrt((b[0]-a[0])**2+(b[1]-a[1])**2)
        if length < tol:
            continue
        # Entry/exit strip boundaries are fixed, not optimizer coordinates.
        if (abs(a[1]) < tol and abs(b[1]) < tol) or (abs(a[1]-1) < tol and abs(b[1]-1) < tol):
            continue
        best = 1e100
        best_i = -1
        sign = 0.0
        matches = 0
        for i in range(len(ns)):
            da = a[0]*ns[i,0]+a[1]*ns[i,1]-offsets[i]
            db = b[0]*ns[i,0]+b[1]*ns[i,1]-offsets[i]
            outer = max(abs(da-1),abs(db-1))
            inner = max(abs(da),abs(db))
            err = min(outer,inner)
            if err < tol:
                matches += 1
            if err < best:
                best, best_i = err, i
                sign = 1.0 if outer < inner else -1.0
        if best > tol:
            missed += length
        else:
            lengths[best_i] += sign*length
            if matches > 1:
                tied += length
    return lengths, missed, tied


def area_gradient(motion: Motion, subdivisions: int = 1):
    """Return (area, gradient per sampled corner, diagnostics).

    Tied active walls receive a deterministic one-sided assignment; there is
    generally no classical gradient at such configurations. Never call this
    an exact-arithmetic or global-optimization certificate.
    """
    angles, corners = motion.sample(subdivisions)
    ns = normals(motion.beta, angles).reshape(-1, 2)
    offsets = np.sum(ns*np.repeat(corners, 2, axis=0), axis=1)
    cap = cap_polygon(motion.bounding_rectangle(), ns, offsets)
    grad = np.zeros_like(corners)
    if len(cap) < 3:
        return 0.0, grad, {"unassigned_length": 0., "tied_length": 0., "components": 0}
    cuts = []
    for i in range(len(corners)):
        w = clip(clip(cap, ns[2*i], offsets[2*i]), ns[2*i+1], offsets[2*i+1])
        if len(w) >= 3:
            cuts.append(Polygon(w))
    shape = Polygon(cap).difference(unary_union(cuts)) if cuts else Polygon(cap)
    if not shape.is_valid:
        raise ArithmeticError("invalid GEOS intersection")
    sofa = largest_component(shape)
    if sofa.is_empty:
        return 0.0, grad, {"unassigned_length": 0., "tied_length": 0., "components": 0}
    tol = 1e-9 * max(1.0, float(np.max(np.abs(cap))))
    lengths = np.zeros(len(ns))
    missed = tied = 0.0
    for ring in [sofa.exterior, *sofa.interiors]:
        l, m, t = assign_edges(np.asarray(ring.coords), ns, offsets, tol)
        lengths += l
        missed += m
        tied += t
    grad = (lengths[:,None]*ns).reshape(-1,2,2).sum(axis=1)
    grad[[0,-1],1] = 0.0  # heights are fixed by the Motion model
    return float(sofa.area), grad, {"unassigned_length": missed, "tied_length": tied,
        "components": 1 if shape.geom_type == "Polygon" else len(shape.geoms)}
