"""Sharp unit-width hallways with arbitrary bend angle (radians).

Float geometry is exploratory, not interval-certified. No plotting or network I/O.
"""
from __future__ import annotations

from dataclasses import dataclass
import math
import numpy as np
from numpy.typing import NDArray
from shapely.geometry import GeometryCollection, Polygon
from shapely.ops import unary_union

Array = NDArray[np.float64]


def validate_beta(beta: float) -> None:
    if not math.isfinite(beta) or not 0.0 < beta < math.pi:
        raise ValueError("bend angle beta must lie strictly between 0 and pi")


def normals(beta: float, theta: Array | float) -> Array:
    """Outward normals to the two outer walls after rotating the hallway."""
    validate_beta(beta)
    t = np.asarray(theta, dtype=float)
    return np.stack((np.stack((-np.sin(t), np.cos(t)), axis=-1),
                     np.stack((np.sin(beta-t), np.cos(beta-t)), axis=-1)), axis=-2)


def clearance(points: Array, beta: float, theta: float, corner: Array) -> Array:
    """Nonnegative iff inside; 1-Lipschitz clearance sufficient for disk safety."""
    f = (np.asarray(points, dtype=float) - corner) @ normals(beta, theta).T
    return np.minimum(1.0 - np.max(f, axis=-1), np.max(f, axis=-1))


def clip_halfplane(vertices: Array, normal: Array, rhs: float) -> Array:
    """Clip a convex polygon by normal.dot(x) <= rhs; no tolerance expansion."""
    if len(vertices) == 0:
        return np.empty((0, 2), dtype=float)
    result = []
    prev = vertices[-1]
    dp = float(prev @ normal - rhs)
    for curr in vertices:
        dc = float(curr @ normal - rhs)
        if (dp <= 0.0) != (dc <= 0.0):
            result.append(prev + (curr - prev) * (dp / (dp - dc)))
        if dc <= 0.0:
            result.append(curr)
        prev, dp = curr, dc
    return np.asarray(result, dtype=float).reshape(-1, 2)


def polygons(geometry):
    if geometry.geom_type == "Polygon":
        if geometry.area > 0.0:
            yield geometry
    elif hasattr(geometry, "geoms"):
        for part in geometry.geoms:
            yield from polygons(part)


def largest_component(geometry) -> Polygon:
    return max(polygons(geometry), key=lambda p: p.area, default=Polygon())


@dataclass(frozen=True)
class Motion:
    """Piecewise-linear corner and angle paths on parameter u in [0,1].

    'forward': hallway rotates beta, endpoint corner heights 0 and 0.
    'reverse': hallway rotates beta-pi, endpoint heights 0 and 1.
    These are two restricted motion families, not an exhaustive reduction.
    """
    beta: float
    mode: str
    corners: Array

    def __post_init__(self) -> None:
        validate_beta(self.beta)
        if self.mode not in ("forward", "reverse"):
            raise ValueError("mode must be forward or reverse")
        c = np.array(self.corners, dtype=float, copy=True)
        if c.ndim != 2 or c.shape[1] != 2 or len(c) < 3 or len(c) % 2 != 1:
            raise ValueError("corners must have odd shape (k,2), k >= 3")
        if not np.isfinite(c).all():
            raise ValueError("corners must be finite")
        end_y = 0.0 if self.mode == "forward" else 1.0
        if c[0, 1] != 0.0 or c[-1, 1] != end_y:
            raise ValueError("endpoint heights do not match entry/exit strips")
        c.setflags(write=False)
        object.__setattr__(self, "corners", c)

    @property
    def turn(self) -> float:
        return self.beta if self.mode == "forward" else self.beta - math.pi

    def sample(self, subdivisions: int) -> tuple[Array, Array]:
        if not isinstance(subdivisions, int) or isinstance(subdivisions, bool) or subdivisions < 1:
            raise ValueError("subdivisions must be a positive integer")
        u = np.linspace(0.0, 1.0, (len(self.corners)-1)*subdivisions+1)
        knots = np.linspace(0.0, 1.0, len(self.corners))
        c = np.column_stack([np.interp(u, knots, self.corners[:, j]) for j in range(2)])
        return self.turn*u, c

    def bounding_rectangle(self) -> Array:
        """A bound implied by the middle hallway and the fixed entry strip.

        The extra unit padding is irrelevant: the derived bounds already
        contain the intersection. No arbitrary search-box truncation is used.
        """
        cx, cy = self.corners[len(self.corners)//2]
        s, c = math.sin(self.beta/2), math.cos(self.beta/2)
        m = max(abs(cy), abs(1.0-cy))
        if self.mode == "forward":
            dx = (1.0+c*m)/s
            lo, hi = cx-dx, cx+dx
        else:
            lo, hi = cx-s*m/c, cx+(1.0+s*m)/c
        return np.array([[lo-1, 0], [hi+1, 0], [hi+1, 1], [lo-1, 1]], dtype=float)


def sampled_intersection(motion: Motion, subdivisions: int = 1, margin: float = 0.0):
    """Intersection of finitely many hallways with a sufficient linear margin.

    This is an OUTER approximation for the chosen continuous path when margin
    is zero. Local maximization of its area is not a global upper bound.
    """
    if not math.isfinite(margin) or margin < 0.0:
        raise ValueError("margin must be finite and nonnegative")
    angles, corners = motion.sample(subdivisions)
    ns = normals(motion.beta, angles)
    cap = motion.bounding_rectangle()
    for pair, corner in zip(ns, corners, strict=True):
        for n in pair:
            cap = clip_halfplane(cap, n, float(n @ corner + 1.0-margin))
            if len(cap) < 3:
                return Polygon()
    outer = Polygon(cap)
    if outer.area == 0.0:
        return Polygon()
    cuts = []
    for pair, corner in zip(ns, corners, strict=True):
        wedge = cap
        for n in pair:
            wedge = clip_halfplane(wedge, n, float(n @ corner + margin))
        if len(wedge) >= 3:
            p = Polygon(wedge)
            if p.area > 0.0:
                cuts.append(p)
    result = outer.difference(unary_union(cuts)) if cuts else outer
    if not result.is_valid:
        raise ArithmeticError("GEOS returned invalid polygon geometry")
    return result


def stationary_area(beta: float) -> float:
    """Exact area for a fixed inner corner, forward rotation, and entry strip."""
    validate_beta(beta)
    return beta + 1.0/math.tan(beta) if beta < math.pi/2 else math.pi/2


def translation_area(beta: float) -> float:
    """Exact optimum among motions using translations only."""
    validate_beta(beta)
    return 1.0/math.sin(beta)
