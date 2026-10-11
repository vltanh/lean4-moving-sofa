"""Tighter continuous-motion inner constructions from swept-wedge enclosures.

The exact-real argument is in SWEPT_ENCLOSURE.md. GEOS is not certified arithmetic.
"""
from __future__ import annotations

import math
import numpy as np
from shapely.geometry import MultiPoint, Polygon
from shapely.ops import unary_union

from geometry import (Motion, clip_halfplane, largest_component, normals,
                      polygons, sampled_intersection)


def clip_fast(vertices, normal, rhs):
    """Vectorized equivalent of clip_halfplane for long convex polygons."""
    if len(vertices) < 16:
        return clip_halfplane(vertices, normal, rhs)
    d = vertices @ normal-rhs
    inside = d <= 0.0
    previous = np.roll(vertices, 1, axis=0)
    dp = np.roll(d, 1)
    cross = inside != np.roll(inside, 1)
    counts = inside.astype(int)+cross.astype(int)
    start = np.cumsum(counts)-counts
    result = np.empty((int(counts.sum()), 2), dtype=float)
    result[start[cross]] = previous[cross]+(vertices[cross]-previous[cross])*(dp[cross]/(dp[cross]-d[cross]))[:, None]
    result[start[inside]+cross[inside].astype(int)] = vertices[inside]
    return result


def offset_convex_intersection(cap, hull: Polygon, distance: float):
    """Intersect cap with shifted supporting halfplanes of a convex polygon.

    This MITERED outer offset contains hull + the Euclidean distance disk.
    No polygonal approximation to a circular buffer is used.
    """
    vertices = np.asarray(hull.exterior.coords)[:-1]
    if not hull.exterior.is_ccw:
        vertices = vertices[::-1]
    result = cap
    for a, b in zip(vertices, np.roll(vertices, -1, axis=0), strict=True):
        edge = b-a
        length = float(np.linalg.norm(edge))
        if length == 0:
            continue
        n = np.array([edge[1], -edge[0]])/length
        result = clip_fast(result, n, float(n@a+distance))
        if len(result) < 3:
            return Polygon()
    return Polygon(result)


def enclose_swept(motion: Motion, subdivisions: int = 32, audit: bool = False):
    raw = sampled_intersection(motion, subdivisions)
    parts = list(polygons(raw))
    record = {"method": "swept_hull_second_order", "samples": (len(motion.corners)-1)*subdivisions+1,
              "sampled_area": float(largest_component(raw).area),
              "sampled_total_area": float(raw.area), "sampled_components": len(parts),
              "inner_area": 0.0, "inner_components": 0, "radius_bound": 0.0,
              "outer_margin": 0.0, "sweep_margin": 0.0,
              "audit_outside_area": 0.0 if audit else None}
    if not parts:
        return record, Polygon()
    verts = np.concatenate([np.asarray(p.exterior.coords) for p in parts])
    radius = max(float(np.linalg.norm(verts-c, axis=1).max()) for c in motion.corners)
    angles, corners = motion.sample(subdivisions)
    ns = normals(motion.beta, angles)
    delta = abs(motion.turn)/(len(angles)-1)
    d = float(np.linalg.norm(np.diff(motion.corners, axis=0), axis=1).max())/subdivisions
    guard = 1e-10*max(1.0, radius)  # heuristic rounding slack, NOT a proof
    outer_margin = (radius+2.0*d/delta)*delta*delta/8.0+guard
    sweep_margin = radius*delta*delta/8.0+guard
    record.update(radius_bound=radius, outer_margin=outer_margin, sweep_margin=sweep_margin)
    cap = motion.bounding_rectangle()
    base = cap.copy()
    for pair, corner in zip(ns, corners, strict=True):
        for n in pair:
            cap = clip_halfplane(cap, n, float(n@corner+1.0-outer_margin))
        if len(cap) < 3:
            return record, Polygon()
    # An endpoint image of a point in a moving wedge can lie outside the raw
    # sofa box. Expand BEFORE clipping endpoint wedges, as required by proof.
    padding = 2.0*radius*math.sin(delta/2.0)+d+1.0
    lo = base.min(axis=0)-padding
    hi = base.max(axis=0)+padding
    expanded = np.array([[lo[0],lo[1]], [hi[0],lo[1]], [hi[0],hi[1]], [lo[0],hi[1]]])
    wedges = []
    for pair, corner in zip(ns, corners, strict=True):
        w = expanded
        for n in pair:
            w = clip_halfplane(w, n, float(n@corner))
        wedges.append(w)
    cuts = []
    for a, b in zip(wedges[:-1], wedges[1:], strict=True):
        points = np.vstack((a, b))
        if len(points) == 0:
            continue
        hull = MultiPoint(points).convex_hull
        if hull.geom_type != "Polygon":
            # The padded box gives an interior neighborhood for every relevant
            # wedge point. Degenerate hulls should never meet the raw sofa.
            if not hull.is_empty and hull.distance(Polygon(cap)) <= sweep_margin:
                raise ArithmeticError("degenerate swept hull meets candidate cap")
            continue
        cut = offset_convex_intersection(cap, hull, sweep_margin)
        if cut.area > 0.0:
            cuts.append(cut)
    geometry = Polygon(cap).difference(unary_union(cuts)) if cuts else Polygon(cap)
    if not geometry.is_valid:
        raise ArithmeticError("GEOS returned invalid swept enclosure")
    inner = largest_component(geometry)
    record.update(inner_area=float(inner.area), inner_components=len(list(polygons(geometry))))
    if audit:
        denser = sampled_intersection(motion, subdivisions*2)
        record["audit_outside_area"] = float(inner.difference(denser).area)
    return record, inner
