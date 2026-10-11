"""A continuous-motion safety margin, evaluated using floating-point polygons."""
from __future__ import annotations

import math
import numpy as np
from geometry import Motion, largest_component, polygons, sampled_intersection


def enclose(motion: Motion, subdivisions: int = 32, audit: bool = False):
    """Return an inner construction and an outer approximation for ONE path.

    The inclusion theorem is in THEORY.md. GEOS and NumPy are not interval
    arithmetic, so the returned decimals are not machine-certified bounds.
    """
    raw = sampled_intersection(motion, subdivisions)
    parts = list(polygons(raw))
    if not parts:
        return {"sampled_area": 0.0, "sampled_total_area": 0.0,
                "inner_area": 0.0, "margin": 0.0, "radius_bound": 0.0,
                "samples": (len(motion.corners)-1)*subdivisions+1,
                "sampled_components": 0, "inner_components": 0,
                "audit_outside_area": 0.0 if audit else None}, largest_component(raw)
    verts = np.concatenate([np.asarray(p.exterior.coords) for p in parts])
    # A convex norm is maximized at polygon vertices and path-segment ends.
    radius = max(float(np.linalg.norm(verts-c, axis=1).max()) for c in motion.corners)
    delta_theta = abs(motion.turn)/((len(motion.corners)-1)*subdivisions)
    delta_corner = float(np.linalg.norm(np.diff(motion.corners, axis=0), axis=1).max())/subdivisions
    analytic_margin = 2.0*radius*math.sin(delta_theta/4.0)+delta_corner/2.0
    numerical_guard = 1e-10*max(1.0, radius)  # heuristic only; not a rounding proof
    inner_geometry = sampled_intersection(motion, subdivisions, analytic_margin+numerical_guard)
    inner = largest_component(inner_geometry)
    audit_outside = None
    if audit:
        denser = sampled_intersection(motion, subdivisions*2)
        audit_outside = float(inner.difference(denser).area)
    record = {"sampled_area": float(largest_component(raw).area),
              "sampled_total_area": float(raw.area), "inner_area": float(inner.area),
              "margin": analytic_margin+numerical_guard, "radius_bound": radius,
              "samples": (len(motion.corners)-1)*subdivisions+1,
              "sampled_components": len(parts),
              "inner_components": len(list(polygons(inner_geometry))),
              "audit_outside_area": audit_outside}
    return record, inner
