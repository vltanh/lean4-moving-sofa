"""Exact finite-position witness for the full-turn n-mesh including both 45° frames.

IMPORTANT: Proves A_n >= rational number > 33/20 for n=32, not a
continuously moving sofa!  Each 3-4-5-style rational frame may use an
independent placement. Connectedness of the resulting finite body is checked
over the entire x interval by integer uniform roof/niche bounds.

Run from docs/ambidextrous/computer-assisted:
python certified_mesh_witness_165.py 32 100000

Requires numpy; reuses already committed certified_near_reference_165.py for
exact algebraic intervals enclosing the reference convex-hull supports.
All decisions, including 45° radicals, are conservative integer bounds.
"""
import sys, json, time
from math import isqrt
from fractions import Fraction
import numpy as np
from certified_near_reference_165 import P, support_samples


def certified_witness(n=32, cells=100000):
    assert 4 <= n <= 512 and cells > 0
    t0 = time.perf_counter()
    m, rows = support_samples(n)
    half = 1167049000000  # 1.167049 < reference half-width m
    assert 0 < half < m.lo
    assert 2 * half % cells == 0
    dx = 2 * half // cells
    xl = -half + dx * np.arange(cells, dtype=np.int64)
    xr = xl + dx
    outer_lower = np.full(cells, P, dtype=np.int64)
    niche_upper = np.zeros(cells, dtype=np.int64)
    # Each row gives an exact rational (c,s)=(cn/d,sn/d), and algebraic
    # support bounds flo<=Q*f_*<=fhi and glo<=Q*g_*<=ghi.
    for cn, sn, d, flo, fhi, glo, ghi, _ in rows:
        F = (flo + fhi)//2
        G = (glo + ghi)//2
        assert 0 < cn and 0 < sn and cn <= d and sn <= d
        assert max(abs(F), abs(G), P) * d + max(cn, sn)*half < 2**62
        # Lower bound outer y roof valid for every x in the whole cell:
        ua = np.floor_divide(F*d-cn*xr, sn)
        ub = np.floor_divide(G*d+sn*xl, cn)
        outer_lower = np.minimum(outer_lower, np.minimum(ua, ub))
        # Upper bound on the lower inner forbidden niche, on whole cell:
        na = np.floor_divide((F-P)*d-cn*xl+sn-1, sn)
        nb = np.floor_divide((G-P)*d+sn*xr+cn-1, cn)
        niche_upper = np.maximum(niche_upper, np.minimum(na, nb))

    # ADD the exact 45° hallway. The two unit normals are
    # (1/sqrt(2),1/sqrt(2)) and (-1/sqrt(2),1/sqrt(2)).
    # Reference midpoint f=g=(R+1/2)/sqrt(2); choose nearby rational
    # F/Q independently of the true sofa support, as a hallway offset.
    sqrt2lo = isqrt(2*P*P)
    sqrt2hi = sqrt2lo + 1
    clo = isqrt(P*P//2)
    Rlo, Rhi = 1302051691595, 1302051691636
    F = ((Rlo+Rhi)//2 + P//2)*clo//P
    assert F > P
    outerlo = F*sqrt2lo//P
    innerhi = ((F-P)*sqrt2hi+P-1)//P
    outer_lower = np.minimum(outer_lower,
                             np.minimum(outerlo-xr, outerlo+xl))
    niche_upper = np.maximum(niche_upper,
                             np.minimum(innerhi-xl, innerhi+xr))

    assert np.max(outer_lower) <= P
    assert int(np.min(outer_lower)) >= P//2
    assert int(np.max(niche_upper)) <= P//2
    # The full finite intersection has nonempty interval y-fibers all
    # containing y=1/2. Therefore it is connected.
    length_low = np.maximum(
        0, 2*np.minimum(outer_lower, P-niche_upper)-P)
    total = int(np.sum(length_low, dtype=np.int64))
    assert total < 2**62
    area = Fraction(total*dx, P*P)
    threshold = Fraction(33,20)
    return {
        "type": "connected_finite_position_witness_NOT_continuous_turns",
        "n": n, "interior_rational_angles_per_hand": n-1,
        "extra_pi_over_four_each_hand": True,
        "cells": cells, "coordinate_scale": P,
        "horizontal_interval": ["-1167049/1000000", "1167049/1000000"],
        "rational_pi4_support_scaled": int(F),
        "slice_lower_sum_scaled": total, "cell_width_scaled": int(dx),
        "area_rational_lower": str(area),
        "area_decimal_lower": float(area),
        "strict_margin_over_33_20": str(area-threshold),
        "strictly_above_33_20": bool(area>threshold),
        "midline_connectivity_certified": True,
        "elapsed_seconds": time.perf_counter()-t0,
        "global_A_F_upper_bound_proved": False,
        "CI_or_Lean_invoked": False,
    }


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv)>1 else 32
    cells = int(sys.argv[2]) if len(sys.argv)>2 else 100000
    print(json.dumps(certified_witness(n,cells), indent=2))
