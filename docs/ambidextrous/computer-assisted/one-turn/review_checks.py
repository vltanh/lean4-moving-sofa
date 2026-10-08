"""Review checks for the imported one-turn proposal, not a proof certificate.

The imported scripts remain unchanged. This module exposes cap_objectives(),
which keeps signed cap-minus-full-niche area distinct from surviving area.
It uses the uploaded cap implementation only for finite-angle roof evaluation.
The user-supplied numerical optimization claims are not reproduced by this run.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import itertools
import json
from pathlib import Path
import platform

import numpy as np
import cand
import polycap as original


def top_profile(vertices: np.ndarray, x: np.ndarray) -> np.ndarray:
    """Upper-chain interpolation, with exact duplicate abscissae consolidated.

    Assumes the input is the complete upper boundary of a convex cap, with
    optional bottom endpoints. This is not a convexity/feasibility verifier.
    """
    p = np.asarray(vertices, dtype=float)
    if p.ndim != 2 or p.shape[1] != 2 or p.shape[0] < 2 or not np.isfinite(p).all():
        raise ValueError('Expected finite planar upper-chain vertices')
    xs, inverse = np.unique(p[:, 0], return_inverse=True)
    if len(xs) < 2:
        raise ValueError('Positive horizontal extent is required')
    ys = np.full(len(xs), -np.inf)
    np.maximum.at(ys, inverse, p[:, 1])
    return np.interp(np.asarray(x, dtype=float), xs, ys)


def area_parts(x: np.ndarray, a: np.ndarray, alpha: np.ndarray) -> dict:
    x, a, alpha = [np.asarray(z, dtype=float) for z in (x, a, alpha)]
    if x.ndim != 1 or len(x) < 2 or a.shape != x.shape or alpha.shape != x.shape:
        raise ValueError('Expected three equal-length one-dimensional arrays')
    if not all(np.isfinite(z).all() for z in (x, a, alpha)) or not np.all(np.diff(x) > 0):
        raise ValueError('Finite values and increasing abscissae are required')
    if np.any(alpha < 0):
        raise ValueError('The niche roof must be nonnegative')
    width = float(x[-1] - x[0])
    signed = float(np.trapezoid(a - alpha, x))
    surviving = float(np.trapezoid(np.maximum(a - alpha, 0), x))
    leakage = float(np.trapezoid(np.maximum(alpha - a, 0), x))
    return {'width': width, 'signed_A': signed, 'surviving_area': surviving,
            'niche_outside_cap': leakage, 'signed_Psi': signed - width / 2,
            'clipped_Psi': surviving - width / 2,
            'decomposition_error': surviving - signed - leakage}


def cap_objectives(vertices: np.ndarray, nt: int = 800, nx: int = 2001) -> dict:
    """Diagnostic values for a supplied cap polygon; neither is a certificate."""
    if type(nt) is not int or type(nx) is not int or nt < 1 or nx < 2:
        raise ValueError('Positive angle count and at least two spatial points required')
    p = np.asarray(vertices, dtype=float)
    top_profile(p, np.array([0.0]))  # validate the array before reading its bounds
    x = np.linspace(p[:, 0].min(), p[:, 0].max(), nx)
    grid = original.Grid(nt, nx)
    _, alpha, _ = original.cap_fibers(p, grid, x)
    return area_parts(x, top_profile(p, x), alpha)


def exact_checks() -> dict:
    # OA.2, with both clipping and the empty-fiber correction retained.
    roof_values = [Q(i, 4) for i in range(5)]
    niche_values = [Q(i, 4) for i in range(9)]
    count = 0
    for a, b, al, be in itertools.product(roof_values, roof_values, niche_values, niche_values):
        raw = min(a, 1-be) - max(al, 1-b)
        clip = min(al, 1-b) + min(be, 1-a)
        assert max(raw, 0) == a+b-1-al-be+clip+max(-raw, 0)
        count += 1
    # The A/P/R classification on exact interval data satisfying OT3a's start tests.
    points = [Q(0), Q(1, 2), Q(1), Q(2), Q(5, 2), Q(3), Q(7, 2), Q(4)]
    intervals = [(l, r) for l in points for r in points if l <= r]
    accepted = 0
    for (lt, rt), (lb, rb) in itertools.product(intervals, repeat=2):
        if any(lt < z < 3 for z in (lb, rb)) or any(lb < z < 3 for z in (lt, rt)):
            continue
        A = lt == lb and lt < 3 and rt >= 3 and rb >= 3
        P = lt == lb and lt < 3 and (rt == lt or rb == lb)
        R = lt >= 3 or lb >= 3
        assert sum([A, P, R]) == 1
        accepted += 1
    # Exact positive leakage witness in the 4-by-1 rectangle at (c,s)=(3/5,4/5).
    left, right, apex_x = Q(5, 4), Q(7, 3), Q(41, 25)
    apex_y = (11-3*apex_x)/4
    assert apex_y == (-2+4*apex_x)/3 == Q(38, 25)
    leakage = (right-left)*(apex_y-1)/2
    assert leakage == Q(169, 600) > 0
    # Sign mutations must actually fail on witnesses.
    a, b, al, be = Q(1, 2), Q(1), Q(0), Q(1, 4)
    raw = min(a, 1-be)-max(al, 1-b)
    assert raw != a+b-1-al-be  # dropping clipping is false
    a, b, al, be = Q(1), Q(1), Q(2), Q(2)
    raw = min(a, 1-be)-max(al, 1-b)
    assert max(raw, 0) != raw  # dropping empty-fiber correction is false
    return {'rational_fiber_cases': count, 'interval_pairs_examined': len(intervals)**2,
            'interval_pairs_meeting_start_tests': accepted,
            'exact_rectangle_leakage_lower_bound': str(leakage),
            'incorrect_sign_formulas_rejected': ['omit clipping', 'omit empty-fiber correction'],
            'scope': 'Finite checks of displayed identities, not continuum verification'}


def run() -> dict:
    exact = exact_checks()
    rectangle = np.array([[4., 0.], [4., 1.], [0., 1.], [0., 0.]])
    endpoints = np.array([0., 4.])
    old_top = original.top_profile_from_vertices(rectangle, endpoints)
    new_top = top_profile(rectangle, endpoints)
    assert np.array_equal(old_top, [1., 0.])
    assert np.array_equal(new_top, [1., 1.])
    rect = cap_objectives(rectangle)
    assert rect['niche_outside_cap'] > float(Q(169, 600))
    assert abs(rect['decomposition_error']) < 1e-10
    rows = []
    for nt in (200, 400, 800):
        data = cand.cap_data(cand.h_star_upper, nt=nt, nx=2001)
        x, a, al = data['x'], data['a'], data['alpha']
        parts = area_parts(x, a, al)
        raw = np.minimum(a, 1-al)-np.maximum(al, 1-a)
        area = float(np.trapezoid(np.maximum(raw, 0), x))
        clipping = float(2*np.trapezoid(np.minimum(al, 1-a), x))
        empty = float(np.trapezoid(np.maximum(-raw, 0), x))
        err = area-(2*parts['signed_Psi']+clipping+empty)
        assert abs(err) < 1e-10
        rows.append({'hallway_angles': nt, 'spatial_points': 2001,
                     'twice_signed_Psi': 2*parts['signed_Psi'], 'pair_area': area,
                     'clipping': clipping, 'empty_fiber_correction': empty,
                     'identity_error': err, 'candidate_M': float(cand.M)})
    root = Path(__file__).resolve().parent
    names = ['cand.py', 'polycap.py', 'review_checks.py']
    return {'status': 'review_checks_passed', 'is_proof_certificate': False,
            'global_optimality_proved': False, 'author_optimization_runs_reproduced': False,
            'exact_checks': exact,
            'endpoint_regression': {'imported': old_top.tolist(), 'corrected': new_top.tolist()},
            'rectangle_diagnostic': rect, 'candidate_diagnostics': rows,
            'source_sha256': {n: hashlib.sha256((root/n).read_bytes()).hexdigest() for n in names},
            'python_version': platform.python_version(), 'numpy_version': np.__version__,
            'ci_or_lean_used': False,
            'warning': 'Floating-point quadrature has no certified error sign or global coverage'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = json.dumps(run(), indent=2) + '\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')
