"""Replays and diagnostics for the canonical-wing package; not certification.

The imported sources are unchanged. Exact mode replays GH algebra and checks
the pointwise winding-accounting identity. Optional polygon diagnostics do not
prove continuum feasibility, connectivity, winding stability, or optimality.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import platform
import sys

HERE = Path(__file__).resolve().parent


def load_checker():
    path = HERE.parent / 'check_two_wing_general_height.py'
    spec = importlib.util.spec_from_file_location('imported_gh_checker', path)
    if spec is None or spec.loader is None:
        raise RuntimeError('Unable to load imported GH checker')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.run()


def accounting_checks() -> dict:
    count = 0
    for s, r, d, winding in itertools.product((0, 1), (0, 1), (0, 1), range(-3, 4)):
        union = int(bool(r or d))
        outside = s * (1-union)
        wp, wn = max(winding, 0), max(-winding, 0)
        uncovered = outside * int(winding <= 0)
        deductions = (union*(1-s) + r*d + (1-outside)*wp
                      + outside*max(wp-1, 0))
        if s-r-d-winding != wn+uncovered-deductions:
            raise AssertionError('Winding-accounting identity failed')
        count += 1
    # Re-evaluate the identity after removing each proposed correction term.
    # These are pointwise controls, not feasible-sofa examples.
    for s, r, d, winding, omit in ((1, 0, 0, 0, 'uncovered'),
                                   (0, 0, 0, -1, 'negative')):
        union = int(bool(r or d))
        outside = s*(1-union)
        wp, wn = max(winding, 0), max(-winding, 0)
        uncovered = outside*int(winding <= 0)
        deductions = (union*(1-s) + r*d + (1-outside)*wp
                      + outside*max(wp-1, 0))
        mutated = wn+uncovered-deductions
        mutated -= uncovered if omit == 'uncovered' else wn
        if s-r-d-winding == mutated:
            raise AssertionError('Omitted correction was not detected')
    return {
        'pointwise_cases': count,
        'winding_range': [-3, 3],
        'arithmetic': 'Python integers',
        'omitted_uncovered_term_control': {'S': 1, 'R': 0, 'D': 0, 'w': 0},
        'omitted_negative_winding_control': {'S': 0, 'R': 0, 'D': 0, 'w': -1},
        'scope': 'Finite regressions of an elementary identity, not geometric coverage',
    }


def numerical_diagnostics() -> dict:
    sys.path.insert(0, str(HERE / 'diagnostics'))
    import numpy as np
    import shapely
    from shapely import affinity
    import wings as W
    import precise as P
    import junction_test as J
    import loops as LP
    results = []
    for nv, nx, nt, nth, ncore in ((800, 1000, 2000, 721, 2001),
                                  (1600, 2000, 4000, 1441, 4001)):
        for kind in ('candidate', 'compressed_0.90', 'junction_shave_0.08'):
            original = W.candidate_hull(nv)
            if kind == 'compressed_0.90':
                original = affinity.scale(original, xfact=0.90, yfact=1, origin=(0, 0))
            elif kind == 'junction_shave_0.08':
                original = J.shaved(0.08, nv=nv)
            xs = np.linspace(original.bounds[0], original.bounds[2], nx+2)[1:-1]
            hull = original if kind == 'candidate' else P.saturate(original, xs, nt=nt)
            data = P.full_analysis(hull, nx=nx, nt=nt, nth=nth, verbose=False)
            gamma, _ = W.gamma_polygon(W.verts(data['Rpoly']), W.verts(data['Dpoly']), nt=ncore)
            core = float(W.signed_area_cw(gamma))
            functional = float(data['R'] + data['D'] + core)
            faces = LP.faces_with_winding(gamma)
            signed = float(sum(int(w)*area for w, area, _ in faces))
            negative = float(sum(max(-int(w), 0)*area for w, area, _ in faces))
            discrepancy = abs(signed-core)
            if discrepancy > 1e-8:
                raise AssertionError('Polygonized winding and shoelace disagree')
            sample_x = np.linspace(hull.bounds[0], hull.bounds[2], nx+2)[1:-1]
            lo, hi = P.T_fibers(hull, sample_x, nt=nt)
            if not np.isfinite(lo).all() or not np.isfinite(hi).all():
                raise AssertionError('Nonfinite sampled fibers')
            results.append({
                'body': kind,
                'resolution': dict(hull_normals=nv, x_samples=nx, hallway_angles=nt,
                                   wing_angles_per_arc=nth, core_samples=ncore),
                'sampled_surviving_area': float(data['T']),
                'sampled_functional': functional,
                'area_minus_functional': float(data['T']-functional),
                'multiplicity_weighted_negative_winding': negative,
                'sampled_candidate_margin': float(W.M-functional),
                'minimum_sampled_fiber_length': float(np.min(hi-lo)),
                'winding_values_on_polygonized_faces': sorted(set(int(w) for w, _, _ in faces)),
                'winding_shoelace_discrepancy': discrepancy,
                'p_beta_central_difference': float(data['p_beta']),
            })
    return {
        'numpy_version': np.__version__, 'shapely_version': shapely.__version__,
        'results': results,
        'source_hashes': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted((HERE/'diagnostics').glob('*.py'))},
        'author_full_campaign_reproduced': False,
        'continuum_feasibility_verified': False,
        'continuum_connectivity_verified': False,
        'error_sign_certified': False,
        'warning': 'Floating-point geometry, finite angles, and spatial quadrature; no rigorous error bound',
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--diagnostics', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = {
        'status': 'review_checks_passed',
        'is_global_proof_certificate': False,
        'geometric_admission_verified_unrestricted': False,
        'unrestricted_optimality_proved': False,
        'python_version': platform.python_version(),
        'gh_exact_replay': load_checker(),
        'winding_accounting_checks': accounting_checks(),
        'diagnostics': numerical_diagnostics() if args.diagnostics else None,
        'review_source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'ci_or_lean_used': False,
    }
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
