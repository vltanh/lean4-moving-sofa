"""Cap-only Mamikon coercivity diagnostics; floating point, not certification.

The two fixed difference supports are f(pi/2)=f(pi)=0. This aligns the left
support of two caps and removes horizontal translation. Auxiliary B,D variables
are absent, not regularized. No Gerver constants or reference shape are loaded.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import cho_factor, cho_solve

from q_experiment import PI, QProblem, unit


def analytic_constant(phi: float) -> float:
    """Constant in ||f||_infinity <= C(phi) sqrt(E), E=1/2 sum ||r_j||_2^2.

The elementary proof in CAP_STABILITY.md uses 0.039 <= phi <= 0.04.
"""
    if not 0.039 <= phi <= 0.04:
        raise ValueError('the stated analytic estimate uses phi in [0.039, 0.04]')
    length = PI / 2 - 2 * phi
    sec = 1 / np.cos(phi)
    coefficients = np.array([
        np.sqrt(np.tan(phi)), sec * np.sqrt(length),
        sec * np.sqrt(np.tan(phi)),
        sec * (length / np.sqrt(2) + np.tan(phi) * np.sqrt(np.sin(phi)*np.cos(phi)))])
    return float(np.sqrt(2 * coefficients @ coefficients))


def cap_energy_matrix(p: QProblem, quadrature: int = 64) -> np.ndarray:
    """Only the first four (K) squares from diagnostics.square_matrix."""
    if quadrature < 2:
        raise ValueError('quadrature must be at least two')
    nk = 2 * p.m + 1
    matrix = np.zeros((nk, nk))
    nodes, weights = leggauss(quadrature)
    terms = [(0, p.phi, PI/2), (p.phi, PI/2-p.phi, None),
             (PI/2-p.phi, PI/2, PI-p.phi), (PI/2, PI, PI)]
    for start, end, target in terms:
        for i in range(p.index(start), p.index(end)):
            a, b = p.angles[i:i+2]
            rows = []
            for t, w in zip((a+b)/2 + (b-a)*nodes/2, weights*(b-a)/2):
                hp = p.support_row(0, t, True)[:nk]
                if target is None:
                    rho = p.support_row(0, t+PI/2)[:nk] - hp
                else:
                    rho = ((p.support_row(0, target)[:nk]
                            - np.cos(target-t)*p.support_row(0, t)[:nk])
                           / np.sin(target-t) - hp)
                rows.append(np.sqrt(w/2) * rho)
            rows = np.stack(rows)
            matrix += rows.T @ rows
    return (matrix + matrix.T) / 2


def free_cap_indices(p: QProblem) -> np.ndarray:
    return np.array([i for i in range(2*p.m+1) if i not in (p.m, 2*p.m)])


def align_difference(p: QProblem, difference: np.ndarray) -> np.ndarray:
    """Remove s cos(t) with s=-difference(pi), leaving f(pi)=0."""
    nk = 2*p.m + 1
    d = np.asarray(difference, dtype=float)
    if d.shape != (nk,) or not np.all(np.isfinite(d)):
        raise ValueError('expected finite cap-support difference of length 2*m+1')
    if abs(d[p.m]) > 1e-8:
        raise ValueError('caps must have identical top support')
    return d + d[-1] * np.cos(p.angles[:nk])


def cap_sup_norm(p: QProblem, difference: np.ndarray) -> float:
    """Continuous angular supremum, not just a maximum on fan normals."""
    nk = 2*p.m + 1
    d = np.asarray(difference, dtype=float)
    if d.shape != (nk,):
        raise ValueError('incorrect cap-support vector length')
    best = 0.
    for i in range(2*p.m):
        a, b = p.angles[i:i+2]
        vertex = p.vertices[0, i, :, :nk] @ d
        candidates = [a, b]
        angle = float(np.arctan2(vertex[1], vertex[0]) % (2*PI))
        for t in (angle, (angle+PI) % (2*PI)):
            if a <= t <= b:
                candidates.append(t)
        best = max(best, *(abs(float(unit(t) @ vertex)) for t in candidates))
    return best


def coercivity(p: QProblem, quadrature: int = 64) -> dict:
    """Best ambient polygonal constant, via inversion of the cap-only energy.

For each angular cell, the squared evaluation norm is a 2x2 quadratic
form u(t)^T W u(t). Endpoints and eigenvector directions give its exact
maximum in exact arithmetic; the implementation uses floating-point algebra.
"""
    energy = cap_energy_matrix(p, quadrature)
    free = free_cap_indices(p)
    reduced = energy[np.ix_(free, free)]
    values = np.linalg.eigvalsh(reduced)
    factor = cho_factor(reduced)
    best, angle, witness_row = -np.inf, None, None
    for i in range(2*p.m):
        a, b = p.angles[i:i+2]
        v = p.vertices[0, i, :, :2*p.m+1][:, free]
        covariance = v @ cho_solve(factor, v.T)
        _, vectors = np.linalg.eigh(covariance)
        candidates = [a, b]
        for eigenvector in vectors.T:
            t = float(np.arctan2(eigenvector[1], eigenvector[0]) % PI)
            if a <= t <= b:
                candidates.append(t)
        for t in candidates:
            row = unit(t) @ v
            evaluation = float(row @ cho_solve(factor, row))
            if evaluation > best:
                best, angle, witness_row = evaluation, t, row
    witness = np.zeros(2*p.m+1)
    witness[free] = cho_solve(factor, witness_row) / np.sqrt(best)
    constant = float(np.sqrt(best))
    return {'intervals': p.intervals, 'phi': p.phi,
            'cap_free_variables': len(free), 'quadrature': quadrature,
            'energy_min_eigenvalue': float(values[0]),
            'energy_max_eigenvalue': float(values[-1]),
            'cap_sup_constant': constant, 'worst_angle': angle,
            'analytic_constant': analytic_constant(p.phi),
            'witness_energy': float(witness @ energy @ witness),
            'witness_sup_norm': cap_sup_norm(p, witness),
            'arithmetic_certified': False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--intervals', type=int, nargs='+', default=[4, 8, 16, 32, 64])
    parser.add_argument('--phi', type=float, default=.04)
    parser.add_argument('--quadrature', type=int, default=64)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rows = []
    for n in args.intervals:
        row = coercivity(QProblem(n, args.phi), args.quadrature)
        rows.append(row)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({'runs': rows}, indent=2)+'\n')
        print(json.dumps(row), flush=True)


if __name__ == '__main__':
    main()
