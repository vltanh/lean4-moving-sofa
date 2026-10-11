"""Oblique support-line algebra; NOT an arbitrary-angle sofa area bound."""
from __future__ import annotations

import argparse
import json
import math
import numpy as np
from geometry import validate_beta


def fourier_multiplier(beta: float, modes):
    validate_beta(beta)
    k = np.asarray(modes, dtype=float)
    return (np.exp(1j*k*beta)-math.cos(beta))/math.sin(beta)-1j*k


def outer_corner(t, beta: float, h, h_shift):
    validate_beta(beta)
    t = np.asarray(t, dtype=float)
    u = np.stack((np.cos(t), np.sin(t)), axis=-1)
    v = np.stack((-np.sin(t), np.cos(t)), axis=-1)
    a = (np.asarray(h_shift)-math.cos(beta)*np.asarray(h))/math.sin(beta)
    return np.asarray(h)[..., None]*u+a[..., None]*v


def tangent_displacement(beta: float, h, h_shift, derivative):
    validate_beta(beta)
    return (np.asarray(h_shift)-math.cos(beta)*np.asarray(h))/math.sin(beta)-np.asarray(derivative)


def spectrum(max_mode: int = 32):
    if max_mode < 2:
        raise ValueError("max_mode must be at least 2")
    modes = np.array([0]+list(range(2, max_mode+1)))
    result = []
    for degrees in [5, 15, 30, 60, 90, 120, 150, 175]:
        beta = math.radians(degrees)
        values = np.abs(fourier_multiplier(beta, modes))
        j = int(np.argmin(values))
        result.append({"bend_degrees": degrees, "cutoff": max_mode,
                       "min_nontranslation_multiplier": float(values[j]),
                       "minimizing_mode": int(modes[j]),
                       "max_translation_residual": float(np.abs(fourier_multiplier(beta, [-1, 1])).max())})
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-mode", type=int, default=32)
    args = parser.parse_args()
    print(json.dumps({"scope": "full-circle Fourier test only", "spectrum": spectrum(args.max_mode)}, indent=2))
