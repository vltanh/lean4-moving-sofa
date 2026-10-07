#!/usr/bin/env python3
"""Numerical algebra regression for the balanced hallway-wall expansion.

Does not execute Lean, Lake, CI or a generated finite certificate. The test
checks only an exact identity in the first-variation algebra; it is not a
verification of Gerver-specific quadratic support Taylor bounds.
"""
from __future__ import annotations

import math
import unittest


def dot(u: tuple[float, float], v: tuple[float, float]) -> float:
    return u[0] * v[0] + u[1] * v[1]


def uv(t: float) -> tuple[float, float]:
    return math.cos(t), math.sin(t)


def vv(t: float) -> tuple[float, float]:
    return -math.sin(t), math.cos(t)


def sub(u: tuple[float, float], v: tuple[float, float]) -> tuple[float, float]:
    return u[0] - v[0], u[1] - v[1]


def add(u: tuple[float, float], v: tuple[float, float]) -> tuple[float, float]:
    return u[0] + v[0], u[1] + v[1]


def smul(a: float, u: tuple[float, float]) -> tuple[float, float]:
    return a * u[0], a * u[1]


def slack_u(point: tuple[float, float], t: float, support: float) -> float:
    return dot(point, uv(t)) - support + 1


def slack_v(point: tuple[float, float], t: float, support: float) -> float:
    return dot(point, vv(t)) - support + 1


def expansion(q: tuple[float, float], w: tuple[float, float],
              t: float, lam: float, d: float, a: float, b: float,
              hs_u: float, hs_v: float) -> tuple[float, float, float, float]:
    """Supports at t are chosen so both slacks of q vanish there.

    The supports at s=t+lam*d are independent input scalars. The identities
    must hold irrespective of the convexity of the supporting cap.
    """
    s = t + lam * d
    ht_u = dot(q, uv(t)) + 1
    ht_v = dot(q, vv(t)) + 1
    p = add(q, smul(d, w))
    lhs_u = slack_u(p, s, hs_u)
    lhs_v = slack_v(p, s, hs_v)
    fu = dot(w, uv(t)) + a * lam
    fv = dot(w, vv(t)) - b * lam
    err_u = (slack_u(q, s, hs_u) - slack_u(q, t, ht_u)
             - a * (s - t) + d * dot(w, sub(uv(s), uv(t))))
    err_v = (slack_v(q, s, hs_v) - slack_v(q, t, ht_v)
             + b * (s - t) + d * dot(w, sub(vv(s), vv(t))))
    return lhs_u, lhs_v, d * fu + err_u, d * fv + err_v


class BalancedWallExpansionTest(unittest.TestCase):
    def test_corrected_exact_identity(self) -> None:
        cases = 0
        for t in (0.04, 0.35, 0.68, 1.2):
            for d in (0.0, 1e-8, 1e-4, 0.03):
                for lam in (-3.5, -0.6, 0.0, 2.2):
                    q = (0.37, 0.81)
                    w = (-0.6, 0.8)
                    a, b = 0.45, 1.1
                    lhsu, lhsv, rhsu, rhsv = expansion(
                        q, w, t, lam, d, a, b, 1.2, 0.3)
                    self.assertAlmostEqual(lhsu, rhsu, delta=2e-13)
                    self.assertAlmostEqual(lhsv, rhsv, delta=2e-13)
                    cases += 1
        self.assertEqual(cases, 64)

    def test_old_direction_free_error_is_not_exact(self) -> None:
        q, w, t, d, lam = (0.37, 0.81), (-0.6, 0.8), 0.68, 0.03, 2.2
        a, b = 0.45, 1.1
        s = t + lam * d
        old_u = (slack_u(q, s, 1.2) - slack_u(q, t, dot(q, uv(t)) + 1)
                 + (s - t) * math.sin(t))
        old_v = (slack_v(q, s, 0.3) - slack_v(q, t, dot(q, vv(t)) + 1)
                 + (s - t) * math.cos(t))
        p = add(q, smul(d, w))
        err_u = abs(slack_u(p, s, 1.2) -
                    (d * (dot(w, uv(t)) + a * lam) + old_u))
        err_v = abs(slack_v(p, s, 0.3) -
                    (d * (dot(w, vv(t)) - b * lam) + old_v))
        self.assertGreater(err_u, 1e-3)
        self.assertGreater(err_v, 1e-3)


if __name__ == "__main__":
    unittest.main()
