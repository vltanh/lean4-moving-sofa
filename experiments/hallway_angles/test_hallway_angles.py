"""Local regression tests. Not a Lean build or a CI workflow."""
import json
import math
from pathlib import Path
import unittest

import numpy as np
from shapely.affinity import translate
from shapely.geometry import MultiPolygon, box

from geometry import (Motion, clearance, clip_halfplane, largest_component,
                      normals, sampled_intersection, stationary_area,
                      translation_area, validate_beta)
from enclosure import enclose
from rigidity import fourier_multiplier, outer_corner, tangent_displacement
from search import optimize, seed_path


class GeometryTests(unittest.TestCase):
    def test_invalid_angles(self):
        for beta in [0, -1, math.pi, math.inf, math.nan]:
            with self.subTest(beta=beta), self.assertRaises(ValueError):
                validate_beta(beta)

    def test_unit_normals_and_separation(self):
        for beta in [.2, .7, math.pi/2, 2.8]:
            ns = normals(beta, np.linspace(-3, 3, 23))
            np.testing.assert_allclose(np.linalg.norm(ns, axis=-1), 1, atol=1e-14)
            np.testing.assert_allclose(np.sum(ns[:, 0]*ns[:, 1], axis=-1), math.cos(beta), atol=1e-14)

    def test_right_angle_hallway(self):
        p = np.random.default_rng(2).uniform(-3, 3, (200, 2))
        expected = (p[:, 0] <= 1) & (p[:, 1] <= 1) & ((p[:, 0] >= 0) | (p[:, 1] >= 0))
        np.testing.assert_array_equal(clearance(p, math.pi/2, 0, np.zeros(2)) >= 0, expected)

    def test_halfplane_area(self):
        v = np.array([[0, 0], [1, 0], [1, 1], [0, 1]], dtype=float)
        from shapely.geometry import Polygon
        self.assertAlmostEqual(Polygon(clip_halfplane(v, np.ones(2), 1)).area, .5)
        self.assertEqual(len(clip_halfplane(v, np.ones(2), -1)), 0)

    def test_invalid_motion(self):
        for c in [np.zeros((2, 2)), np.zeros((4, 2)), np.zeros((3, 3)), np.full((3, 2), math.nan)]:
            with self.assertRaises(ValueError):
                Motion(1, "forward", c)
        with self.assertRaises(ValueError):
            Motion(1, "unknown", np.zeros((3, 2)))
        with self.assertRaises(ValueError):
            Motion(1, "reverse", np.zeros((3, 2)))

    def test_motion_owns_immutable_copy(self):
        c = np.zeros((3, 2))
        m = Motion(1, "forward", c)
        c[1, 0] = 12
        self.assertEqual(m.corners[1, 0], 0)
        self.assertFalse(m.corners.flags.writeable)

    def test_sampling_includes_knots(self):
        m = seed_path(1, "reverse", 9, .5, .1)
        t, c = m.sample(3)
        np.testing.assert_allclose(c[::3], m.corners)
        self.assertAlmostEqual(t[-1], 1-math.pi)
        for n in [0, -1, 2.5, True]:
            with self.assertRaises(ValueError):
                m.sample(n)

    def test_stationary_baseline(self):
        for degrees in [30, 60, 90, 120, 150]:
            beta = math.radians(degrees)
            m = Motion(beta, "forward", np.zeros((3, 2)))
            area = sampled_intersection(m, 128).area
            expected = stationary_area(beta)
            self.assertGreaterEqual(area+1e-10, expected)
            self.assertLess(area-expected, .0001)

    def test_translation_parallelogram_and_legs(self):
        for beta in [.4, 1.0, math.pi/2, 2.7]:
            ns = normals(beta, 0)
            coords = np.array([[0, 0], [1, 0], [1, 1], [0, 1]])
            p = np.linalg.solve(ns, coords.T).T
            from shapely.geometry import Polygon
            self.assertAlmostEqual(Polygon(p).area, translation_area(beta), places=12)
            for a in [0, 1, 10]:
                incoming = p-np.array([a, 0])
                outgoing = p+a*np.array([math.cos(beta), -math.sin(beta)])
                self.assertGreaterEqual(clearance(incoming, beta, 0, np.zeros(2)).min(), -1e-13)
                self.assertGreaterEqual(clearance(outgoing, beta, 0, np.zeros(2)).min(), -1e-13)

    def test_nested_outer_approximations(self):
        for mode in ["forward", "reverse"]:
            m = seed_path(2.2, mode, 5, .4, .3)
            coarse = sampled_intersection(m, 2)
            fine = sampled_intersection(m, 8)
            self.assertLess(fine.difference(coarse).area, 1e-10)

    def test_horizontal_translation_invariance(self):
        for mode in ["forward", "reverse"]:
            m = seed_path(2.2, mode, 5, .4, .3)
            shifted = Motion(m.beta, mode, m.corners+np.array([7.0, 0.0]))
            a, b = sampled_intersection(m, 4), sampled_intersection(shifted, 4)
            self.assertLess(translate(a, xoff=7).symmetric_difference(b).area, 1e-10)

    def test_bounding_rectangle_does_not_truncate(self):
        for degrees in [30, 90, 150]:
            for mode in ["forward", "reverse"]:
                m = seed_path(math.radians(degrees), mode, 5, .5, .1)
                s = sampled_intersection(m, 8)
                if not s.is_empty:
                    r = m.bounding_rectangle()
                    self.assertGreater(s.bounds[0], r[0, 0]+.5)
                    self.assertLess(s.bounds[2], r[1, 0]-.5)

    def test_largest_component_not_sum(self):
        p = MultiPolygon([box(0, 0, 1, 1), box(2, 0, 4, 1)])
        self.assertEqual(largest_component(p).area, 2.0)
        self.assertEqual(p.area, 3.0)

    def test_negative_margin_rejected(self):
        m = Motion(1, "forward", np.zeros((3, 2)))
        for margin in [-1, math.nan]:
            with self.assertRaises(ValueError):
                sampled_intersection(m, 2, margin)

    def test_continuous_margin_audit(self):
        for beta, mode in [(1.0, "forward"), (2.6, "reverse")]:
            m = seed_path(beta, mode, 5, .5, .2)
            r, inner = enclose(m, 32, audit=True)
            self.assertGreater(r["inner_area"], 0)
            self.assertLessEqual(r["inner_area"], r["sampled_area"]+1e-10)
            self.assertLess(r["audit_outside_area"], 1e-10)
            self.assertTrue(inner.is_valid)


class RigidityTests(unittest.TestCase):
    def test_oblique_support_corner(self):
        t = np.linspace(0, 6, 100)
        for beta in [.3, math.pi/2, 2.7]:
            h, hs = 2+.1*np.cos(2*t), 2+.1*np.cos(2*(t+beta))
            y = outer_corner(t, beta, h, hs)
            np.testing.assert_allclose((y*np.column_stack([np.cos(t), np.sin(t)])).sum(axis=1), h, atol=1e-13)
            np.testing.assert_allclose((y*np.column_stack([np.cos(t+beta), np.sin(t+beta)])).sum(axis=1), hs, atol=1e-13)

    def test_corner_offset_widths(self):
        for beta in [.3, 1, 2.7]:
            d = np.array([1, math.tan(beta/2)])
            self.assertAlmostEqual(d @ np.array([math.cos(beta), math.sin(beta)]), 1)
            self.assertAlmostEqual(np.linalg.norm(d), 1/math.cos(beta/2))

    def test_fourier_kernel(self):
        for beta in [.1, .6, math.pi/2, 2.7, 3.0]:
            np.testing.assert_allclose(fourier_multiplier(beta, [-1, 1]), 0, atol=1e-13)
            k = [0]+list(range(2, 40))
            self.assertGreater(np.abs(fourier_multiplier(beta, k)).min(), 1e-5)

    def test_square_gap(self):
        t = np.linspace(0, 2*math.pi, 4096, endpoint=False)
        for beta in [.4, 1.2, 2.7]:
            a = tangent_displacement(beta, 2+.1*np.cos(2*t), 2+.1*np.cos(2*(t+beta)), -.2*np.sin(2*t))
            b = tangent_displacement(beta, 2+.15*np.sin(3*t), 2+.15*np.sin(3*(t+beta)), .45*np.cos(3*t))
            lam = .37
            gap = np.mean((1-lam)*a*a+lam*b*b-((1-lam)*a+lam*b)**2)
            self.assertAlmostEqual(gap, lam*(1-lam)*np.mean((a-b)**2), places=12)


class NegativeResultTests(unittest.TestCase):
    def test_affine_conjugation_is_not_rigid(self):
        a = np.array([[1, 1], [0, 1]])
        r = np.array([[0, -1], [1, 0]])
        q = a @ r @ np.linalg.inv(a)
        np.testing.assert_allclose(q, [[1, -2], [1, -1]])
        self.assertFalse(np.allclose(q.T @ q, np.eye(2)))

    def test_endpoint_only_collision_check_fails(self):
        p = np.array([[1., 1.]])
        for t in [0, math.pi/2]:
            self.assertGreaterEqual(clearance(p, math.pi/2, t, np.zeros(2))[0], -1e-14)
        self.assertLess(clearance(p, math.pi/2, math.pi/4, np.zeros(2))[0], -.4)

    def test_direct_objective_not_concave(self):
        areas = []
        for y in [0, 1.5, 3]:
            c = np.zeros((3, 2)); c[1, 1] = y
            areas.append(largest_component(sampled_intersection(Motion(math.pi/2, "forward", c), 32)).area)
        self.assertGreater(areas[0], 1.57)
        self.assertEqual(areas[2], 0)
        self.assertLess(areas[1], (areas[0]+areas[2])/2)
        self.assertLess(areas[1], .125)

    def test_recorded_sampling_counterexample(self):
        data = json.loads((Path(__file__).parent/"results/coarse-grid-counterexample.json").read_text())
        m = Motion(math.pi/2, "forward", data["corners"])
        coarse = largest_component(sampled_intersection(m, 4)).area
        fine = largest_component(sampled_intersection(m, 32)).area
        self.assertAlmostEqual(coarse, data["observations"][0]["sampled_area"], places=8)
        self.assertAlmostEqual(fine, data["observations"][1]["sampled_area"], places=8)
        self.assertGreater(coarse, 2.23)
        self.assertLess(fine, 2.2195)

    def test_optimization_budget_status_is_preserved(self):
        _, r = optimize(math.pi/2, "forward", knots=3, subdivisions=1,
                        restarts=1, maxiter=1, seed=1)
        self.assertEqual(len(r["runs"]), 1)
        self.assertIn("success", r["runs"][0])
        self.assertIn("message", r["runs"][0])
        self.assertGreater(r["evaluations"], 0)


if __name__ == "__main__":
    unittest.main()
