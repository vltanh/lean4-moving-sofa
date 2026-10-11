"""Local checks for the improved continuous-motion enclosure."""
import json
import math
from pathlib import Path
import unittest

import numpy as np
from shapely.geometry import Polygon

from geometry import Motion, clip_halfplane, sampled_intersection, stationary_area
from enclosure import enclose
from search import seed_path
from swept import clip_fast, enclose_swept, offset_convex_intersection


class SweptTests(unittest.TestCase):
    def test_vectorized_clip_matches_scalar(self):
        t = np.linspace(0, 2*math.pi, 100, endpoint=False)
        cap = np.column_stack((2*np.cos(t), np.sin(t)))
        rng = np.random.default_rng(11)
        for _ in range(40):
            n = rng.normal(size=2)
            rhs = rng.uniform(-.8, .8)
            a, b = clip_halfplane(cap, n, rhs), clip_fast(cap, n, rhs)
            np.testing.assert_allclose(a, b, atol=2e-14)

    def test_mitered_offset_contains_disk_dilation(self):
        hull = Polygon([[0, 0], [2, 0], [0, 1]])
        cap = np.array([[-3.,-3.], [5.,-3.], [5.,4.], [-3.,4.]])
        outer = offset_convex_intersection(cap, hull, .3)
        # GEOS's inscribed circular approximation is used only as a TEST set,
        # not as the outer enclosure algorithm.
        self.assertLess(hull.buffer(.3, quad_segs=128).difference(outer).area, 1e-12)
        self.assertGreater(outer.area, hull.buffer(.3, quad_segs=128).area)

    def test_containment_both_directions(self):
        for beta, mode in [(1., "forward"), (2.6, "reverse")]:
            motion = seed_path(beta, mode, 5, .5, .2)
            result, inner = enclose_swept(motion, 16, audit=True)
            self.assertTrue(inner.is_valid)
            self.assertGreater(result["inner_area"], 0)
            self.assertLessEqual(result["inner_area"], result["sampled_area"]+1e-12)
            self.assertLess(result["audit_outside_area"], 1e-12)
            self.assertLess(inner.difference(sampled_intersection(motion, 64)).area, 1e-12)

    def test_stationary_inner_below_exact_area(self):
        for degrees in [30, 90, 150]:
            beta = math.radians(degrees)
            motion = Motion(beta, "forward", np.zeros((3, 2)))
            result, _ = enclose_swept(motion, 32)
            self.assertLessEqual(result["inner_area"], stationary_area(beta)+1e-12)
            self.assertGreater(result["inner_area"], stationary_area(beta)-.1)

    def test_improved_margin_retains_more_area_on_saved_path(self):
        data = json.loads((Path(__file__).parent/"results/coarse-grid-counterexample.json").read_text())
        motion = Motion(math.pi/2, "forward", data["corners"])
        first, _ = enclose(motion, 16)
        improved, _ = enclose_swept(motion, 16, audit=True)
        self.assertGreater(improved["inner_area"], first["inner_area"]+.1)
        self.assertLess(improved["audit_outside_area"], 1e-12)

    def test_empty_candidate(self):
        corners = np.zeros((3, 2)); corners[1, 1] = 3
        result, inner = enclose_swept(Motion(math.pi/2, "forward", corners), 16, audit=True)
        self.assertEqual(result["inner_area"], 0)
        self.assertTrue(inner.is_empty)
        self.assertEqual(result["audit_outside_area"], 0)


if __name__ == "__main__":
    unittest.main()
