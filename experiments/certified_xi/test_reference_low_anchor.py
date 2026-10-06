"""Regression checks for the low-anchor frozen-reference sign failure."""
from __future__ import annotations

from fractions import Fraction
import unittest

from flint import ctx

from common_remainder import anchored_moments
from continuous_theta import curvature as true_theta_curvature
from reference_low_anchor import certify_anchor, frozen_moments


class FrozenReferenceLowAnchorTests(unittest.TestCase):
    def test_opposite_signs_at_anchor_one(self):
        reference = certify_anchor(1)
        theta = true_theta_curvature(1)
        self.assertEqual(reference['status'], 'positive_reference_curvature')
        self.assertGreater(Fraction(reference['log_deficit_second']['lo']), 0)
        self.assertLess(Fraction(theta['log_epsilon_second']['hi']), 0)

    def test_formula_matches_existing_high_anchor_evaluator(self):
        with ctx.workprec(384):
            new = frozen_moments(10**6, 0)
            existing = anchored_moments('1000000', 0)
            for left, right in zip(new, existing):
                self.assertTrue(left.overlaps(right))

    def test_invalid_domain_rejected(self):
        for anchor, offset in ((0, 0), (1, 2), (1.5, 0)):
            with self.assertRaises(ValueError):
                frozen_moments(anchor, offset)


if __name__ == '__main__':
    unittest.main()
