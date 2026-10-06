"""Replay physical cross-support overlap and its strip-profile bound."""
import json
from fractions import Fraction
import math
from pathlib import Path
import unittest

from flint import arb, ctx

from cross_support_physical_overlap import cross_gram, run


RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


class CrossSupportPhysicalOverlapTests(unittest.TestCase):
    def test_cross_gram_matches_independent_quadrature(self):
        small, large = math.log(17), math.log(19)
        panels = 10_000
        step = small / panels

        def basis(index: int, length: float, t: float) -> float:
            return (1 / math.sqrt(length) if index == 0 else
                    math.sqrt(2 / length) * math.cos(
                        2 * math.pi * index * (t + length / 2) / length))

        with ctx.workprec(256):
            for i in range(4):
                for j in range(4):
                    with self.subTest(i=i, j=j):
                        direct = 0.0
                        for k in range(panels + 1):
                            t = -small / 2 + step * k
                            weight = 1 if k in (0, panels) else (4 if k % 2 else 2)
                            direct += weight * basis(i, small, t) * basis(j, large, t)
                        direct *= step / 3
                        analytic = cross_gram(i, j, arb(17).log(), arb(19).log())
                        self.assertAlmostEqual(float(analytic.mid()), direct, delta=1e-10)
            for i in range(4):
                for j in range(4):
                    equal = cross_gram(i, j, arb(17).log(), arb(17).log())
                    self.assertTrue(equal.contains(1 if i == j else 0))

    def test_saved_certificates_replay_and_bound_profile_step(self):
        previous_physical_lower = Fraction(0)
        previous_coordinate_upper = Fraction(1)
        for modes in (8, 12, 16):
            with self.subTest(modes=modes):
                result = run(RESEARCH / f'isolated_kernel_17_{modes}.json',
                             RESEARCH / f'isolated_kernel_19_{modes}.json')
                saved = json.loads((RESEARCH / f'physical_overlap_17_19_{modes}.json').read_text())
                self.assertEqual(result, saved)
                physical = result['physical_l2_overlap']
                coordinate = result['coefficient_coordinate_overlap']
                self.assertGreater(Fraction(physical['lo']), previous_physical_lower)
                self.assertLess(Fraction(coordinate['hi']), previous_coordinate_upper)
                previous_physical_lower = Fraction(physical['hi'])
                previous_coordinate_upper = Fraction(coordinate['lo'])
                support = json.loads((RESEARCH / f'support_schur_17_19_{modes}.json').read_text())
                change = support['profile_change']['real_4']['direct_profile_change']
                magnitude = max(abs(Fraction(change['lo'])), abs(Fraction(change['hi'])))
                coupled = Fraction(result['coupled_uniform_strip_profile_difference_upper'])
                self.assertLess(magnitude, coupled)
                self.assertLess(coupled,
                                Fraction(result['uniform_strip_profile_difference_upper']) / 2)

    def test_rejects_mismatched_rank(self):
        from cross_support_physical_overlap import certify
        first = json.loads((RESEARCH / 'isolated_kernel_17_8.json').read_text())
        second = json.loads((RESEARCH / 'isolated_kernel_19_12.json').read_text())
        with self.assertRaises(ValueError):
            certify(first, second)


if __name__ == '__main__':
    unittest.main()
