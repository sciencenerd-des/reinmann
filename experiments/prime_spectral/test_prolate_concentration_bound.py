"""Regression checks for the exact prolate/Weil interface classifier."""
import unittest
from fractions import Fraction

from prolate_concentration_bound import run


class ProlateConcentrationBoundTests(unittest.TestCase):
    def test_cutoff_13_effective_bounds(self):
        result = run(13)
        self.assertEqual(result['status'],
                         'analytic_prolate_compression_bounds_not_weil_transfer')
        self.assertLess(Fraction(result['concentration_deficit_0_upper']),
                        Fraction('2.61e-36'))
        self.assertLess(Fraction(result['concentration_deficit_4_upper']),
                        Fraction('7.73e-29'))
        self.assertLess(Fraction(result['compressed_fourier_theta_4_lower']), 1)
        self.assertGreater(Fraction(result['compressed_fourier_theta_4_lower']), 0)

    def test_invalid_cutoff_fails_closed(self):
        for cutoff in (1, 2.0, True):
            with self.subTest(cutoff=cutoff), self.assertRaises(ValueError):
                run(cutoff)

    def test_start_of_claimed_cutoff_range(self):
        result = run(2)
        self.assertLess(Fraction(result['concentration_deficit_4_upper']), 1)


if __name__ == '__main__':
    unittest.main()
