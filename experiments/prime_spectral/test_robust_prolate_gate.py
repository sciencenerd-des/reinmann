"""Checks the exact finite exclusion radius and fail-closed input pairing."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from robust_prolate_gate import robust_radius, run


ROOT = Path(__file__).resolve().parents[2]


class RobustProlateGateTests(unittest.TestCase):
    def test_saved_cutoff_13_radii(self):
        for modes, lower in ((4, '3.79e-5'), (8, '9.51e-11')):
            with self.subTest(modes=modes):
                result = run(
                    ROOT / f'research/prime_spectral/certified_weil_13_{modes}.json',
                    ROOT / f'research/prime_spectral/prolate_candidate_13_{modes}.json')
                self.assertGreater(Fraction(result['strict_unit_vector_l2_radius']),
                                   Fraction(lower))
                self.assertLess(Fraction(result['strict_unit_vector_l2_radius']),
                                Fraction(lower) * Fraction(101, 100))

    def test_mismatched_gate_fails_closed(self):
        certificate = json.loads((ROOT / 'research/prime_spectral/certified_weil_13_4.json').read_text())
        candidate = json.loads((ROOT / 'research/prime_spectral/prolate_candidate_13_4.json').read_text())
        candidate['modes'] = 8
        with self.assertRaises(ValueError):
            robust_radius(certificate, candidate)
        candidate['modes'] = 4
        candidate['exact_rounded_candidate_gate']['rayleigh_above_second'] = False
        with self.assertRaises(ValueError):
            robust_radius(certificate, candidate)


if __name__ == '__main__':
    unittest.main()
