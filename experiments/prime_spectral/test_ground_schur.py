"""Replay the origin-constrained finite Weil resolvent."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from flint import arb, ctx

from certified_mode_comparison import box
from ground_schur import origin_schur_vector, run


ROOT = Path(__file__).resolve().parents[2]


class GroundSchurTests(unittest.TestCase):
    def test_saved_profiles_and_independent_grid_factorization(self):
        for modes, width_gain in ((4, 10**6), (8, 10**8)):
            with self.subTest(modes=modes), ctx.workprec(512):
                path = ROOT / f'research/prime_spectral/certified_weil_13_{modes}.json'
                result = run(path)
                saved = json.loads((ROOT / f'research/prime_spectral/ground_schur_13_{modes}.json').read_text())
                self.assertEqual(result, saved)
                self.assertGreater(Fraction(result['minimum_old_to_schur_coordinate_width_ratio']),
                                   width_gain)
                trace = json.loads((ROOT / f'research/prime_spectral/euler_trace_13_{modes}_y2.json').read_text())
                quotient_at_i = box(trace['anchor_quotient_value'])
                length = arb(13).log()
                grid = arb(1)
                for index in range(1, modes + 1):
                    grid *= 1 + (length / (2 * arb.pi() * index))**2
                exterior_at_i = (length / 2).sinh() / (length / 2) / grid
                self.assertTrue((box(result['profile']['imag_1'])
                                 - quotient_at_i * exterior_at_i).contains(0))

    def test_uncertified_matrix_rejected(self):
        with self.assertRaises(ValueError):
            origin_schur_vector({'status': 'unresolved'})


if __name__ == '__main__':
    unittest.main()
