"""Independent checks of the finite Weil support derivative."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from flint import arb, ctx

from certified_weil import entry
from smooth_support_derivative import entry_derivative, run
from weil_matrix import prime_powers


ROOT = Path(__file__).resolve().parents[2]


def _upper(value):
    return Fraction(str(value.upper().fmpq()))


class SmoothSupportDerivativeTests(unittest.TestCase):
    def test_interior_secant_agrees_with_original_weil_entry(self):
        # The original integral formula is evaluated independently of the
        # differentiated fixed-interval formula. This is a numerical
        # diagnostic; the analytic differentiation supplies the proof.
        with ctx.workprec(512):
            length = arb(18).log()
            step = arb(1) / 4096
            powers = prime_powers(18)
            for indices in ((0, 0), (0, 1), (1, 1)):
                with self.subTest(indices=indices):
                    derivative = entry_derivative(*indices, length, powers,
                                                  include_endpoint=True)
                    secant = (entry(*indices, length + step, powers, 0)
                              - entry(*indices, length - step, powers, 0)) / (2 * step)
                    self.assertLess(_upper(abs(secant - derivative)), Fraction(1, 10000))

    def test_saved_prime_threshold_replays(self):
        for cutoff, modes in ((17, 1), (17, 8), (19, 8)):
            with self.subTest(cutoff=cutoff, modes=modes):
                result = run(cutoff, modes)
                saved = json.loads((ROOT / 'research/prime_spectral/'
                                    f'smooth_support_derivative_{cutoff}_{modes}.json').read_text())
                self.assertEqual(result, saved)
                self.assertEqual(result['status'],
                                 'certified_finite_smooth_weil_derivative_and_prime_jump')


if __name__ == '__main__':
    unittest.main()
