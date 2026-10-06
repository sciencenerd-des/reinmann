"""Replay one-sided ground-profile derivatives and independent jump data."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from flint import acb, arb, ctx

from eigenvalue_response import _fourier_functional
from smooth_support_profile import _fourier_length_derivative, run


RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


def _upper(value):
    return Fraction(str(value.upper().fmpq()))


def _overlap(first, second):
    return max(Fraction(first['lo']), Fraction(second['lo'])) <= min(
        Fraction(first['hi']), Fraction(second['hi']))


class SmoothSupportProfileTests(unittest.TestCase):
    def test_fourier_length_derivative_matches_independent_secant(self):
        with ctx.workprec(512):
            length = arb(17).log()
            step = arb(1) / 4096
            for argument in (acb(4), acb(8), acb(0, 1)):
                analytic = _fourier_length_derivative(8, length, argument)
                plus = _fourier_functional(8, length + step, argument)
                minus = _fourier_functional(8, length - step, argument)
                for expected, high, low in zip(analytic, plus, minus):
                    self.assertLess(_upper(abs((high - low) / (2 * step) - expected)),
                                    Fraction(1, 10000))

    def test_replay_and_independent_rank_one_jump(self):
        for cutoff in (17, 19):
            with self.subTest(cutoff=cutoff):
                result = run(cutoff, 8)
                saved = json.loads((RESEARCH / f'smooth_support_profile_{cutoff}_8.json').read_text())
                previous = json.loads((RESEARCH / f'prime_threshold_jump_{cutoff}_8.json').read_text())
                self.assertEqual(result, saved)
                self.assertTrue(_overlap(
                    result['lowest_eigenvalue_derivative_jump'],
                    previous['lowest_even_eigenvalue_derivative_jump']))
                for label in ('real_4', 'real_8', 'imag_1'):
                    self.assertTrue(_overlap(
                        result['profile_derivative_jump'][label],
                        previous['ground_profile_derivative_jump'][label]))


if __name__ == '__main__':
    unittest.main()
