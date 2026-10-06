"""Replay finite derivative kicks and check the endpoint normalization."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from flint import acb, arb, ctx

from certified_weil import certified_matrix, correlation_ball
from eigenvalue_response import _fourier_functional
from isolated_kernel import isolated_spectrum
from prime_threshold_jump import _prime_power_exponent, run


RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


class PrimeThresholdJumpTests(unittest.TestCase):
    def test_endpoint_correlation_slope_matches_even_and_off_diagonal_cases(self):
        # The written proof gives 2/L for every integer Fourier pair.
        # Finite differences check the implementation, not the limiting proof.
        with ctx.workprec(256):
            length = arb(17).log()
            step = arb(2)**-24
            expected = arb(2) / length
            for first, second in ((0, 0), (1, 1), (0, 1), (1, 2), (-2, 3)):
                with self.subTest(indices=(first, second)):
                    endpoint = correlation_ball(first, second, length, length)
                    self.assertTrue(endpoint.contains(0))
                    slope = (correlation_ball(first, second, length, length + step)
                             - endpoint) / step
                    self.assertLess(abs(float((slope - expected).mid())), 1e-5)

    def test_independent_rank_one_perturbation_secant(self):
        # Perturb the complete finite matrix, rather than reusing the
        # constrained inverse formula. The secant checks its sign and scale.
        with ctx.workprec(512):
            cutoff, modes = 17, 8
            _, matrix, _ = certified_matrix(cutoff, modes)
            boundary = [arb(1)] + [arb(2).sqrt() for _ in range(modes)]
            coefficient = arb(2) / arb(cutoff).sqrt()
            step = arb('1e-27')
            functional = _fourier_functional(modes, arb(cutoff).log(), acb(4))

            def response(sign):
                perturbed = [[matrix[i][j] - sign * step * coefficient
                              * boundary[i] * boundary[j]
                              for j in range(modes + 1)]
                             for i in range(modes + 1)]
                eigenvalues, raw = isolated_spectrum(perturbed)
                normalized = [arb(1)] + [value / raw[0] for value in raw[1:]]
                profile = sum((a*b for a, b in zip(functional, normalized)), arb(0))
                return eigenvalues[0], profile

            plus, minus = response(1), response(-1)
            eigen_secant = (plus[0] - minus[0]) / (2 * step)
            profile_secant = (plus[1] - minus[1]) / (2 * step)
            saved = json.loads((RESEARCH / 'prime_threshold_jump_17_8.json').read_text())
            for secant, record, tolerance in (
                    (eigen_secant,
                     saved['lowest_even_eigenvalue_derivative_jump'], 1e-30),
                    (profile_secant,
                     saved['ground_profile_derivative_jump']['real_4'], 1e-10)):
                midpoint = (Fraction(record['lo']) + Fraction(record['hi'])) / 2
                self.assertLess(abs(float(secant.mid()) - float(midpoint)), tolerance)

    def test_positive_kernel_model_separates_profile_and_eigenvalue_kinks(self):
        with ctx.workprec(256):
            functional = _fourier_functional(1, 2 * arb.pi(), acb(1))
            step = arb(2)**-70
            for denominator in (4, 16, 64):
                with self.subTest(epsilon=f'1/{denominator}'):
                    epsilon = arb(1) / arb(denominator)
                    h = -(1 - epsilon) / arb(2).sqrt()
                    ground = [arb(1), h]
                    excited = [-h, arb(1)]
                    boundary = [arb(1), arb(2).sqrt()]
                    norm_squared = 1 + h*h
                    self.assertTrue((boundary[0] + boundary[1]*h - epsilon).contains(0))
                    matrix = [[epsilon**2 * (1 if i == j else 0)
                               + epsilon / norm_squared * excited[i] * excited[j]
                               for j in range(2)] for i in range(2)]
                    for i in range(2):
                        self.assertTrue((sum((matrix[i][j] * ground[j]
                                              for j in range(2)), arb(0))
                                         - epsilon**2 * ground[i]).contains(0))

                    def response(sign):
                        perturbed = [[matrix[i][j] - sign * step
                                      * boundary[i] * boundary[j]
                                      for j in range(2)] for i in range(2)]
                        eigenvalues, raw = isolated_spectrum(perturbed)
                        profile = functional[0] + functional[1] * raw[1] / raw[0]
                        return eigenvalues[0], profile

                    plus, minus = response(1), response(-1)
                    eigen_secant = (plus[0] - minus[0]) / (2 * step)
                    profile_secant = (plus[1] - minus[1]) / (2 * step)
                    self.assertLess(abs(float(eigen_secant.mid()
                                              + epsilon**2 / norm_squared)), 1e-10)
                    self.assertLess(abs(float(profile_secant.mid()
                                              + (3 - epsilon) / 2)), 1e-10)
                    self.assertGreater(-profile_secant, arb(1))
                    self.assertLess(abs(float(eigen_secant.mid())),
                                    1 / denominator)

    def test_saved_prime_threshold_kicks_replay(self):
        for cutoff in (17, 19):
            for modes in (8, 12, 16):
                with self.subTest(cutoff=cutoff, modes=modes):
                    result = run(RESEARCH / f'isolated_kernel_{cutoff}_{modes}.json')
                    saved = json.loads((RESEARCH / f'prime_threshold_jump_{cutoff}_{modes}.json').read_text())
                    self.assertEqual(result, saved)
                    jump = result['lowest_even_eigenvalue_derivative_jump']
                    self.assertLess(Fraction(jump['hi']), 0)
                    real_profile = result['ground_profile_derivative_jump']['real_4']
                    imaginary_profile = result['ground_profile_derivative_jump']['imag_1']
                    self.assertLess(Fraction(real_profile['hi']), 0)
                    self.assertGreater(Fraction(imaginary_profile['lo']), 0)
                    # Tiny eigenvalue kinks do not bound the profile kinks.
                    self.assertGreater(-Fraction(real_profile['hi']),
                                       10**20 * -Fraction(jump['lo']))

    def test_non_prime_power_threshold_rejected(self):
        self.assertEqual(_prime_power_exponent(4), (2, 2))
        self.assertEqual(_prime_power_exponent(9), (3, 2))
        with self.assertRaises(ValueError):
            _prime_power_exponent(18)


if __name__ == '__main__':
    unittest.main()
