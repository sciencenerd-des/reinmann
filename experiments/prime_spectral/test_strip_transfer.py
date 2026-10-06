"""Regression checks for residual/gap and strip Fourier transfer."""
from __future__ import annotations

from pathlib import Path
import unittest

from flint import arb, ctx

from quotient_operator import fourier_profile
from strip_transfer import (finite_comparison, normalized_profile_upper,
                            rayleigh_distance_upper, residual_distance_upper,
                            strip_functional_norm)


COMPARISON = (Path(__file__).resolve().parents[2]/
              'research/prime_spectral/mode_comparison_13_4_8.json')


class StripTransferTests(unittest.TestCase):
    def test_residual_bound_controls_origin_normalized_profiles(self):
        with ctx.workprec(256):
            # A=diag(1,3); v is its lowest unit eigenvector and w a
            # Pythagorean unit candidate. All spectral inputs are exact.
            v = [arb(1), arb(0)]
            w = [arb(120)/121, arb(11)/121]
            rayleigh = w[0]**2+3*w[1]**2
            residual = ((1-rayleigh)**2*w[0]**2
                        +(3-rayleigh)**2*w[1]**2).sqrt()
            distance = residual_distance_upper(rayleigh, residual, 3)
            actual_distance = ((v[0]-w[0])**2+(v[1]-w[1])**2).sqrt()
            self.assertLess(actual_distance, distance)
            bound = normalized_profile_upper(2, arb('0.4'), w[0], distance)
            self.assertLess(bound, arb('0.316'))

            def profile(vector, z):
                coefficients = [vector[1]/arb(2).sqrt(), vector[0],
                                vector[1]/arb(2).sqrt()]
                return fourier_profile(coefficients, arb(2), z)

            for z in (0, 1, 2, 1+0.4j, 3+0.2j):
                self.assertLess(abs(profile(v, z)-profile(w, z)), bound)

    def test_fail_closed_without_gap_or_origin(self):
        with self.assertRaises(ArithmeticError):
            residual_distance_upper(3, arb('0.01'), 3)
        with self.assertRaises(ArithmeticError):
            rayleigh_distance_upper(3, 1, 3)
        with self.assertRaises(ArithmeticError):
            normalized_profile_upper(2, 0, arb('0.1'), arb('0.1'))
        with self.assertRaises(ValueError):
            strip_functional_norm(2, -1)

    def test_finite_prime_comparison_on_critical_substrip(self):
        with ctx.workprec(256):
            self.assertEqual(strip_functional_norm(2, 0), 1)
            self.assertGreater(strip_functional_norm(2, arb('0.4')), 1)
            row = finite_comparison(COMPARISON, '2/5')
            self.assertEqual(row['status'], 'finite_strip_profile_comparison_not_convergence')
            self.assertLess(arb(row['profile_difference_upper']), arb('0.294'))
            with self.assertRaises(ValueError):
                finite_comparison(COMPARISON, '1/2')

    def test_rayleigh_excess_controls_ground_profile_without_residual(self):
        with ctx.workprec(256):
            ground = [arb(1), arb(0)]
            candidate = [arb(120)/121, arb(11)/121]
            mu = candidate[0]**2 + 3*candidate[1]**2
            distance = rayleigh_distance_upper(mu, 1, 3)
            actual = ((ground[0]-candidate[0])**2
                      +(ground[1]-candidate[1])**2).sqrt()
            self.assertLess(actual, distance)
            bound = normalized_profile_upper(2, arb('0.4'), candidate[0], distance)
            for z in (1, 2, 1+0.4j, 3+0.2j):
                def profile(vector):
                    coefficients = [vector[1]/arb(2).sqrt(), vector[0],
                                    vector[1]/arb(2).sqrt()]
                    return fourier_profile(coefficients, arb(2), z)
                self.assertLess(abs(profile(ground)-profile(candidate)), bound)


if __name__ == '__main__':
    unittest.main()
