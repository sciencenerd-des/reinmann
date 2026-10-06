"""Check the exact Legendre algebra and saved analytic projection balls."""
import json
from fractions import Fraction
import math
from pathlib import Path
import unittest

from certified_prolate_projection import _polynomials, project_trials


ROOT = Path(__file__).resolve().parents[2]


class CertifiedProlateProjectionTests(unittest.TestCase):
    def test_legendre_recurrence_has_known_degree_four_polynomial(self):
        coefficients = _polynomials(4)[4]
        self.assertEqual(coefficients,
                         [Fraction(3, 8), 0, Fraction(-15, 4), 0, Fraction(35, 8)])

    def test_saved_analytic_projection_replays(self):
        vectors = json.loads((ROOT / 'research/prime_spectral/prolate_vectors_13_80.json').read_text())
        for modes in (4, 8):
            with self.subTest(modes=modes):
                result = project_trials(13, modes,
                                        vectors['modes']['0']['trial_vector'],
                                        vectors['modes']['2']['trial_vector'])
                saved = json.loads((ROOT / f'research/prime_spectral/prolate_projection_trial_13_{modes}.json').read_text())
                for key in ('unit_coefficient_intervals', 'projection_norm_interval',
                            'zero_integral_ratio_interval'):
                    self.assertEqual(result[key], saved[key])
                for cell in result['unit_coefficient_intervals']:
                    self.assertLess(Fraction(cell['hi']) - Fraction(cell['lo']), Fraction('1e-30'))

    def test_closed_formula_agrees_with_independent_piecewise_integral(self):
        result = project_trials(2, 1, ['1', '0', '0'],
                                ['0.2', '0.9797958971132712', '0'])
        length = math.log(2)
        left, right = -length / 2, length / 2
        panels = 10000

        def simpson(mode):
            total = 0.0
            for index in range(panels + 1):
                t = left + (right - left) * index / panels
                z = math.exp(t) / math.sqrt(2)
                polynomial = (3 * z * z - 1) / 2
                basis = (1 / math.sqrt(length) if mode == 0 else
                         math.sqrt(2 / length) * math.cos(2 * math.pi * (t - left) / length))
                weight = 1 if index in (0, panels) else (4 if index % 2 else 2)
                total += weight * math.exp(t / 2) * polynomial * basis
            return total * (right - left) / (3 * panels)

        direct = [simpson(0), simpson(1)]
        norm = math.hypot(*direct)
        for cell, value in zip(result['unit_coefficient_intervals'], direct):
            center = float((Fraction(cell['lo']) + Fraction(cell['hi'])) / 2)
            self.assertAlmostEqual(center, value / norm, delta=1e-10)

    def test_projection_with_multiple_prime_sum_thresholds(self):
        # The synthetic zero-integral combination is a scalar multiple of P_2.
        # Hold the active n-set fixed on each open piece: k has jumps at its
        # thresholds, so an endpoint must use the limit from that piece.
        cutoff, modes, panels = 13, 4, 512
        result = project_trials(cutoff, modes, ['1', '0', '0'],
                                ['0.2', '0.9797958971132712', '0'])
        length = math.log(cutoff)
        lam = math.sqrt(cutoff)
        thresholds = sorted(math.log(lam / n) for n in range(1, cutoff + 1))
        direct = []
        for mode in range(modes + 1):
            total = 0.0
            for left, right in zip(thresholds[:-1], thresholds[1:]):
                active = math.floor(lam / math.exp((left + right) / 2))
                step = (right - left) / panels
                subtotal = 0.0
                for index in range(panels + 1):
                    t = left + index * step
                    u = math.exp(t)
                    h = sum((3 * (n * u / lam)**2 - 1) / 2
                            for n in range(1, active + 1))
                    basis = (1 / math.sqrt(length) if mode == 0 else
                             math.sqrt(2 / length) * math.cos(
                                 2 * math.pi * mode * (t + length / 2) / length))
                    weight = 1 if index in (0, panels) else 4 if index % 2 else 2
                    subtotal += weight * math.sqrt(u) * h * basis
                total += step * subtotal / 3
            direct.append(total)
        norm = math.sqrt(sum(value * value for value in direct))
        for cell, value in zip(result['unit_coefficient_intervals'], direct):
            center = float((Fraction(cell['lo']) + Fraction(cell['hi'])) / 2)
            self.assertAlmostEqual(center, value / norm, delta=1e-10)


if __name__ == '__main__':
    unittest.main()
