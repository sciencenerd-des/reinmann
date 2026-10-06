"""Check the paired-spectrum resolvent identity and finite Euler probe."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from flint import arb, ctx

from euler_region_trace import (compare, compare_isolated, run,
                                secular_trace_at_height, trace_at_height)
from isolated_kernel import run as isolate_kernel
from quotient_operator import build


ROOT = Path(__file__).resolve().parents[2]


class EulerRegionTraceTests(unittest.TestCase):
    def test_paired_diagonal_resolvent(self):
        with ctx.workprec(256):
            matrix = [[arb(value) if i == j else arb(0)
                       for j in range(4)]
                      for i, value in enumerate((-2, 2, -3, 3))]
            actual = trace_at_height(matrix, arb(2))
            expected = 4 * (arb(1) / 8 + arb(1) / 13)
            self.assertTrue((actual - expected).contains(0))

    def test_rank_one_secular_formula(self):
        with ctx.workprec(256):
            coefficients = [arb(1) / 4, arb(1) / 2, arb(1) / 4]
            quotient = [[-arb(3) / 4, -arb(1) / 4],
                        [arb(1) / 4, arb(3) / 4]]
            secular = secular_trace_at_height(coefficients, 2 * arb.pi(), arb(2))
            self.assertTrue((secular['derivative'] - arb(8) / 9).contains(0))
            self.assertTrue(secular['characteristic_value'].contains(9))
            self.assertTrue((secular['derivative']
                             - trace_at_height(quotient, arb(2))).contains(0))

    def test_cutoff_13_finite_separations_replay(self):
        for cutoff, modes in ((13, 4), (13, 8), (13, 12), (13, 16),
                              (17, 16), (23, 16)):
            with self.subTest(cutoff=cutoff, modes=modes):
                kind = 'certified_weil' if cutoff == 13 and modes in (4, 8) else 'isolated_kernel'
                path = ROOT / f'research/prime_spectral/{kind}_{cutoff}_{modes}.json'
                actual = run(path, '2')
                saved = json.loads((ROOT / f'research/prime_spectral/euler_trace_{cutoff}_{modes}_y2.json').read_text())
                self.assertEqual(actual, saved)
                self.assertTrue(actual['strict_quotient_below_xi'])
                self.assertGreater(Fraction(actual['anchor_quotient_value']['lo']), 1)
                self.assertLess(Fraction(actual['quotient_log_derivative']['hi']),
                                Fraction(actual['xi_log_derivative_enclosure']['lo']))

    def test_actual_mode_four_agrees_with_dense_trace(self):
        with ctx.workprec(512):
            path = ROOT / 'research/prime_spectral/certified_weil_13_4.json'
            coefficients, length, quotient, _ = build(json.loads(path.read_text()))
            secular = secular_trace_at_height(coefficients, length, arb(2))
            dense = trace_at_height(quotient, arb(2))
            self.assertTrue((secular['derivative'] - dense).contains(0))

    def test_isolated_and_original_mode_four_overlap(self):
        original = run(ROOT / 'research/prime_spectral/certified_weil_13_4.json', '2')
        isolated = compare_isolated(isolate_kernel(13, 4), '2')
        self.assertLessEqual(Fraction(original['quotient_log_derivative']['lo']),
                             Fraction(isolated['quotient_log_derivative']['hi']))
        self.assertLessEqual(Fraction(isolated['quotient_log_derivative']['lo']),
                             Fraction(original['quotient_log_derivative']['hi']))

    def test_mesh_budget_covers_an_unsampled_height(self):
        path = ROOT / 'research/prime_spectral/isolated_kernel_13_16.json'
        result = run(path, '2', mesh_segments=16)
        saved = json.loads((ROOT / 'research/prime_spectral/euler_mesh_13_16_m16.json').read_text())
        self.assertEqual(result, saved)
        mesh = result['mesh_budget']
        self.assertEqual(Fraction(mesh['target_lipschitz_upper']), Fraction(40, 9))
        probe = compare_isolated(json.loads(path.read_text()), '1.03125')
        quotient = probe['quotient_log_derivative']
        target = probe['finite_prime_power_target']
        error = max(abs(Fraction(quotient['lo']) - Fraction(target['hi'])),
                    abs(Fraction(quotient['hi']) - Fraction(target['lo'])))
        self.assertLess(error, Fraction(mesh['integrated_absolute_error_upper']))

    def test_finer_mesh_certifies_interval_wide_signed_gap(self):
        for cutoff in (13, 23):
            with self.subTest(cutoff=cutoff):
                path = ROOT / f'research/prime_spectral/isolated_kernel_{cutoff}_16.json'
                result = run(path, '2', mesh_segments=64)
                saved = json.loads((ROOT / f'research/prime_spectral/euler_mesh_{cutoff}_16_m64.json').read_text())
                self.assertEqual(result, saved)
                budget = result['mesh_budget']
                self.assertTrue(budget['strict_quotient_below_finite_target_on_interval'])
                self.assertGreater(Fraction(budget['uniform_target_minus_quotient_lower']), 0)
                self.assertLess(Fraction(budget['integrated_absolute_error_lower']),
                                Fraction(budget['integrated_absolute_error_upper']))
                probe = compare_isolated(json.loads(path.read_text()), '1.0078125')
                actual_gap = (Fraction(probe['finite_prime_power_target']['lo'])
                              - Fraction(probe['quotient_log_derivative']['hi']))
                self.assertGreater(actual_gap,
                                   Fraction(budget['uniform_target_minus_quotient_lower']))

    def test_outside_euler_region_rejected(self):
        certificate = json.loads((ROOT / 'research/prime_spectral/certified_weil_13_4.json').read_text())
        with self.assertRaises(ValueError):
            compare(certificate, '0.5')
        with self.assertRaises(ValueError):
            run(ROOT / 'research/prime_spectral/certified_weil_13_4.json', '2',
                mesh_segments=0)


if __name__ == '__main__':
    unittest.main()
