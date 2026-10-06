"""Replay a finite exact-prolate residual gate and its decision boundary."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from flint import arb, ctx

from prolate_residual_gap_audit import residual_gate, run


ROOT = Path(__file__).resolve().parents[2]
RESEARCH = ROOT / 'research/prime_spectral'


class ProlateResidualGapAuditTests(unittest.TestCase):
    def test_synthetic_gate_passes_and_fails(self):
        with ctx.workprec(128):
            matrix = [[arb(1), arb(0), arb(0)],
                      [arb(0), arb(3), arb(0)],
                      [arb(0), arb(0), arb(5)]]
            passed = residual_gate(matrix, [arb(1), arb(0), arb(0)], Fraction(0),
                                   arb(1), arb(3))
            failed = residual_gate(matrix, [arb(0), arb(0), arb(1)], Fraction(0),
                                   arb(1), arb(3))
        self.assertEqual(passed['residual_and_gap_gate'],
                         'certified_finite_strip_transfer_inputs')
        self.assertEqual(failed['residual_and_gap_gate'], 'certified_above_second')
        self.assertTrue(passed['origin_protected_by_residual'])
        self.assertIsNone(failed['ground_distance_upper_from_residual'])
        self.assertEqual(Fraction(passed['exact_residual_norm_enclosure']['hi']), 0)
        self.assertEqual(Fraction(failed['exact_residual_norm_enclosure']['hi']), 0)

    def test_unit_error_propagates_to_an_actual_perturbed_vector(self):
        with ctx.workprec(128):
            matrix = [[arb(1), arb(0)], [arb(0), arb(3)]]
            audit = residual_gate(matrix, [arb(1), arb(0)], Fraction(1, 50),
                                  arb(1), arb(3))
            true_vector = [(1 - arb(1) / 10000).sqrt(), arb(1) / 100]
            product = [true_vector[0], 3 * true_vector[1]]
            rayleigh = sum((a * b for a, b in zip(true_vector, product)), arb(0))
            residual = sum(((b - rayleigh * a)**2
                            for a, b in zip(true_vector, product)), arb(0)).sqrt()
        for value, cell in ((rayleigh, audit['exact_rayleigh_interval']),
                            (residual, audit['exact_residual_norm_enclosure'])):
            self.assertLessEqual(Fraction(cell['lo']), Fraction(str(value.lower().fmpq())))
            self.assertGreaterEqual(Fraction(cell['hi']), Fraction(str(value.upper().fmpq())))

    def test_saved_exact_prolate_gates_replay(self):
        for cutoff, modes, terms in ((17, 8, 80), (17, 16, 80), (19, 16, 100)):
            with self.subTest(cutoff=cutoff, modes=modes):
                result = run(RESEARCH / f'exact_prolate_gate_{cutoff}_{modes}.json',
                             RESEARCH / f'isolated_kernel_{cutoff}_{modes}.json',
                             RESEARCH / f'prolate_jacobi_{cutoff}_{terms}.json',
                             RESEARCH / f'prolate_vectors_{cutoff}_{terms}.json')
                saved = json.loads((RESEARCH / f'prolate_residual_gap_{cutoff}_{modes}.json').read_text())
                self.assertEqual(result, saved)
                self.assertEqual(result['residual_and_gap_gate'], 'certified_above_second')
                self.assertGreater(Fraction(result['exact_residual_norm_enclosure']['lo']), 0)
                self.assertLess(Fraction(result['second_minus_exact_rayleigh_interval']['hi']), 0)


if __name__ == '__main__':
    unittest.main()
