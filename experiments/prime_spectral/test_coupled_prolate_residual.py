"""Verify residual-centered error propagation and exact-prolate provenance."""
from fractions import Fraction
import json
from pathlib import Path
import unittest
from flint import arb, ctx
from certified_mode_comparison import box
from coupled_prolate_residual import coupled_gate, run
from prolate_residual_gap_audit import residual_gate

DATA = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


class CoupledProlateTests(unittest.TestCase):
    def test_actual_perturbed_unit_vector_is_enclosed(self):
        with ctx.workprec(256):
            matrix = [[arb(1), arb(0)], [arb(0), arb(3)]]
            trial = [arb(1), arb(0)]
            eta = Fraction(1, 50)
            result = coupled_gate(matrix, trial, eta, arb(1), arb(3))
            direct = [(1-arb(1)/10000).sqrt(), arb(1)/100]
            mu = direct[0]*direct[0]+3*direct[1]*direct[1]
            rho = ((direct[0]-mu*direct[0])**2+(3*direct[1]-mu*direct[1])**2).sqrt()
            self.assertTrue(box(result['exact_rayleigh_interval']).contains(mu))
            self.assertTrue(box(result['exact_residual_norm_enclosure']).contains(rho))
            self.assertEqual(result['residual_and_gap_gate'], 'certified_finite_strip_transfer_inputs')
            self.assertLess(Fraction(result['coupled_rayleigh_error_upper']),
                            Fraction(result['uncoupled_rayleigh_error_upper'])/100)

    def test_gate_with_zero_error_and_invalid_inputs(self):
        with ctx.workprec(128):
            matrix = [[arb(1), arb(0)], [arb(0), arb(3)]]
            result = coupled_gate(matrix, [arb(0), arb(1)], 0, arb(1), arb(3))
            self.assertEqual(result['residual_and_gap_gate'], 'clearance_inconclusive')
            self.assertEqual(Fraction(result['exact_residual_norm_enclosure']['hi']), 0)
            with self.assertRaises(ValueError):
                coupled_gate(matrix, [arb(2), arb(0)], 0, arb(1), arb(3))
            with self.assertRaises(ValueError):
                coupled_gate(matrix, [arb(1), arb(0)], -1, arb(1), arb(3))
            with self.assertRaises(ValueError):
                coupled_gate([[arb(1), arb(1)], [arb(0), arb(3)]], [arb(1), arb(0)], 0, arb(1), arb(3))

    def test_saved_exact_prolate_projection_replays_and_fails_gate(self):
        for cutoff, modes, terms in ((13, 4, 80), (13, 8, 80), (17, 8, 80)):
            with self.subTest(cutoff=cutoff, modes=modes):
                spectrum = DATA / (f'certified_weil_{cutoff}_{modes}.json' if cutoff == 13
                                   else f'isolated_kernel_{cutoff}_{modes}.json')
                candidate = DATA / f'prolate_candidate_{cutoff}_{modes}.json' if cutoff == 13 else None
                result = run(DATA / f'exact_prolate_gate_{cutoff}_{modes}.json', spectrum,
                             DATA / f'prolate_jacobi_{cutoff}_{terms}.json',
                             DATA / f'prolate_vectors_{cutoff}_{terms}.json', candidate)
                saved = json.loads((DATA / f'coupled_prolate_residual_{cutoff}_{modes}.json').read_text())
                self.assertEqual(result, saved)
                self.assertEqual(result['residual_and_gap_gate'], 'certified_above_second')
                self.assertLess(Fraction(result['second_minus_exact_rayleigh_interval']['hi']), 0)
                self.assertGreater(Fraction(result['exact_residual_norm_enclosure']['lo']), 0)
                self.assertLess(Fraction(result['coupled_rayleigh_error_upper']),
                                Fraction(result['uncoupled_rayleigh_error_upper'])/100)


if __name__ == '__main__':
    unittest.main()
