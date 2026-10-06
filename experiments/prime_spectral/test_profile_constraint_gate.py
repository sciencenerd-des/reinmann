"""Replay the two-frequency obstruction and cross-check its Fourier basis."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from flint import arb, ctx

from profile_constraint_gate import _fourier_row, certify, run
from quotient_operator import fourier_profile


ROOT = Path(__file__).resolve().parents[2]


class ProfileConstraintGateTests(unittest.TestCase):
    def test_fourier_row_matches_existing_profile_functional(self):
        with ctx.workprec(256):
            vector = [arb(1), arb(1) / 3, -arb(2) / 5, arb(1) / 7, -arb(1) / 11]
            length = arb(13).log()
            row = _fourier_row(length, 4, 4)
            direct = sum((x * y for x, y in zip(row, vector)), arb(0)) / vector[0]
            full = [vector[abs(j)] / arb(2).sqrt() if j else vector[0]
                    for j in range(-4, 5)]
            reference = fourier_profile(full, length, 4)
            self.assertTrue((direct - reference.real).contains(0))
            self.assertTrue(reference.imag.contains(0))

    def test_saved_obstructions_replay_from_all_inputs(self):
        for modes, excess, tolerance in ((4, '4e-8', '1e-9'),
                                         (8, '3e-17', '1e-22')):
            with self.subTest(modes=modes):
                result = run(
                    ROOT / f'research/prime_spectral/certified_weil_13_{modes}.json',
                    ROOT / f'research/prime_spectral/prolate_candidate_13_{modes}.json',
                    ROOT / 'research/prime_spectral/prolate_jacobi_13_80.json',
                    ROOT / 'research/prime_spectral/prolate_vectors_13_80.json',
                    Fraction(excess), Fraction(tolerance))
                saved = json.loads((ROOT / f'research/prime_spectral/profile_constraint_13_{modes}.json').read_text())
                self.assertEqual(result, saved)
                self.assertEqual(len(result['constrained_shifted_ldl_pivot_lower']), modes - 1)
                self.assertTrue(all(Fraction(pivot) > 0 for pivot in
                                    result['constrained_shifted_ldl_pivot_lower']))

    def test_excess_too_large_fails_closed(self):
        certificate = json.loads((ROOT / 'research/prime_spectral/certified_weil_13_4.json').read_text())
        exact_gate = json.loads((ROOT / 'research/prime_spectral/exact_prolate_gate_13_4.json').read_text())
        with self.assertRaises(ArithmeticError):
            certify(certificate, exact_gate, Fraction(1))


if __name__ == '__main__':
    unittest.main()
