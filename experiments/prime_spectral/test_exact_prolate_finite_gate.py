"""Replay the exact-prolate finite Weil exclusion from its inputs."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from exact_prolate_finite_gate import certify, run


ROOT = Path(__file__).resolve().parents[2]


class ExactProlateFiniteGateTests(unittest.TestCase):
    def test_exact_prolate_fails_both_saved_finite_gates(self):
        jacobi = json.loads((ROOT / 'research/prime_spectral/prolate_jacobi_13_80.json').read_text())
        vectors = json.loads((ROOT / 'research/prime_spectral/prolate_vectors_13_80.json').read_text())
        for modes in (4, 8):
            with self.subTest(modes=modes):
                result = run(
                    ROOT / f'research/prime_spectral/certified_weil_13_{modes}.json',
                    ROOT / f'research/prime_spectral/prolate_candidate_13_{modes}.json',
                    ROOT / 'research/prime_spectral/prolate_jacobi_13_80.json',
                    ROOT / 'research/prime_spectral/prolate_vectors_13_80.json')
                saved = json.loads((ROOT / f'research/prime_spectral/exact_prolate_gate_13_{modes}.json').read_text())
                self.assertEqual(result['status'], saved['status'])
                for key in ('exact_to_rounded_unit_coefficient_distance_upper',
                            'exact_rayleigh_excess_over_second_even_lower',
                            'input_sha256', 'generator_sha256'):
                    self.assertEqual(result[key], saved[key])
                self.assertTrue(result['rayleigh_above_second_even_certified'])
                self.assertLess(Fraction(result['exact_to_rounded_unit_coefficient_distance_upper']),
                                Fraction(result['robust_exclusion_radius']))
                self.assertGreater(Fraction(result['exact_rayleigh_excess_over_second_even_lower']), 0)

    def test_tampered_rounded_vector_fails_closed(self):
        jacobi = json.loads((ROOT / 'research/prime_spectral/prolate_jacobi_13_80.json').read_text())
        vectors = json.loads((ROOT / 'research/prime_spectral/prolate_vectors_13_80.json').read_text())
        certificate = json.loads((ROOT / 'research/prime_spectral/certified_weil_13_4.json').read_text())
        candidate = json.loads((ROOT / 'research/prime_spectral/prolate_candidate_13_4.json').read_text())
        candidate['rounded_candidate_coefficients'][0] = '0.1'
        with self.assertRaises(ValueError):
            certify(certificate, candidate, jacobi, vectors)


if __name__ == '__main__':
    unittest.main()
