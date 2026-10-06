"""Replay exact-prolate low-cluster mass certificates."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from prolate_cluster_gate import certify, run


ROOT = Path(__file__).resolve().parents[2]
RESEARCH = ROOT / 'research/prime_spectral'
JACOBI = RESEARCH / 'prolate_jacobi_13_80.json'
VECTORS = RESEARCH / 'prolate_vectors_13_80.json'


class ProlateClusterGateTests(unittest.TestCase):
    def test_exact_prolate_near_first_four_even_modes(self):
        for modes in (4, 8, 12, 16):
            with self.subTest(modes=modes):
                spectrum = RESEARCH / f'{"certified_weil" if modes <= 8 else "isolated_kernel"}_13_{modes}.json'
                candidate = (RESEARCH / f'prolate_candidate_13_{modes}.json'
                             if modes <= 8 else None)
                result = run(RESEARCH / f'exact_prolate_gate_13_{modes}.json',
                             spectrum, JACOBI, VECTORS, candidate)
                saved = json.loads((RESEARCH / f'prolate_cluster_13_{modes}.json').read_text())
                self.assertEqual(result, saved)
                self.assertEqual(result['retained_even_eigenvectors'], 4)
                self.assertLess(Fraction(result['squared_mass_outside_cluster_upper']),
                                Fraction(3, 10_000))
                self.assertGreater(Fraction(result['squared_mass_inside_cluster_lower']),
                                   Fraction(9997, 10000))

    def test_spectrum_dimension_rejected(self):
        exact = json.loads((RESEARCH / 'exact_prolate_gate_13_4.json').read_text())
        with self.assertRaises(ValueError):
            certify(exact, [{'lo': '1', 'hi': '1'}],
                    {'lo': '1', 'hi': '1'}, Fraction(1), Fraction(0))

    def test_cutoff_19_higher_ranks_fail_four_mode_rayleigh_gate(self):
        for modes in (12, 16):
            with self.subTest(modes=modes):
                exact = json.loads((RESEARCH / f'exact_prolate_gate_19_{modes}.json').read_text())
                spectrum = json.loads((RESEARCH / f'isolated_kernel_19_{modes}.json').read_text())
                norm = Fraction(exact['even_matrix_operator_norm_upper'])
                error = Fraction(exact['exact_to_trial_unit_coefficient_distance_upper'])
                exact_rayleigh_lower = Fraction(exact['trial_rayleigh_interval']['lo']) - 2 * norm * error
                self.assertGreater(exact_rayleigh_lower,
                                   Fraction(spectrum['even_spectrum'][4]['hi']))
                with self.assertRaisesRegex(ArithmeticError, 'cluster Rayleigh gate'):
                    certify(exact, spectrum['even_spectrum'],
                            exact['trial_rayleigh_interval'], norm, error)


if __name__ == '__main__':
    unittest.main()
