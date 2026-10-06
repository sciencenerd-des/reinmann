"""Whole-cell even eigenfamily replay and independent integral eigenpairs."""
import json
from pathlib import Path
import unittest

from flint import acb, arb, arb_mat, ctx

from certified_weil import entry
from eigenvalue_response import _fourier_functional
from isolated_kernel import isolated_spectrum
from weil_eigenfamily import _validate, ball, box, run
from weil_matrix import prime_powers
from weil_support_taylor import evaluate


RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


def _original_even(length, modes):
    powers = prime_powers(18)
    cache = {}

    def cell(i, j):
        key = min((i, j), (j, i), (-i, -j), (-j, -i))
        if key not in cache:
            cache[key] = entry(*key, length, powers, 0)
        return cache[key]

    result = [[arb(0) for _ in range(modes + 1)] for _ in range(modes + 1)]
    result[0][0] = cell(0, 0)
    for i in range(1, modes + 1):
        result[0][i] = result[i][0] = arb(2).sqrt() * cell(0, i)
        for j in range(1, modes + 1):
            result[i][j] = cell(i, j) + cell(i, -j)
    return result


class WeilEigenfamilyTests(unittest.TestCase):
    def test_saved_full_cover_replays(self):
        saved = json.loads((RESEARCH / 'weil_eigenfamily_17_19_8.json').read_text())
        self.assertEqual(run(RESEARCH / 'weil_support_taylor_17_19_8.json'), saved)
        self.assertEqual(saved['certified_subcells'], saved['subdivisions'])
        self.assertTrue(saved['all_origin_strip_transfers_certified'])
        self.assertTrue(saved['all_even_ground_eigenvalues_positive'])
        with ctx.workprec(256):
            self.assertLess(ball(saved['uniform_strip_profile_error_upper']), arb('1e-8'))

    def test_independent_integral_eigenpairs_and_profiles_at_boundaries_and_center(self):
        saved = json.loads((RESEARCH / 'weil_eigenfamily_17_19_8.json').read_text())
        with ctx.workprec(1024):
            center = box(saved['log_support_center'])
            for index, length in ((0, arb(17).log()), (16, center), (31, arb(19).log())):
                local = saved['cells'][index]
                displacement = length - center - ball(local['center_offset'])
                self.assertLessEqual(abs(displacement).upper(), ball(local['half_width']).upper() + arb(2)**-900)
                basis = arb_mat([[box(x) for x in row] for row in local['center_basis']])
                coordinates = [evaluate([ball(x) for x in row], displacement)
                               for row in local['ground_candidate_coefficients']]
                candidate = [sum((basis[i, j] * coordinates[j] for j in range(9)), arb(0))
                             for i in range(9)]
                values, raw = isolated_spectrum(_original_even(length, 8))
                if raw[0] < 0:
                    raw = [-x for x in raw]
                norm = sum((x**2 for x in raw), arb(0)).sqrt()
                unit = [x / norm for x in raw]
                candidate_norm = sum((x**2 for x in candidate), arb(0)).sqrt()
                distance = sum(((a - b / candidate_norm)**2
                                for a, b in zip(unit, candidate)), arb(0)).sqrt()
                self.assertLessEqual(distance.upper(), ball(local['uniform_unit_ground_distance_upper']))
                approximate_lambda = evaluate([ball(x) for x in local['ground_eigenvalue_candidate_coefficients']], displacement)
                self.assertLessEqual(abs(values[0] - approximate_lambda).upper(),
                                     ball(local['uniform_eigenvalue_disk_radius_upper']))
                for argument in (acb(4), acb(8), acb(0, arb(2) / 5)):
                    functional = _fourier_functional(8, length, argument)
                    true_profile = sum((a * b for a, b in zip(functional, raw)), arb(0)) / raw[0]
                    trial_profile = sum((a * b for a, b in zip(functional, candidate)), arb(0)) / candidate[0]
                    self.assertLessEqual(abs(true_profile - trial_profile).upper(),
                                         ball(local['uniform_origin_normalized_strip_profile_error_upper']))

    def test_spectral_crossing_fails_the_uniform_gate(self):
        with ctx.workprec(1024):
            coefficients = [arb_mat([[1, 0], [0, 3]]), arb_mat([[10, 0], [0, -10]])]
            result = _validate(coefficients, arb(1) / 5, arb(0), 1, arb(1))
            self.assertEqual(result['status'], 'finite_eigenfamily_candidate_validation_unresolved')
            self.assertIsNone(result['uniform_unit_ground_distance_upper'])


if __name__ == '__main__':
    unittest.main()
