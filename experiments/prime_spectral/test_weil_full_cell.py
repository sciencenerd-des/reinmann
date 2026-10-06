"""Full parity/spatial replay, independent integrals, and exact boundary algebra."""
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import unittest

from flint import arb, arb_mat, ctx

from certified_weil import certified_matrix, entry
from positive_kernel import bernstein_coefficients
from smooth_support_derivative import entry_derivative
from weil_eigenfamily import ball, box, center_basis, run as even_run
from weil_matrix import prime_powers
from weil_odd_cell import full_gap, run as parity_run, validate_partition, validate_spectrum
from weil_spatial_cell import bernstein_functionals, certify, run as spatial_run
from weil_support_taylor import evaluate

RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'
TAYLOR = RESEARCH / 'weil_support_taylor_17_19_8_degree64.json'
EVEN = RESEARCH / 'weil_eigenfamily_17_19_8_degree64.json'
PARITY = RESEARCH / 'weil_odd_cell_17_19_8_degree64.json'
SPATIAL = RESEARCH / 'weil_spatial_cell_17_19_8_degree64.json'


class WeilFullCellTests(unittest.TestCase):
    def test_degree64_even_and_full_parity_cover_replay(self):
        even, parity = json.loads(EVEN.read_text()), json.loads(PARITY.read_text())
        self.assertEqual(even_run(TAYLOR), even)
        self.assertEqual(parity_run(TAYLOR, EVEN), parity)
        self.assertEqual(parity['certified_parity_subcells'], 32)
        self.assertGreater(Fraction(parity['uniform_full_weil_gap_lower']), 0)

    def test_original_odd_entries_derivatives_and_spectra(self):
        saved = json.loads(PARITY.read_text())
        even = json.loads(EVEN.read_text())
        coefficients = saved['odd_matrix_coefficients']
        degree, modes = saved['degree'], saved['modes']
        with ctx.workprec(1024):
            center = box(even['log_support_center'])
            for index, length, cutoff, include in ((0, arb(17).log(), 17, True),
                                                  (16, center, 18, True),
                                                  (31, arb(19).log(), 19, False)):
                if cutoff in (17, 19):
                    _, _, original = certified_matrix(cutoff, modes)
                else:
                    original = [[entry(i, j, length, prime_powers(18), 0)
                                 - entry(i, -j, length, prime_powers(18), 0)
                                 for j in range(1, modes + 1)] for i in range(1, modes + 1)]
                displacement = length - center
                for i in range(modes):
                    for j in range(modes):
                        cells = [box(coefficients[k][i][j]) for k in range(degree + 1)]
                        value = evaluate(cells, displacement) + arb(0, ball(saved['odd_value_remainder_upper'][i][j]))
                        self.assertTrue(value.overlaps(original[i][j]), (cutoff, i, j, 'value'))
                        if cutoff in (17, 19):
                            powers = prime_powers(cutoff)
                            derivative = (entry_derivative(i + 1, j + 1, length, powers, include_endpoint=include)
                                          - entry_derivative(i + 1, -j - 1, length, powers, include_endpoint=include))
                            slope = evaluate([k * cells[k] for k in range(1, degree + 1)], displacement)
                            slope += arb(0, ball(saved['odd_derivative_remainder_upper'][i][j]))
                            self.assertTrue(slope.overlaps(derivative), (cutoff, i, j, 'derivative'))
                values, _ = center_basis(arb_mat(original))
                local = saved['cells'][index]
                error = ball(local['eigenvalue_disk_radius_upper'])
                for value, interval in zip(values, local['candidate_ranges']):
                    self.assertTrue((box(interval) + arb(0, error)).contains(value))

    def test_crossing_and_lower_odd_mode_fail_closed(self):
        with ctx.workprec(1024):
            result = validate_spectrum([arb_mat([[1, 0], [0, 3]]),
                                        arb_mat([[10, 0], [0, -10]])], arb(1) / 5, arb(0), 1)
            self.assertFalse(result['isolated'])
            e = {'uniform_eigenvalue_disk_radius_upper': '0',
                 'uniform_candidate_eigenvalue_ranges': [{'lo': '2', 'hi': '2'}, {'lo': '3', 'hi': '3'}]}
            o = {'isolated': True, 'eigenvalue_disk_radius_upper': '0',
                 'candidate_ranges': [{'lo': '1', 'hi': '1'}]}
            self.assertLess(full_gap(e, o), 0)

    def test_incomplete_cover_and_unprotected_origin_are_rejected(self):
        even, parity = json.loads(EVEN.read_text()), json.loads(PARITY.read_text())
        partial = deepcopy(even)
        partial['cells'].pop()
        with self.assertRaises(ValueError):
            validate_partition(partial)
        parity['cells'].pop()
        with self.assertRaises(ValueError):
            certify(even, parity)
        even['all_origin_strip_transfers_certified'] = False
        with self.assertRaises(ValueError):
            certify(even, json.loads(PARITY.read_text()))

    def test_spatial_cover_replay_and_independent_bernstein_values(self):
        saved = json.loads(SPATIAL.read_text())
        self.assertEqual(spatial_run(EVEN, PARITY), saved)
        self.assertEqual(saved['positive_subcells'], 32)
        self.assertTrue(saved['all_spatial_boundaries_nonzero_from_parity'])
        self.assertGreater(Fraction(saved['uniform_absolute_boundary_lower_from_displacement']), 0)
        with ctx.workprec(1024):
            for index, cutoff in ((0, 17), (31, 19)):
                _, original, _ = certified_matrix(cutoff, 8)
                _, basis = center_basis(arb_mat(original))
                vector = [basis[i, 0] for i in range(9)]
                if vector[0] < 0:
                    vector = [-x for x in vector]
                raw = [sum((a * b for a, b in zip(row, vector)), arb(0))
                       for row in bernstein_functionals(8)]
                local = saved['cells'][index]
                for value, interval in zip(raw, local['exact_unit_ground_bernstein_intervals']):
                    self.assertTrue(box(interval).contains(value))
                self.assertGreater(raw[0].lower(), ball(local['absolute_spatial_boundary_lower_from_displacement']))

    def test_bernstein_normalization_matches_existing_gate(self):
        with ctx.workprec(512):
            for modes in (1, 2, 8):
                vector = [arb(3)] + [arb(1) / (20 * j * j) for j in range(1, modes + 1)]
                boundary = vector[0] + arb(2).sqrt() * sum(vector[1:], arb(0))
                normalized = bernstein_coefficients([x / (arb(2).sqrt() * boundary) for x in vector[1:]])
                raw = [sum((a * b for a, b in zip(row, vector)), arb(0))
                       for row in bernstein_functionals(modes)]
                for actual, expected in zip(raw, normalized):
                    self.assertTrue((actual - boundary * expected).contains(0))

    def test_odd_resolvent_reconstructs_boundary_normalized_ground(self):
        with ctx.workprec(1024):
            for cutoff in (17, 19):
                _, even, odd = certified_matrix(cutoff, 8)
                values, basis = center_basis(arb_mat(even))
                ground = [basis[i, 0] for i in range(9)]
                boundary = ground[0] + arb(2).sqrt() * sum(ground[1:], arb(0))
                self.assertGreater(boundary, 0)
                shifted = arb_mat([[odd[i][j] - (values[0] if i == j else 0)
                                    for j in range(8)] for i in range(8)])
                source = arb_mat([[(j + 1) * even[j + 1][0]] for j in range(8)])
                h = shifted.solve(source)
                divided = [h[j, 0] / (j + 1) for j in range(8)]
                reconstructed = [1 + arb(2).sqrt() * sum(divided, arb(0))] + [-x for x in divided]
                norm = sum((x * x for x in reconstructed), arb(0)).sqrt()
                for actual, expected in zip(reconstructed, ground):
                    self.assertTrue((actual * boundary - expected).contains(0))
                self.assertTrue((1 / norm).overlaps(boundary))
                error = sum(((a / norm - b) * (a / norm - b)
                             for a, b in zip(reconstructed, ground)), arb(0)).abs_upper().sqrt()
                self.assertLess(error, arb('1e-40'))

    def test_exact_displacement_boundary_rigidity(self):
        # A=I+ee^T: a zero-boundary even eigenvector at lambda=1
        # has a nonzero odd partner at that same eigenvalue.
        indices = list(range(-2, 3))
        matrix = [[Fraction(1 + (i == j)) for j in indices] for i in indices]
        b = [Fraction(i) for i in indices]
        c = [Fraction(1), Fraction(-1), Fraction(0), Fraction(-1), Fraction(1)]
        multiply = lambda a, v: [sum(x * y for x, y in zip(row, v)) for row in a]
        dc = [i * x for i, x in zip(indices, c)]
        self.assertEqual(sum(c), 0)
        self.assertEqual(multiply(matrix, c), c)
        self.assertNotEqual(dc, [0] * 5)
        self.assertEqual(multiply(matrix, dc), dc)
        for i, first in enumerate(indices):
            for j, second in enumerate(indices):
                self.assertEqual(matrix[i][j] * (second - first), b[j] - b[i])
        # A=I-ee^T has a simple even ground with nonzero boundary;
        # the general identity G diag(i)c=-b*sum(c) is exact as well.
        matrix = [[Fraction((i == j) - 1) for j in indices] for i in indices]
        c = [Fraction(1, 5)] * 5
        b = [-Fraction(i) for i in indices]
        ground = Fraction(-4)
        g = [[x - (ground if i == j else 0) for j, x in enumerate(row)] for i, row in enumerate(matrix)]
        dc = [i * x for i, x in zip(indices, c)]
        self.assertEqual(multiply(g, dc), [-x * sum(c) for x in b])


if __name__ == '__main__':
    unittest.main()
