"""Whole-cell budget replay, independent derivatives and exact normalization."""
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import unittest

from flint import acb, acb_series, arb, arb_mat, arb_poly, ctx

from certified_weil import certified_matrix
from eigenvalue_response import _fourier_functional
from smooth_support_profile import _fourier_length_derivative
from weil_eigenfamily import ball, box, center_basis
from weil_profile_cell_budget import (candidate_derivative_bound, certify,
                                     density_derivative_polynomials, physical_candidate, run)
from weil_profile_cell_budget import profile_transfer_bound
from weil_support_taylor import _cos, evaluate

RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'
EVEN = RESEARCH / 'weil_eigenfamily_17_19_8_degree64.json'
BUDGET = RESEARCH / 'weil_profile_cell_budget_17_19_8_degree64.json'
WIDE_BUDGET = RESEARCH / 'weil_profile_cell_budget_17_19_8_degree64_strip1.json'


class WeilProfileCellBudgetTests(unittest.TestCase):
    def test_complete_budget_replays_with_material_cancellation_gain(self):
        saved = json.loads(BUDGET.read_text())
        self.assertEqual(run(EVEN), saved)
        with ctx.workprec(256):
            total = ball(saved['any_two_supports_exact_ground_strip_increment_upper'])
            naive = ball(saved['termwise_integrated_candidate_strip_budget_upper'])
            self.assertLess(total, arb('0.086'))
            self.assertGreater(naive, 5 * total)
            self.assertLess(ball(saved['total_exact_ground_transfer_allowance_upper']), arb('1e-17'))
        self.assertEqual(len(saved['cells']), 32)

    def test_wide_strip_budget_replays_and_zero_height_transfer_is_regular(self):
        saved = json.loads(WIDE_BUDGET.read_text())
        self.assertEqual(run(EVEN, sigma=Fraction(1)), saved)
        self.assertEqual(saved['strip_height'], '1')
        with ctx.workprec(512):
            self.assertLess(ball(saved['any_two_supports_exact_ground_strip_increment_upper']), arb('0.204'))
            cell = json.loads(EVEN.read_text())['cells'][0]
            self.assertGreater(profile_transfer_bound(cell, arb(0), arb(19).log()), 0)
            self.assertLess(profile_transfer_bound(cell, arb(0), arb(19).log()),
                            profile_transfer_bound(cell, arb(1), arb(19).log()))

    def test_constant_mode_derivative_includes_both_spatial_endpoints(self):
        with ctx.workprec(512):
            result = candidate_derivative_bound([arb_poly([1])], arb(3), arb(1) / 100, arb(2) / 5, 16)
            minimum = arb(3) - arb(1) / 100
            for key in ('spatial_density_derivative_L1_upper', 'spatial_endpoint_flux_upper'):
                upper = ball(result[key])
                self.assertGreaterEqual(upper, (1 / minimum).lower())
                self.assertLess(abs(upper - 1 / minimum).upper(), arb('1e-9'))
            bound = ball(result['uniform_candidate_strip_derivative_upper'])
            for length in (arb('2.99'), arb(3), arb('3.01')):
                for z in (acb(4), acb(1000000, arb(2) / 5), acb(0, arb(2) / 5)):
                    derivative = ((z * length / 2).cos() - (z * length / 2).sinc()) / length
                    self.assertLess(abs(derivative).upper(), bound)

    def test_common_candidate_scale_cancels_before_range_evaluation(self):
        with ctx.workprec(512):
            scale = arb_poly([1, 100])
            physical = [scale, 2 * scale, -3 * scale]
            length = arb_poly([3, 1])
            constant, cosines, sines = density_derivative_polynomials(physical, length)
            self.assertTrue(all(x.contains(0) for x in (constant + scale * scale).coeffs()))
            for coefficient, cosine in zip(physical[1:], cosines):
                residual = cosine + arb(2).sqrt() * coefficient * scale
                self.assertTrue(all(x.contains(0) for x in residual.coeffs()))
                self.assertLess(max((abs(x).upper() for x in residual.coeffs()), default=arb(0)), arb('1e-140'))
            self.assertEqual(len(sines), 2)

    def test_candidate_density_derivative_against_independent_analytic_series(self):
        saved = json.loads(EVEN.read_text())
        with ctx.workprec(1024):
            previous_cap = ctx.cap
            try:
                ctx.cap = 3
                for index in (0, 16, 31):
                    cell = saved['cells'][index]
                    physical = physical_candidate(cell)
                    length = box(saved['log_support_center']) + ball(cell['center_offset'])
                    constant, cosines, sines = density_derivative_polynomials(physical, arb_poly([length, 1]))
                    parameter = acb_series([0, 1], prec=3)
                    length_series = acb_series([length, 1], prec=3)
                    coeffs = []
                    for poly in physical:
                        series = acb_series([], prec=3)
                        for coefficient in reversed(poly.coeffs()):
                            series = series * parameter + coefficient
                        coeffs.append(series)
                    for scaled in (Fraction(0), Fraction(1, 5), Fraction(1, 2)):
                        location = ball(scaled) * length
                        numerator = coeffs[0]
                        for j, coefficient in enumerate(coeffs[1:], 1):
                            angle = 2 * arb.pi() * j * (location * length_series.inv() + arb(1) / 2)
                            numerator += arb(2).sqrt() * coefficient * _cos(angle)
                        density = numerator * (length_series * coeffs[0]).inv()
                        analytic = constant[0]
                        for j, (cosine, sine) in enumerate(zip(cosines, sines), 1):
                            angle = 2 * arb.pi() * j * (ball(scaled) + arb(1) / 2)
                            analytic += cosine[0] * angle.cos() + ball(scaled) * sine[0] * angle.sin()
                        analytic /= length * length * physical[0][0] * physical[0][0]
                        self.assertTrue(density[1].real.overlaps(analytic))
                        self.assertLess(abs(density[1] - analytic).upper(), arb('1e-80'))
            finally:
                ctx.cap = previous_cap

    def test_original_endpoint_profile_increments_and_candidate_derivatives(self):
        even, budget = json.loads(EVEN.read_text()), json.loads(BUDGET.read_text())
        wide_budget = json.loads(WIDE_BUDGET.read_text())
        with ctx.workprec(1024):
            profiles = []
            arguments = (acb(4), acb(8), acb(0, arb(2) / 5), acb(0, 1))
            for index, cutoff in ((0, 17), (31, 19)):
                length = arb(cutoff).log()
                _, matrix, _ = certified_matrix(cutoff, 8)
                _, basis = center_basis(arb_mat(matrix))
                vector = [basis[i, 0] / basis[0, 0] for i in range(9)]
                profiles.append([sum((a * b for a, b in zip(_fourier_functional(8, length, z), vector)), arb(0))
                                 for z in arguments])
                local = even['cells'][index]
                physical = physical_candidate(local)
                displacement = length - box(even['log_support_center']) - ball(local['center_offset'])
                values = [evaluate(poly.coeffs(), displacement) for poly in physical]
                primes = [evaluate(poly.derivative().coeffs(), displacement) for poly in physical]
                normalized = [x / values[0] for x in values]
                response = [(p * values[0] - x * primes[0]) / (values[0] * values[0])
                            for x, p in zip(values, primes)]
                bound = ball(budget['cells'][index]['uniform_candidate_strip_derivative_upper'])
                for argument_index, z in enumerate(arguments):
                    functional = _fourier_functional(8, length, z)
                    drift = _fourier_length_derivative(8, length, z)
                    derivative = sum((a * b + c * d for a, b, c, d in zip(drift, normalized, functional, response)), arb(0))
                    applicable_bound = bound if argument_index < 3 else ball(wide_budget['cells'][index]['uniform_candidate_strip_derivative_upper'])
                    self.assertLess(abs(derivative).upper(), applicable_bound)
            for argument_index, (old, new) in enumerate(zip(*profiles)):
                applicable_budget = budget if argument_index < 3 else wide_budget
                self.assertLess(abs(new - old).upper(), ball(applicable_budget['any_two_supports_exact_ground_strip_increment_upper']))

    def test_odd_origin_normalization_is_exactly_the_even_schur_block(self):
        with ctx.workprec(1024):
            for cutoff in (17, 19):
                _, even, odd = certified_matrix(cutoff, 8)
                values, basis = center_basis(arb_mat(even))
                for i in range(8):
                    for j in range(8):
                        expected = odd[i][j] * (j + 1) / (i + 1) + arb(2).sqrt() * even[i + 1][0]
                        residual = expected - even[i + 1][j + 1]
                        self.assertTrue(residual.contains(0))
                        self.assertLess(abs(residual).upper(), arb('1e-65'))
                shifted_odd = arb_mat([[odd[i][j] - (values[0] if i == j else 0) for j in range(8)] for i in range(8)])
                shifted_even = arb_mat([[even[i + 1][j + 1] - (values[0] if i == j else 0) for j in range(8)] for i in range(8)])
                ratio = shifted_odd.det() / shifted_even.det()
                direct = (basis[0, 0] + arb(2).sqrt() * sum((basis[j, 0] for j in range(1, 9)), arb(0))) / basis[0, 0]
                self.assertGreater(ratio, 0)
                self.assertTrue(ratio.overlaps(direct))
                self.assertLess(abs(ratio - direct).upper(), arb('1e-40'))

    def test_invalid_cover_origin_and_spatial_settings_fail_closed(self):
        even = json.loads(EVEN.read_text())
        partial = deepcopy(even)
        partial['cells'].pop()
        with self.assertRaises(ValueError):
            certify(partial)
        with self.assertRaises(ValueError):
            certify(even, sigma=Fraction(-1))
        with ctx.workprec(256):
            with self.assertRaises(ArithmeticError):
                candidate_derivative_bound([arb_poly([0, 1])], arb(3), arb(1) / 10, arb(0), 16)
            with self.assertRaises(ValueError):
                candidate_derivative_bound([arb_poly([1])], arb(3), arb(1) / 10, arb(0), 0)


if __name__ == '__main__':
    unittest.main()
