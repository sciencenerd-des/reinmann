"""Full-cell Taylor replay and independent boundary value/derivative checks."""
from fractions import Fraction
import json
from pathlib import Path
import unittest

from flint import acb, acb_series, arb, ctx

from certified_weil import certified_matrix
from smooth_support_derivative import even_derivative_matrix
from weil_support_taylor import _cos, _psi_enclosed, _sin, evaluate, run


RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


def ball(value):
    number = Fraction(value)
    return arb(number.numerator) / number.denominator


def box(value):
    return ball(value['lo']).union(ball(value['hi']))


class WeilSupportTaylorTests(unittest.TestCase):
    def test_series_trigonometric_coefficients_retain_requested_precision(self):
        with ctx.workprec(512):
            previous_cap = ctx.cap
            try:
                ctx.cap = 8
                for value in (acb(1), acb(49)):
                    series = acb_series([value, 1], prec=8)
                    sine, cosine = _sin(series), _cos(series)
                    self.assertTrue(sine[0].overlaps(value.sin()))
                    self.assertTrue(cosine[0].overlaps(value.cos()))
                    self.assertTrue(sine[1].overlaps(value.cos()))
                    self.assertTrue(cosine[1].overlaps(-value.sin()))
                    for coefficient in (sine[0], sine[1], cosine[0], cosine[1]):
                        self.assertGreater(coefficient.real.rel_accuracy_bits(), 480)
            finally:
                ctx.cap = previous_cap

    def test_saved_whole_cell_replays(self):
        saved = json.loads((RESEARCH / 'weil_support_taylor_17_19_8.json').read_text())
        self.assertEqual(run(), saved)
        self.assertEqual((saved['lower_prime_power'], saved['upper_prime_power']), (17, 19))

    def test_all_even_entries_and_one_sided_derivatives_at_both_boundaries(self):
        saved = json.loads((RESEARCH / 'weil_support_taylor_17_19_8.json').read_text())
        with ctx.workprec(1024):
            center = box(saved['log_support_center'])
            coefficients = saved['even_matrix_coefficients']
            degree, modes = saved['degree'], saved['modes']
            for matrix in coefficients:
                for row in matrix:
                    for cell in row:
                        self.assertLess(box(cell).rad(), arb('1e-140'))
            for cutoff, include_endpoint in ((17, True), (19, False)):
                _, original, _ = certified_matrix(cutoff, modes)
                derivative = even_derivative_matrix(cutoff, modes, include_endpoint=include_endpoint)
                displacement = arb(cutoff).log() - center
                for i in range(modes + 1):
                    for j in range(modes + 1):
                        cells = [box(coefficients[k][i][j]) for k in range(degree + 1)]
                        value = evaluate(cells, displacement) + arb(0, ball(saved['even_value_remainder_upper'][i][j]))
                        slope = evaluate([k * cells[k] for k in range(1, degree + 1)], displacement)
                        slope += arb(0, ball(saved['even_derivative_remainder_upper'][i][j]))
                        self.assertTrue(value.overlaps(original[i][j]), (cutoff, i, j, 'value'))
                        self.assertTrue(slope.overlaps(derivative[i][j]), (cutoff, i, j, 'derivative'))

    def test_mean_value_digamma_enclosure_contains_complex_point_values(self):
        with ctx.workprec(512):
            rectangle = acb(arb('0.25', '0.1'), arb('-8', '0.1'))
            enclosed = _psi_enclosed(rectangle, 0)
            for real in ('0.15', '0.25', '0.35'):
                for imag in ('-8.1', '-8', '-7.9'):
                    self.assertTrue(enclosed.contains(acb(real, imag).digamma()))


if __name__ == '__main__':
    unittest.main()
