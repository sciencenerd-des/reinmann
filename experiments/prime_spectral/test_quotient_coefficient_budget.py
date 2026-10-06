import json
from pathlib import Path
import unittest
from flint import arb, acb, ctx
from grid_tail import quotient_polynomial_profile
from quotient_operator import build
from quotient_coefficient_budget import coefficient_budget, compare


class QuotientCoefficientBudgetTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512
        self.B = [[arb(v) if i == j else arb(0) for j in range(4)]
                  for i, v in enumerate((-2, 2, -3, 3))]

    def test_exact_diagonal_coefficients(self):
        result = coefficient_budget(self.B, 2, 1)
        expected = [arb(1), -arb(13)/36, arb(1)/36]
        self.assertTrue(result['spectral_sum'].contains(arb(13)/36))
        for a, b in zip(result['even_coefficients'], expected):
            self.assertTrue((a-b).contains(0))
        self.assertTrue(result['disk_tail_upper'].is_zero())

    def test_tail_encloses_omitted_terms(self):
        result = coefficient_budget(self.B, 1, 2)
        for z in (acb(0, 2), acb('1.2', '0.7')):
            value = quotient_polynomial_profile(self.B, z)
            truncated = sum((a*z**(2*k) for k, a in enumerate(result['even_coefficients'])), acb(0))
            self.assertLess(abs(value-truncated), result['disk_tail_upper'])
            self.assertLess(abs(value), result['disk_modulus_upper'])

    def test_actual_prime_comparison(self):
        root = Path(__file__).resolve().parents[2]
        certificates = [json.loads((root/f'research/prime_spectral/certified_weil_13_{n}.json').read_text()) for n in (4, 8)]
        result = compare(*certificates)
        upper = arb(result['profile_difference_upper'])
        self.assertLess(upper, arb('0.004'))
        matrices = [build(c)[2] for c in certificates]
        # Interior points leave clearance for the wider direct determinant
        # intervals; the full disk bound is justified by the coefficient proof.
        for z in (acb('0.5', '0.5'), acb(0, '0.75')):
            difference = quotient_polynomial_profile(matrices[0], z)-quotient_polynomial_profile(matrices[1], z)
            self.assertLess(abs(difference), upper)

    def test_invalid_domains(self):
        for order, radius in ((0, 1), (3, 1), (1, -1)):
            with self.assertRaises(ValueError):
                coefficient_budget(self.B, order, radius)
        with self.assertRaises(ValueError):
            coefficient_budget([[1]], 1, 1)


if __name__ == '__main__':
    unittest.main()
