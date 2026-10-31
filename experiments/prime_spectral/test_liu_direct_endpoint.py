from fractions import Fraction as F
import unittest

import sympy as sp

from liu_direct_endpoint import (balanced_price, certificate,
    combination_obstruction, dh_reciprocal_coefficients, pricing_certificate)
from verify_row_density_extraction import dh_inverse


class DirectEndpointTests(unittest.TestCase):
    def test_primal_probe_needs_negative_exponent(self):
        p = balanced_price(F(1, 5), F(1, 10))
        self.assertEqual(F(p['required_probe_exponent']), -F(11, 60))
        self.assertEqual(F(p['current_direct_exponent']), F(11, 60))
        self.assertEqual(F(p['necessary_saving']), F(11, 30))
        self.assertTrue(p['support_lengths'])

    def test_formal_length_solution_is_outside_support(self):
        p = pricing_certificate()
        self.assertEqual(p['formal_length_for_half'], '5/3')
        self.assertFalse(p['formal_half_price']['positive_lengths'])
        self.assertFalse(p['formal_half_price']['support_lengths'])
        self.assertFalse(p['removing_reflection_or_Gram_penalty_alone_sufficient'])

    def test_all_direct_costs_included_in_saving(self):
        # Past the old cap the naive balanced formula understates the cost.
        p = balanced_price(F(1, 4), F(1, 100))
        naive = F(5, 12)-F(1, 4)/4
        self.assertEqual(F(p['necessary_saving']), naive+F(1, 32))

    def test_DH_inverse_agrees_with_separate_existing_implementation(self):
        _, beta = dh_reciprocal_coefficients()
        old = dh_inverse()
        k = sp.Symbol('k')
        for name, n in [('b7', 7), ('b13', 13), ('b91', 91)]:
            self.assertEqual(beta[n], sum(v*k**i for i, v in enumerate(old[name])))
        self.assertEqual(beta[4], 1+k*k)
        self.assertNotEqual(beta[4], sp.mobius(4))

    def test_DH_inverse_rejects_invalid_count(self):
        for n in [0, -1, True, 3.5]:
            with self.assertRaises(ValueError):
                dh_reciprocal_coefficients(n)

    def test_linear_combination_does_not_transfer_reciprocal(self):
        result = combination_obstruction()
        self.assertFalse(result['arithmetic_separator_proved'])

    def test_no_actual_probe_or_whole_method_claim(self):
        c = certificate()
        self.assertFalse(c['whole_method_family_closed'])
        self.assertFalse(c['new_arithmetic_estimate_proved'])
        self.assertFalse(c['DH_principal_model']['actual_probe_GRH_equivalence_proved'])
        self.assertFalse(c['DH_principal_model']['actual_DH_metaplectic_probe_instantiated'])


if __name__ == '__main__':
    unittest.main()
