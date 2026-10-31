import unittest

import sympy as sp

from liu_closure_interface import (certificate, local_correction_certificate,
                                 remainder_certificate, shifted_zero_certificate)


class ClosureInterfaceTests(unittest.TestCase):
    def test_supplied_remainder_saving_is_relative_not_absolute(self):
        beta, B = sp.Rational(7, 8), sp.Rational(8748867, 10**7)
        largest_constructed_rho = (beta-B)/50
        self.assertGreater(beta-sp.Rational(1, 2)-largest_constructed_rho,
                           B-sp.Rational(1, 2))
        self.assertFalse(remainder_certificate()['actual_remainder_decay_disproved'])
        self.assertEqual(sp.Rational(87, 100)-sp.Rational(1, 2)-sp.Rational(1, 600),
                         sp.Rational(221, 600))

    def test_independent_principal_table_values(self):
        # A genuinely complex phase prevents silently substituting psi=1.
        q, T, eta, psi = sp.Integer(13), sp.Rational(1, 4), sp.I, -sp.I
        R, Y, V = psi*q**3*T**6, 1/q, 1/q
        Pstar = ((R*(1-1/q)-eta*(q-1)*T*Y*V)/(1-V)-eta*T+Y*R)/(1-R)
        H = (1-V)*(1-Y)*(1/(1-V)+Y/(1-Y)+Pstar)/(1-eta*T)
        E = 1+(eta*T/q-psi*q**2*T**6)/(1-eta*T)
        self.assertEqual(sp.cancel(H-(1-q**-2)*E/(1-R)), 0)
        wrong_R = q**3*T**6
        self.assertNotEqual(sp.cancel(H-(1-q**-2)*E/(1-wrong_R)), 0)

    def test_regular_factor_bound_and_angular_character_retained(self):
        c = local_correction_certificate()
        self.assertEqual(c['E_local_uniform_defect_bound_for_q_at_least_9'], '2/9')
        self.assertIn('conjugate(alpha)^6', c['angular_character'])
        self.assertFalse(c['analytic_theory_proved_by_code'])

    def test_angular_critical_line_maps_to_seven_twelfths(self):
        c = shifted_zero_certificate()
        self.assertEqual(c['mapped_critical_line'], '7/12')
        self.assertFalse(c['target_L_zero_or_common_zero_located'])
        self.assertFalse(c['numerical_angular_zero_scan_performed'])

    def test_no_automatic_GRH_or_DH_strategy(self):
        c = certificate()
        self.assertFalse(c['direct_probe_GRH_implication_proved'])
        self.assertFalse(c['DH_metaplectic_probe_instantiated'])
        self.assertFalse(c['whole_method_family_closed'])


if __name__ == '__main__':
    unittest.main()
