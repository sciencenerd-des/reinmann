from fractions import Fraction as F
import unittest

import sympy as sp

from liu_exponent_system import direct_components
from liu_refined_architecture import (Q, STAGES, certificate,
    direct_relaxation_certificate, endpoint_certificate, fixed_point_regression,
    geometry, refined_endpoint)


class RefinedArchitectureTests(unittest.TestCase):
    def test_independent_published_Xu_Sang_polynomials(self):
        # Appendix D of 2610.15291v2: compare every polynomial coefficient.
        expected = (
            (2916000000,
             [1209956550, 2343372300, 1740394800, 794068800],
             [-1135891798, -1173235148, 258347816],
             [266598135, 244982070]),
            (1457125331220000000,
             [604514027207496297, 1171060420363058502,
              869869372328057808, 396910005991680000],
             [-567451842451072679, -586296072701709724, 128972962522474840],
             [133165863887059575, 122393853878983830]),
        )
        for stage, (scale, A, B, C) in zip(STAGES, expected):
            result = endpoint_certificate(stage)
            for name, coeffs in [('A', A), ('B_polynomial', B), ('C', C)]:
                self.assertEqual([F(v)*scale for v in result[name]], coeffs)

    def test_full_high_exponent_independently_reduces_to_endpoint(self):
        b, ell, k, delta, x, z0 = sp.symbols('b ell k delta x z0')
        e = refined_endpoint(b, ell, k, delta, x)
        theta = delta*x/(6*k)
        a = (1+delta)/2
        B = Q(11, 12)-ell/4
        full = (a-B-e['ly']*(Q(1, 2)+theta)+e['h']*(z0-Q(1, 6))
                -ell/2+ell*delta*x
                +e['h']*((3*e['R']+1)/4+theta/2-z0))
        self.assertEqual(sp.cancel(full-e['E']), 0)

    def test_every_stage_uses_previous_boundary(self):
        previous = F(7, 8)
        for stage in STAGES:
            row = endpoint_certificate(stage)
            self.assertEqual(F(row['licensed_by_B']), previous)
            self.assertLess(F(row['B']), previous)
            self.assertGreater(F(row['retained_uniform_margin']), 0)
            previous = F(row['B'])
        self.assertEqual(previous, F(874886647041, 10**12))

    def test_free_direct_floor_does_not_depend_on_high_inputs(self):
        c = direct_relaxation_certificate()
        self.assertEqual(c['floor'], '13/15')
        self.assertIsNone(c['full_idealized_system_exact_optimum'])
        self.assertEqual(sum(map(F, c['dual_weights'])), 1)

    def test_extrapolating_balanced_formula_would_give_false_improvement(self):
        b, ell = F(1, 100), F(1, 4)
        lx, ly, _ = geometry(b, ell)
        naive = F(11, 12)-ell/4
        self.assertLess(naive, F(13, 15))
        actual = direct_components(lx, ly, ell)['B_low']
        self.assertEqual(actual, naive+(5*ell-1)/8)
        self.assertGreater(actual, F(13, 15))

    def test_fixed_point_is_derived_with_relevant_critical_class(self):
        r = fixed_point_regression()
        lo, hi = map(F, r['B_interval'])
        self.assertLess(hi-lo, F(1, 10**55))
        self.assertLess(lo, F('0.874886647039964131'))
        self.assertGreater(hi, F('0.874886647039964130'))
        self.assertTrue(all(F(v) > 0 for v in r['critical_delta_positive_bounds']))
        self.assertEqual(r['quartic_roots_in_broad_kappa_range'], 2)
        self.assertFalse(r['external_optimality_and_tangent_family_reproved'])

    def test_claim_scope_is_explicit(self):
        c = certificate()
        self.assertFalse(c['RH_claim'])
        self.assertFalse(c['analytic_estimate_proved'])
        self.assertFalse(c['novelty_claim'])


if __name__ == '__main__':
    unittest.main()
