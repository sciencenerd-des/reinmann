from fractions import Fraction as F
import unittest

from liu_exponent_system import (ALPHA, MomentInputs, boundary, bootstrap_intervals,
    count_closed, detector_count_at_t, direct_components, geometry,
    isolate_decreasing_root, nonprincipal, ordinary_gm_template, raw_polynomial,
    symbolic_certificates)


class LiuExponentSystemTests(unittest.TestCase):
    def test_original_lengths_and_normalization(self):
        ell, b = F(1, 6), F(1, 8)
        lx, ly = (1-b-ell)/2, (1+b-ell)/2
        self.assertEqual((lx, ly), (F(17, 48), F(23, 48)))
        self.assertEqual(boundary(ell), F(7, 8))
        self.assertEqual(direct_components(lx, ly, ell)['B_low'], F(7, 8))
        principal = F(7, 8)-F(5, 6)+lx/3+ell/6
        self.assertEqual(principal, lx/2+b/12)

    def test_naive_balanced_boundary_must_keep_reflection_loss(self):
        ell, b = F(1, 4), F(1, 100)
        lx, ly = (1-b-ell)/2, (1+b-ell)/2
        value = direct_components(lx, ly, ell)['B_low']
        self.assertEqual(value, boundary(ell)+(5*ell-1)/8)
        self.assertGreater(value, boundary(ell))

    def test_count_free_direct_primal_and_global_lower_bound(self):
        self.assertEqual(direct_components(F(7, 20), F(9, 20), F(1, 5))['B_low'], F(13, 15))
        for lx in (F(1, 10), F(2, 5), F(4, 5)):
            for ly in (F(3, 20), F(1, 2), F(6, 5)):
                for ell in (F(1, 20), F(1, 5), F(2, 5)):
                    self.assertGreaterEqual(direct_components(lx, ly, ell)['B_low'], F(13, 15))

    def test_relative_nonprincipal_exponent_and_contour_cancellation(self):
        ell, b, delta, x, R = F(1, 6), F(1, 8), F(2, 5), F(1, 3), F(2, 3)
        lx, ly = (1-b-ell)/2, (1+b-ell)/2
        h = 1-lx+ell
        expected = -F(1, 4)+b/6+5*ell/4+(F(1, 2)+ell)*delta+ell*x*delta-h*(1-R)
        for z0 in (F(17, 50), F(1, 3), F(2, 5)):
            self.assertEqual(nonprincipal(lx, ly, ell, boundary(ell), delta, x, h, R, z0), expected)

    def test_closed_count_matches_independent_affine_minimax(self):
        # The minimax optimizer does not call the closed formula.
        for delta, x in ((F(1, 5), F(1, 4)), (F(2, 5), F(1, 2)), (F(3, 4), F(0))):
            kappa = F(3, 4)
            closed = count_closed(delta, x, kappa)
            answer = detector_count_at_t(closed['t'], delta, x)
            self.assertEqual(answer['R'], closed['R'])

    def test_supplied_count_is_not_an_actual_count_lower_bound(self):
        delta, x, kappa = F(2, 5), F(1, 2), F(3, 4)
        closed = count_closed(delta, x, kappa)
        restricted = detector_count_at_t(closed['t'], delta, x, prime_support=F(0))
        self.assertGreaterEqual(restricted['R'], closed['R'])
        improved = detector_count_at_t(closed['t'], delta, x,
            MomentInputs(alpha=F(3, 4), inverse_prime_cost=F(3, 2)))
        self.assertLessEqual(improved['R'], closed['R'])

    def test_reject_invalid_formal_extrapolations(self):
        with self.assertRaises(ValueError):
            count_closed(F(4, 5), F(1, 2), F(3, 4), alpha=F(3, 4))
        with self.assertRaises(ValueError):
            detector_count_at_t(F(2), F(2, 5), F(1, 2))
        with self.assertRaises(ValueError):
            MomentInputs(plain_prime_cost=F(0))
        with self.assertRaises(ValueError):
            detector_count_at_t(F(1), F(2, 5), F(1, 2),
                                MomentInputs(plain_prime_cost=F(1, 10)))

    def test_cubic_root_bracket_and_reported_value(self):
        lo, hi = isolate_decreasing_root([1188, -2160, 171, 190])
        p = lambda x: 1188*x**3-2160*x**2+171*x+190
        self.assertGreater(p(lo), 0)
        self.assertLess(p(hi), 0)
        self.assertLess(hi-lo, F(1, 10**50))
        B = geometry((lo+hi)/2)['B']
        self.assertTrue(F('0.87495701942009894612860385056145297') < B <
                        F('0.87495701942009894612860385056145300'))

    def test_bootstrap_uses_previous_bound(self):
        rows = bootstrap_intervals(4)
        previous = [F(7, 8), F(7, 8)]
        for row in rows:
            kappa = list(map(F, row['moment_kappa_interval_from_previous_bound']))
            current = list(map(F, row['new_B_interval']))
            self.assertEqual(kappa, [2*previous[0]-1, 2*previous[1]-1])
            self.assertLess(current[1], previous[0])
            previous = current

    def test_raw_amplitudes_not_L2_normalized_values(self):
        delta, r, z = F(2, 5), F(7, 10), F(3, 20)
        for copies in (1, 2):
            raw = raw_polynomial(delta, F(1, 2), r, z, copies)
            self.assertEqual(raw['sigma'], (1+delta)/2)
            self.assertEqual(raw['N_exponent'], copies*r+z)
        raw = raw_polynomial(delta, F(0), r, z)
        self.assertLess(raw['sigma'], (1+delta)/2)
        with self.assertRaises(ValueError):
            raw_polynomial(delta, F(1, 2), F(0))

    def test_GM_template_normalization_matches_standard_critical_case(self):
        # N=T^(4/5), V=N^(3/4) gives R=T^(13/25), GM section 1.
        self.assertEqual(ordinary_gm_template(F(4, 5), F(3, 5)), F(13, 25))

    def test_uniform_endpoint_and_LP_certificates(self):
        result = symbolic_certificates()
        self.assertTrue(result['original_seven_eighths_uniform_central_endpoint_verified'])
        self.assertEqual(result['direct_floor'], '13/15')
        self.assertTrue(all(F(v) > 0 for v in result['endpoint_and_reserve_positive_Bernstein_bounds'].values()))


if __name__ == '__main__':
    unittest.main()
