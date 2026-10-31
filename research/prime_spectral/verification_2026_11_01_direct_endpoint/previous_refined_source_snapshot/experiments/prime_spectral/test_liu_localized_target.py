from fractions import Fraction as F
import unittest

import sympy as sp

from liu_conditional_moment import ALPHA, B_GAP, BOUNDARY, ELL, KAPPA
from liu_exponent_system import count_closed, nonprincipal
from liu_localized_target import (COUNT_GAIN, DELTA_BOX, R_BAND, X_BOX,
    bernstein_rectangle, certificate, direct_count_certificate, hybrid_detector_count)


class LocalizedTargetTests(unittest.TestCase):
    def test_tensor_certificate_has_correct_bounds_and_rejects_a_bad_rectangle(self):
        d, x = sp.symbols('d x')
        result = bernstein_rectangle(1+d-x, (d, x), ((F(1), F(2)), (F(0), F(1, 2))))
        self.assertEqual(result['lower_bound'], F(3, 2))
        with self.assertRaises(ArithmeticError):
            bernstein_rectangle(1-10*d, (d, x), ((F(0), F(1)), (F(0), F(1))))

    def test_uniform_localization_retains_positive_savings(self):
        result = certificate()
        self.assertEqual(result['B'], BOUNDARY)
        self.assertGreater(result['outside_box_uses_original_count']['minimum_saving'], F(5, 10**6))
        self.assertGreater(result['localized_moment_total_endpoint_saving'], F(7, 10**7))
        self.assertEqual(result['unchanged_auxiliary_reserve_count'], 30)
        self.assertFalse(result['arithmetic_estimate_proved'])
        self.assertFalse(result['DH_family_instantiated'])

    def test_band_only_moment_matches_independent_affine_supremum(self):
        # This optimizer actually uses the OLD moment on 1<=r<1.099.
        # It is independent of the polynomial localization certificate.
        for delta in (DELTA_BOX[0], F(2, 5), DELTA_BOX[1]):
            for x in (X_BOX[0], F(23, 50), X_BOX[1]):
                count = count_closed(delta, x, KAPPA, ALPHA)
                self.assertLess(R_BAND[0], count['t'])
                self.assertLess(count['t'], R_BAND[1])
                self.assertEqual(hybrid_detector_count(count['t'], delta, x), count['R'])

    def test_old_count_really_fails_inside_the_enclosure(self):
        delta, x = F(2, 5), F(1, 2)
        lx, ly = (1-B_GAP-ELL)/2, (1+B_GAP-ELL)/2
        h = 1-lx+ELL
        old = count_closed(delta, x, KAPPA)
        self.assertGreater(nonprincipal(lx, ly, ELL, BOUNDARY, delta, x, h, old['R']), 0)
        self.assertGreater(nonprincipal(lx, ly, ELL, BOUNDARY, delta, x, h, old['R']-F(1, 1000)), 0)
        self.assertLess(nonprincipal(lx, ly, ELL, BOUNDARY, delta, x, h, old['R']-COUNT_GAIN), 0)

    def test_lower_length_edge_cannot_be_rounded_up_carelessly(self):
        delta, x = DELTA_BOX[0], X_BOX[1]
        new = count_closed(delta, x, KAPPA, ALPHA)
        old_at = lambda r: F(1, 6)+(F(5, 6)-delta)*r
        self.assertLess(old_at(R_BAND[0]), new['R'])
        self.assertGreater(old_at(F(11, 10)), new['R'])

    def test_weaker_direct_count_gain_is_not_automatically_sufficient(self):
        self.assertGreater(direct_count_certificate()['uniform_endpoint_saving'], 0)
        with self.assertRaises(ArithmeticError):
            direct_count_certificate(gain=F(1, 1000))
        with self.assertRaises(ValueError):
            direct_count_certificate(gain=F(0))

    def test_hybrid_optimizer_rejects_unproved_parameter_extrapolation(self):
        with self.assertRaises(ValueError):
            hybrid_detector_count(F(6, 5), F(2, 5), F(1, 2))
        with self.assertRaises(ValueError):
            hybrid_detector_count(F(9, 8), F(1, 4), F(1, 2))


if __name__ == '__main__':
    unittest.main()
