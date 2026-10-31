from fractions import Fraction as F
import unittest

from liu_exponent_system import count_closed
from liu_refined_localized import (ALPHA, B_TARGET, DELTA_BOX, KAPPA,
    R_BAND, X_BOX, certificate, hybrid_detector)


class RefinedLocalizedTests(unittest.TestCase):
    def test_affine_detector_is_bounded_by_capped_band_envelope(self):
        for delta in [*DELTA_BOX, F(47, 100), F(1, 2)]:
            for x in [*X_BOX, F(9, 20)]:
                full = count_closed(delta, x, KAPPA, ALPHA)
                t = min(full['t'], R_BAND[1])
                c = F(2, 3)/KAPPA
                D, P = 3-(1+c)*x, (2-c*x)*(1-x)
                old_left = 1-F(5, 6)+(F(5, 6)-delta)*R_BAND[0]
                capped_short = 1-delta+delta*P*(F(3, 2)-R_BAND[1])/D
                bound = max(full['R'], old_left, capped_short)
                self.assertLessEqual(hybrid_detector(t, delta, x), bound)

    def test_cap_is_actually_needed(self):
        t = count_closed(F(51, 100), F(1, 2), KAPPA, ALPHA)['t']
        self.assertGreater(t, R_BAND[1])
        with self.assertRaises(ValueError):
            hybrid_detector(t, F(51, 100), F(1, 2))

    def test_certificate_scope_and_nonoptimal_boundary(self):
        c = certificate()
        self.assertEqual(F(c['conditional_B']), B_TARGET)
        self.assertTrue(c['improves_B_flat'])
        self.assertFalse(c['improves_older_conditional_B_0_874793'])
        self.assertFalse(c['arithmetic_moment_proved'])
        self.assertFalse(c['DH_family_instantiated'])
        self.assertGreater(F(c['retained_margin']), 0)
        self.assertTrue(all(F(v) > 0 for v in c['strict_auxiliary_reserves'].values()))


if __name__ == '__main__':
    unittest.main()
