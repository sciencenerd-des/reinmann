from fractions import Fraction as F
import unittest

from liu_conditional_moment import (ALPHA, B_GAP, BOUNDARY, ELL, KAPPA,
    certificate, critical_class, endpoint_polynomials)
from liu_exponent_system import (MomentInputs, count_closed, detector_count_at_t,
    geometry, isolate_decreasing_root, nonprincipal)


class ConditionalMomentTests(unittest.TestCase):
    def test_certificate_and_prior_antecedent(self):
        result = certificate()
        self.assertEqual(result['parameters']['B'], BOUNDARY)
        self.assertEqual((1+KAPPA)/2, F(7, 8))
        self.assertGreater((1+KAPPA)/2, BOUNDARY)
        self.assertGreater(result['uniform_endpoint_saving_lower_bound'], F(1, 10**7))
        self.assertFalse(result['arithmetic_estimate_proved'])
        self.assertFalse(result['hypothetical_long_inverse_moment']['DH_family_instantiated'])

    def test_rational_bound_strictly_below_published_algebraic_root(self):
        lo, hi = isolate_decreasing_root([1188, -2160, 171, 190])
        self.assertLess(BOUNDARY, geometry(lo)['B'])
        self.assertLess(geometry(hi)['B'], F(7, 8))

    def test_original_moment_cannot_certify_the_new_bound(self):
        # Negative control: the smaller B cannot be obtained simply by
        # changing the old parameters while retaining the old long moment.
        polys = endpoint_polynomials(alpha=F(5, 6))
        self.assertLess(polys['discriminant_complement'][0], 0)
        with self.assertRaises(ArithmeticError):
            certificate(alpha=F(5, 6))
        delta, x = F(3874135, 10**7), F(1, 2)
        lx, ly = (1-B_GAP-ELL)/2, (1+B_GAP-ELL)/2
        h = 1-lx+ELL
        old_R = count_closed(delta, x, KAPPA)['R']
        new_R = count_closed(delta, x, KAPPA, ALPHA)['R']
        self.assertGreater(nonprincipal(lx, ly, ELL, BOUNDARY, delta, x, h, old_R), 0)
        self.assertLess(nonprincipal(lx, ly, ELL, BOUNDARY, delta, x, h, new_R), 0)

    def test_changed_long_moment_matches_independent_affine_optimizer(self):
        # Exact minimax over detector lengths, independently of closed count.
        inputs = MomentInputs(alpha=ALPHA)
        for delta in (F(1, 50), F(2, 5), F(3, 4), F(19, 25)):
            for x in (F(0), F(1, 4), F(1, 2)):
                closed = count_closed(delta, x, KAPPA, ALPHA)
                answer = detector_count_at_t(closed['t'], delta, x, inputs)
                self.assertEqual(answer['R'], closed['R'])

    def test_reject_lost_principal_or_support_range(self):
        with self.assertRaises(ArithmeticError):
            certificate(ell=F(1, 5))
        with self.assertRaises(ValueError):
            certificate(alpha=F(3, 4))
        with self.assertRaises(ValueError):
            certificate(kappa=2*BOUNDARY-1)  # A new bound cannot justify itself.

    def test_long_moment_gain_is_uniform_in_the_declared_range(self):
        for r in (F(1), F(5, 4), F(3, 2)):
            old, new = (1+5*r)/6, F(1, 5)+F(4, 5)*r
            self.assertEqual(old-new, (r-1)/30)
            self.assertGreaterEqual(old-new, 0)

    def test_algebraic_tangency_is_below_strict_rational_certificate(self):
        diag = critical_class()
        self.assertLess(F(diag['B_tangency_display']), BOUNDARY)
        self.assertTrue(F('0.8747921786') < F(diag['B_tangency_display']) < F('0.8747921787'))


if __name__ == '__main__':
    unittest.main()
