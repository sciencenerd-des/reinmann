import unittest
from flint import arb, acb, ctx
from laboratory import interval
from localized_saddle import (
    phase, polynomial_tangent_tail, first_summand_models, certify_point,
)


class LocalizedSaddleTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_tangent_integrals_and_invalid_domains(self):
        # Exact integrals of exp(-2v) times 1, 2(3+v), 4(3+v)^2.
        for k, expected in enumerate(('1/2', '7/2', '25')):
            result = polynomial_tangent_tail(arb(-3), arb(2), arb(0), k)
            self.assertTrue(result.contains(arb(expected)))
        for slope, k in ((0, 0), (-1, 1), (1, 3), (1, True)):
            with self.assertRaises(ValueError):
                polynomial_tangent_tail(arb(1), arb(slope), arb(0), k)
        with self.assertRaises(ValueError):
            first_summand_models(255)
        with self.assertRaises(ValueError):
            certify_point(256)

    def test_independent_u_coordinate_integral(self):
        # Check the substitution and normalization in another coordinate.
        models, errors, record = first_summand_models(256)
        center = interval(record['center'])
        p0 = phase(center, arb(256))
        lo, hi = interval(record['left']).exp(), interval(record['right']).exp()
        scale = 4 * arb.pi()**2 * p0.exp()
        for k in range(3):
            def integrand(u, _analytic):
                return ((512*u.log()+arb(9)*u/2-arb.pi()*(2*u).exp()-p0).exp()
                        * (1-3/(2*arb.pi())*(-2*u).exp())*(2*u.log())**k)
            direct = acb.integral(integrand, lo, hi,
                                  rel_tol=arb(2)**-120, abs_tol=arb(2)**-140)
            self.assertTrue(direct.is_finite())
            self.assertTrue(direct.imag.contains(0))
            model = models[k] / scale
            enclosure = model + arb(0, (abs(model)*errors[k]).upper())
            self.assertTrue(enclosure.overlaps(direct.real))

    def test_wider_window_reduces_both_analytic_tails(self):
        _, _, narrow = first_summand_models(256, spread=8)
        _, _, wide = first_summand_models(256, spread=16)
        for a, b in zip(narrow['moments'], wide['moments']):
            for side in ('left_tail_upper', 'right_tail_upper'):
                self.assertTrue(arb(b[side]) < arb(a[side]))

    def test_true_theta_curvature_with_propagated_errors(self):
        result = certify_point(257)
        self.assertEqual(result['status'], 'certified_negative_curvature_at_point')
        self.assertTrue(interval(result['transfer']['curvature_enclosure']) < 0)
        self.assertEqual(len(result['moments']), 3)
        for record in result['moments']:
            for error in record['combined_errors']:
                self.assertTrue(0 < arb(error) < arb('1e-25'))


if __name__ == '__main__':
    unittest.main()
