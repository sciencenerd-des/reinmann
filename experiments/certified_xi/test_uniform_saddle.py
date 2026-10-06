import unittest
from flint import arb, acb, ctx
from laboratory import interval
from localized_saddle import first_summand_models, phase
from uniform_saddle import uniform_quadratic_bound


class UniformSaddleTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_domain_and_failed_decay(self):
        for x, radius in ((255, 8), (65536, 1)):
            with self.assertRaises(ValueError):
                uniform_quadratic_bound(x, radius)
        with self.assertRaises(ArithmeticError):
            uniform_quadratic_bound(256, 64)

    def test_global_bounds_cover_local_derivatives(self):
        record = uniform_quadratic_bound(65536)
        constants = record['constants']
        C = interval(constants['standardized_third_derivative_upper']).upper()
        tilt = interval(constants['tilt_upper']).upper()
        for x in (65536, 10**8, 10**12):
            x = arb(x)
            u = (2*x/arb.pi()).lambertw()/2
            A = 2*x*(1+2*u)-arb(9)*u/2
            self.assertTrue((1+arb(9)*u/2)/A.sqrt() < tilt)
            for s in (-8, -4, 0, 4, 8):
                v = u*(arb(s)/A.sqrt()).exp()
                third = arb(9)*v/2-2*arb.pi()*v*(2*v).exp()*(1+6*v+4*v**2)
                self.assertTrue(abs(third)/A**arb('1.5') < C)

    def test_uniform_error_contains_independent_integral_difference(self):
        bound = uniform_quadratic_bound(65536)
        # A finite regression check of a uniform analytic bound, not its proof.
        for parameter in (65536, 10**6):
            x = arb(parameter)
            actual, errors, _ = first_summand_models(x)
            u = (2*x/arb.pi()).lambertw()/2
            c = u.log()
            A = 2*x*(1+2*u)-arb(9)*u/2
            tilt = (1+arb(9)*u/2)/A.sqrt()
            scale = 4*arb.pi()**2*phase(c,x).exp()/A.sqrt()
            for k in range(3):
                def integrand(s, _analytic):
                    return (tilt*s-s*s/2).exp()*(2*(c+s/A.sqrt()))**k
                quadratic = acb.integral(integrand,-8,8,
                                         rel_tol=arb(2)**-120, abs_tol=arb(2)**-140)
                self.assertTrue(quadratic.is_finite())
                self.assertTrue(quadratic.imag.contains(0))
                ratio = actual[k]/(scale*quadratic.real)
                discrepancy = abs(ratio-1)+abs(ratio)*errors[k]
                self.assertTrue(discrepancy < arb(bound['moments'][k]['relative_error_upper']))

    def test_threshold_improvement_and_precision_restoration(self):
        ctx.prec = 192
        coarse = uniform_quadratic_bound(10**8)
        fine = uniform_quadratic_bound(10**12)
        self.assertEqual(ctx.prec, 192)
        for a,b in zip(coarse['moments'],fine['moments']):
            self.assertTrue(0 < arb(b['relative_error_upper']) < arb(a['relative_error_upper']))
        self.assertLess(arb(fine['moments'][2]['relative_error_upper']), arb('0.001281'))


if __name__ == '__main__':
    unittest.main()
