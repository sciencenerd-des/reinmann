import unittest
from flint import arb, acb, ctx
from laboratory import interval
from high_order_saddle import stirling_row, growing_bound, model_moments, certify_point
from localized_saddle import phase


class HighOrderSaddleTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_touchard_coefficients_and_domains(self):
        self.assertEqual(stirling_row(0),[1])
        self.assertEqual(stirling_row(3),[0,1,3,1])
        self.assertEqual(stirling_row(4),[0,1,7,6,1])
        self.assertEqual(sum(stirling_row(13)),27644437)
        for value in (-1,26,True):
            with self.assertRaises(ValueError):
                stirling_row(value)
        with self.assertRaises(ValueError):
            growing_bound(65535)
        with self.assertRaises(ValueError):
            growing_bound(10**8,degree=25)
        with self.assertRaises(ArithmeticError):
            growing_bound(65536,window_factor=10000)

    def test_uniform_bounds_improve_without_fixed_tail_floor(self):
        previous=None
        for x in (10**6,10**8,10**12):
            record=growing_bound(x)
            self.assertTrue(interval(record['constants']['gaussian_tail_exponent'])>0)
            if previous:
                for a,b in zip(previous['moments'],record['moments']):
                    self.assertTrue(arb(b['relative_error_upper'])<arb(a['relative_error_upper']))
                    self.assertTrue(arb(b['tail_relative_upper'])<arb(a['tail_relative_upper']))
            previous=record
        self.assertTrue(arb(previous['moments'][2]['relative_error_upper'])<arb('1.374e-61'))

    def test_independent_true_phase_integral(self):
        # Stable exact phase differences, not the Touchard Taylor model.
        x=arb(10**8)
        model,quad=model_moments(x)
        bound=growing_bound(10**8)
        u=(2*x/arb.pi()).lambertw()/2
        c=u.log()
        A=2*x*(1+2*u)-arb(9)*u/2
        L=(32*u).sqrt()
        scale=4*arb.pi()**2*phase(c,x).exp()/A.sqrt()
        for k in range(3):
            def integrand(s,_analytic):
                d=s/A.sqrt()
                shift=d.expm1()
                exponent=(2*x+1)*d+arb(9)*u/2*shift-x/u*(2*u*shift).expm1()
                amplitude=1-3/(2*arb.pi())*(-2*u*d.exp()).exp()
                return exponent.exp()*amplitude*(2*(c+d))**k
            actual=acb.integral(integrand,-L,L,rel_tol=arb(2)**-220,abs_tol=arb(2)**-240)
            self.assertTrue(actual.is_finite())
            self.assertTrue(actual.imag.contains(0))
            ratio=actual.real*scale/model[k]
            self.assertTrue(abs(ratio-1)+quad[k]<arb(bound['moments'][k]['relative_error_upper']))

    def test_curvature_success_and_inconclusive_case(self):
        failed=certify_point(10**6+1)
        self.assertEqual(failed['status'],'unresolved')
        self.assertTrue(interval(failed['transfer']['curvature_enclosure']).contains(0))
        passed=certify_point(10**8+1)
        self.assertEqual(passed['status'],'certified_negative_curvature_at_point')
        self.assertTrue(interval(passed['transfer']['curvature_enclosure'])<0)


if __name__=='__main__':
    unittest.main()
