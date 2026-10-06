import math
import unittest

from flint import acb, arb, arb_series, ctx, fmpq_poly

from gaussian_jet_bound import gaussian_polynomials, jet_constants, uniform_jet_tail
from high_order_saddle import stirling_row


class GaussianJetBoundTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_passing_tail_and_unresolved_lower_anchor(self):
        result = uniform_jet_tail(14)
        self.assertEqual(result['status'], 'uniform_jet_tail_majorants_pass')
        self.assertTrue(all(result['conditions'].values()))
        self.assertLess(arb(result['upper_bounds']['combined_relative_budget']), arb('0.274447'))
        lower = uniform_jet_tail(6)
        self.assertEqual(lower['status'], 'unresolved')
        self.assertFalse(lower['conditions']['half_negative_margin'])
        with self.assertRaises(ValueError):
            uniform_jet_tail(5)

    def test_exact_touchard_majorants(self):
        u = fmpq_poly([0, 1])
        v = 1+2*u
        t3 = 1+6*u+4*u**2
        t4 = 1+14*u+24*u**2+8*u**3
        for polynomial in (2*v**2-t3, 6*v**3-t4):
            self.assertTrue(all(c >= 0 for c in polynomial.coeffs()))

    def test_replacement_errors_against_exact_expressions(self):
        for U in (6, 14, 40):
            u = arb(U)
            a = arb.pi()*u*(2*u).exp()
            v = 1+2*u
            A = 2*a*v-arb('4.5')*u
            t3, t4 = 1+6*u+4*u**2, 1+14*u+24*u**2+8*u**3
            p3, p4 = arb('4.5')*u-2*a*t3, arb('4.5')*u-2*a*t4
            self.assertLess(abs(4/A-2/(a*v)), 4/a**2)
            self.assertLess(abs(8*p3/A**3+2*t3/(a**2*v**3)), 250/a**3)
            self.assertLess(abs(16*p4/A**4+48*p3**2/A**5
                                +2*t4/(a**3*v**4)-6*t3**2/(a**3*v**5)), 10000/a**4)

    def test_common_integral_log_jet_with_independent_quadrature(self):
        # Regression at the lower permitted U, including both neighboring
        # parameters. This checks the implementation, not the uniform proof.
        u, a, C, _, conditions = jet_constants(6)
        self.assertTrue(all(conditions.values()))
        A = 2*a*(1+2*u)-arb('4.5')*u
        window = (32*u).sqrt()
        beta = arb('1.5')*u/a
        coefficients = [arb(0), (1+arb('4.5')*u)/A.sqrt()]
        for j in range(2, 17):
            touchard = sum((arb(s)*(2*u)**k
                            for k, s in enumerate(stirling_row(j))), arb(0))
            coefficients.append((arb('4.5')*u-a/u*touchard)
                                /(math.factorial(j)*A**(arb(j)/2)))
        for offset in (-1, 0, 1):
            tilt = 2*offset/A.sqrt()
            integrals = []
            for k in range(5):
                def integrand(s, _analytic):
                    phase = acb(0)
                    for coefficient in reversed(coefficients):
                        phase = phase*s+coefficient
                    amplitude = (1-beta*(-2*u*((s/A.sqrt()).exp()-1)).exp())/(1-beta)
                    return (phase+tilt*s).exp()*amplitude*s**k/(2*arb.pi()).sqrt()
                value = acb.integral(integrand, -window, window,
                                     rel_tol=arb(2)**-200, abs_tol=arb(2)**-220)
                self.assertTrue(value.is_finite())
                self.assertTrue(value.imag.contains(0))
                integrals.append(value.real/math.factorial(k))
            z = arb_series(integrals, prec=5)
            t = arb_series([tilt, 1], prec=5)
            moments = gaussian_polynomials(t, 6)
            lam, cubic, quartic = coefficients[1], coefficients[3], coefficients[4]
            p1 = lam*moments[1]+cubic*moments[3]
            p2 = (quartic*moments[4]+lam**2*moments[2]/2
                  +lam*cubic*moments[4]+cubic**2*moments[6]/2)
            remainder = z.log()-t*t/2-p1-p2+p1*p1/2
            norm = sum((abs(remainder[k]) for k in range(5)), arb(0))
            self.assertLess(norm, C*(u/a)**arb('1.5'))


if __name__ == '__main__':
    unittest.main()
