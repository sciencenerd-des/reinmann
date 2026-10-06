import math
import unittest

from flint import acb, arb, arb_series, ctx, fmpq_poly

from coefficientwise_curvature import coefficientwise_constants, uniform_coefficientwise_tail
from cubic_gaussian_tail import fourth_order_constants
from gaussian_jet_bound import gaussian_polynomials
from high_order_saddle import stirling_row


class CoefficientwiseCurvatureTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_tail_and_domain(self):
        result = uniform_coefficientwise_tail(6)
        self.assertEqual(result['status'], 'uniform_coefficientwise_tail_pass')
        self.assertTrue(all(result['conditions'].values()))
        self.assertLess(arb(result['upper_bounds']['combined_relative_budget']), arb('0.468174'))
        self.assertGreater(arb(result['scaled_deficit_lower']), arb('1.84'))
        with self.assertRaises(ValueError):
            uniform_coefficientwise_tail(5)

    def test_exact_leading_derivative_bounds(self):
        u = fmpq_poly([0, 1])
        v = 1+2*u
        ell_numerator = 16*u*u*(u+1)
        m_absolute_numerator = 16*u**3*(8*u*u+16*u+9)
        for poly in (2*v**3-ell_numerator, 4*v**5-m_absolute_numerator):
            self.assertTrue(all(c >= 0 for c in poly.coeffs()))

    def test_individual_coefficients_improve_old_norm(self):
        for U in (6, 7, 14):
            _, _, old, _, _, _, _, _ = fourth_order_constants(U)
            _, _, bounds, _, _, _, _ = coefficientwise_constants(U)
            for value in bounds:
                self.assertLess(value, old)

    def test_individual_remainder_derivatives_against_quadrature(self):
        u, a, bounds, _, _, _, _ = coefficientwise_constants(6)
        A = 2*a*(1+2*u)-arb('4.5')*u
        window, beta = (32*u).sqrt(), arb('1.5')*u/a
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
            moments = gaussian_polynomials(t, 9)
            l, b, c, d = coefficients[1], coefficients[3], coefficients[4], coefficients[5]
            gamma = beta*2*u/(A.sqrt()*(1-beta))
            p1 = l*moments[1]+b*moments[3]
            p2 = c*moments[4]+l*l*moments[2]/2+l*b*moments[4]+b*b*moments[6]/2
            p3 = ((d+l*c)*moments[5]+b*c*moments[7]+l**3*moments[3]/6
                  +l*l*b*moments[5]/2+l*b*b*moments[7]/2+b**3*moments[9]/6+gamma*moments[1])
            remainder = z.log()-t*t/2-p1-p2+p1*p1/2-p3+p1*p2-p1**3/3
            for j in range(5):
                self.assertLess(abs(remainder[j]), bounds[j]*(u/a)**2)


if __name__ == '__main__':
    unittest.main()
