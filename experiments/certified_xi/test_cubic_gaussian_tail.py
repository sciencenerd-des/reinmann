import math
import unittest

from flint import acb, arb, arb_series, ctx

from cubic_gaussian_tail import cubic_identity, fourth_order_constants, uniform_cubic_tail
from gaussian_jet_bound import gaussian_polynomials
from high_order_saddle import stirling_row


class CubicGaussianTailTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_exact_cubic_cancellation(self):
        result = cubic_identity()
        self.assertTrue(result['degree_seven_and_nine_cancel'])
        self.assertEqual(result['fourth_derivative_at_zero'], '0')

    def test_uniform_tail_and_failure_classification(self):
        result = uniform_cubic_tail(7)
        self.assertEqual(result['status'], 'uniform_cubic_tail_majorants_pass')
        self.assertTrue(all(result['conditions'].values()))
        self.assertLess(arb(result['upper_bounds']['combined_relative_budget']), arb('0.742183'))
        failed = uniform_cubic_tail(6)
        self.assertEqual(failed['status'], 'unresolved')
        self.assertFalse(failed['conditions']['strict_negative_margin'])
        with self.assertRaises(ValueError):
            uniform_cubic_tail(5)

    def test_elementary_replacement_envelopes(self):
        for U in (6, 7, 14):
            u, a, _, _, _, _, _, _ = fourth_order_constants(U)
            v = 1+2*u
            A = 2*a*v-arb('4.5')*u
            t3, t4 = 1+6*u+4*u*u, 1+14*u+24*u*u+8*u**3
            p3, p4 = arb('4.5')*u-2*a*t3, arb('4.5')*u-2*a*t4
            AH = arb(9)/(4*u)
            AL = 9*(4+7/u+1/u**2)/(8*u)
            AM = (arb(45)/4*(8+24/u+14/u**2+1/u**3)/(16*u)+arb(9)/(16*u**3)
                  +arb(81)/2*(4+6/u+1/u**2)**2/(32*u)
                  +54*(4+6/u+1/u**2)/(32*u**2)+arb(243)/(128*a*u**3))
            self.assertLess(abs(4/A-2/(a*v)), AH/a**2)
            self.assertLess(abs(8*p3/A**3+2*t3/(a*a*v**3)), AL/a**3)
            self.assertLess(abs(16*p4/A**4+48*p3*p3/A**5
                                +2*t4/(a**3*v**4)-6*t3*t3/(a**3*v**5)), AM/a**4)
            logc = ((1-1/(2*a))/((1+1/a)*(1+1/(2*a)))).log()
            L = 1/a+1/(a-arb('0.5'))-1/(a+1)-1/(a+arb('0.5'))
            M = -1/a**2-1/(a-arb('0.5'))**2+1/(a+1)**2+1/(a+arb('0.5'))**2
            self.assertLess(abs(logc+2/a), 1/a**2)
            self.assertLess(abs(L-2/a**2), 2/a**3)
            self.assertLess(abs(M+4/a**3), 6/a**4)

    def test_fourth_order_common_remainder_against_quadrature(self):
        u, a, C, _, _, _, _, conditions = fourth_order_constants(6)
        self.assertTrue(all(conditions.values()))
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
            norm = sum((abs(remainder[k]) for k in range(5)), arb(0))
            self.assertLess(norm, C*(u/a)**2)


if __name__ == '__main__':
    unittest.main()
