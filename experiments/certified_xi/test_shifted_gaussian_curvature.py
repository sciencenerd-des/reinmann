import math
import unittest

from flint import acb, arb, arb_series, ctx

from common_remainder import anchored_moments
from gaussian_jet_bound import gaussian_polynomials
from high_order_saddle import stirling_row
from shifted_gaussian_curvature import shifted_constants, uniform_shifted_curvature


class ShiftedGaussianCurvatureTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_full_reference_domain_certificate(self):
        result = uniform_shifted_curvature(10**6)
        self.assertEqual(result['status'], 'uniform_shifted_curvature_pass')
        self.assertEqual(result['anchor_threshold'], '1000000')
        self.assertTrue(all(result['conditions'].values()))
        self.assertLess(arb(result['upper_bounds']['combined_relative_budget']), arb('0.229338'))
        larger = uniform_shifted_curvature(10**8)
        self.assertEqual(larger['status'], 'uniform_shifted_curvature_pass')
        self.assertLess(arb(larger['upper_bounds']['combined_relative_budget']),
                        arb(result['upper_bounds']['combined_relative_budget']))
        with self.assertRaises(ValueError):
            uniform_shifted_curvature(999999)

    def test_shifted_common_remainder_against_original_integral(self):
        u, a, bounds, _, _, _, _, _, conditions = shifted_constants(10**6)
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
            w = arb_series([tilt+coefficients[1], 1], prec=5)
            moments = gaussian_polynomials(w, 9)
            b, c, d = coefficients[3], coefficients[4], coefficients[5]
            gamma = beta*2*u/(A.sqrt()*(1-beta))
            p1 = b*moments[3]
            p2 = c*moments[4]+b*b*moments[6]/2
            p3 = d*moments[5]+b*c*moments[7]+b**3*moments[9]/6+gamma*moments[1]
            remainder = z.log()-w*w/2-p1-p2+p1*p1/2-p3+p1*p2-p1**3/3
            for j in range(5):
                self.assertLess(abs(remainder[j]), bounds[j]*(u/a)**2)

    def test_original_reference_curvature_and_neighboring_errors(self):
        a = arb(10**6)
        u = (2*a/arb.pi()).lambertw()/2
        result = uniform_shifted_curvature(10**6)
        rows = [anchored_moments('1000000', offset) for offset in (-1, 0, 1)]
        mean = [row[1]/row[0] for row in rows]
        variance = [row[2]/row[0]-(row[1]/row[0])**2 for row in rows]
        q = a*(a-arb('0.5'))/((a+1)*(a+arb('0.5')))*rows[0][0]*rows[2][0]/rows[1][0]**2
        L = 1/a+1/(a-arb('0.5'))-1/(a+1)-1/(a+arb('0.5'))+mean[0]+mean[2]-2*mean[1]
        M = -1/a**2-1/(a-arb('0.5'))**2+1/(a+1)**2+1/(a+arb('0.5'))**2
        M += variance[0]+variance[2]-2*variance[1]
        v = 1+2*u
        h, ell = 4*u/v, 16*u*u*(u+1)/v**3
        m = -16*u**3*(8*u*u+16*u+9)/v**5
        limits = result['upper_bounds']
        self.assertLess(abs(q.log()+h/a), arb(limits['H_error_constant'])/a**2)
        self.assertLess(abs(L-ell/a**2), arb(limits['L_error_constant'])/a**3)
        self.assertLess(abs(M-m/a**3), arb(limits['M_error_constant'])/a**4)
        curvature = -1/(a+1)**2-q*M/(1-q)-q*L*L/(1-q)**2
        N = (4*u*u+8*u+1)/(a*a*v**4)
        self.assertLess(curvature, 0)
        self.assertLess(abs(curvature+N), arb(limits['reference_relative_budget'])*N)


if __name__ == '__main__':
    unittest.main()
