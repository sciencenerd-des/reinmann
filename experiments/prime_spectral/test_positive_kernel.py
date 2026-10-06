import json
import math
from pathlib import Path
import unittest
from flint import arb, acb, ctx
from positive_kernel import bernstein_coefficients, run
from quotient_operator import build, fourier_profile
from certified_mode_comparison import box


class PositiveKernelTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512
        root=Path(__file__).resolve().parents[2]
        self.certificates=[json.loads((root/f'research/prime_spectral/certified_weil_13_{N}.json').read_text()) for N in (4,8)]

    def test_whole_interval_positivity_and_endpoints(self):
        for certificate in self.certificates:
            result=run(certificate)
            coefficients=[box(x) for x in result['bernstein_coefficients']]
            self.assertTrue(all(x>0 for x in coefficients))
            self.assertTrue(coefficients[0].contains(1))
            self.assertGreater(box(result['variance']),0)
            self.assertLess(box(result['variance']),arb('0.1'))

    def test_bernstein_representation_matches_fourier_kernel(self):
        c,L,_,_=build(self.certificates[1])
        N=8
        b=bernstein_coefficients(c[N+1:])
        for s in (arb(0),arb('0.1'),arb('0.25'),arb('0.49'),arb('0.5')):
            u=(1+(2*arb.pi()*s).cos())/2
            polynomial=sum((b[k]*math.comb(N,k)*u**k*(1-u)**(N-k) for k in range(N+1)),arb(0))
            fourier=c[N]+2*sum(((-1)**n*c[N+n]*(2*arb.pi()*n*s).cos() for n in range(1,N+1)),arb(0))
            self.assertTrue((polynomial-fourier).contains(0))

    def test_independent_kernel_integrals(self):
        certificate=self.certificates[0]
        c,L,_,_=build(certificate)
        N=4
        def density(t):
            return (c[N]+2*sum(((-1)**n*c[N+n]*(t*2*arb.pi()*n/L).cos() for n in range(1,N+1)),acb(0)))/(L*c[N])
        variance=acb.integral(lambda t, analytic: t*t*density(t),-L/2,L/2)
        self.assertTrue((variance-box(run(certificate)['variance'])).contains(0))
        z=acb('0.4','0.7')
        transform=acb.integral(lambda t, analytic: (-acb(0,1)*z*t).exp()*density(t),-L/2,L/2)
        self.assertTrue((transform-fourier_profile(c,L,z)).contains(0))

    def test_positivity_is_not_automatic(self):
        # c1=2/5, c0=1/5: g(center)=-3/5, although its mass is positive.
        coefficients=bernstein_coefficients([arb(2)/5])
        self.assertLess(coefficients[-1],0)
        with self.assertRaises(ValueError):
            bernstein_coefficients([])


if __name__=='__main__':
    unittest.main()
