import unittest
from fractions import Fraction as F
from flint import arb,ctx
from lambert_curvature import leading_tail,real_zero_control


class LambertCurvatureTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_uniform_margin_and_domain_rejection(self):
        result=leading_tail(256)
        self.assertTrue(arb(result['budget_upper'])<arb('0.178'))
        with self.assertRaises(ValueError):
            leading_tail(0)
        with self.assertRaises(ArithmeticError):
            leading_tail(1)

    def test_direct_derivatives_respect_proved_bound(self):
        margin=arb(leading_tail()['margin_fraction_lower'])
        for parameter in (256,1000,10**8):
            x=arb(parameter)
            w=(2*x/arb.pi()).lambertw()
            h=2*w/(x*(1+w))
            hp=-2*w**2*(w+2)/(x**2*(1+w)**3)
            hpp=2*w**3*(2*w**2+8*w+9)/(x**3*(1+w)**5)
            Q=(w*w+4*w+1)/(x*x*(1+w)**4)
            exact=-1/(x+1)**2+hpp/h.expm1()-h.exp()*hp**2/h.expm1()**2
            self.assertTrue(exact < -margin*Q)

    def test_exact_real_zero_counterexample(self):
        row=real_zero_control(3)
        self.assertEqual(F(row['continuous_log_curvature']),F(17,2888))
        self.assertEqual(F(row['discrete_logconcavity_slack']),F(-439,57600))
        for x in (3,10,1000):
            row=real_zero_control(x)
            self.assertGreater(F(row['continuous_log_curvature']),0)
            self.assertLess(F(row['discrete_logconcavity_slack']),0)

    def test_tent_cancellation_for_polynomial_remainder(self):
        # R(t)=a+b*t+c*t^2+d*t^3+e*t^4: integrate its second
        # derivative against 1-|s| exactly, using mass 1 and second moment 1/6.
        a,b,c,d,e=map(F,(1000000,-99999,7,-3,2))
        R=lambda t:a+b*t+c*t*t+d*t**3+e*t**4
        for x in map(F,(2,10,100)):
            direct=R(x-1)-2*R(x)+R(x+1)
            tent=2*c+6*d*x+12*e*x*x+2*e
            self.assertEqual(direct,tent)


if __name__=='__main__':
    unittest.main()
