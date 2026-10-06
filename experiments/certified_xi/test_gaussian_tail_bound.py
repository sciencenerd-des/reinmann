import math
import unittest
from flint import arb, ctx
from gaussian_tail_bound import uniform_tail, gaussian_absolute_moments
from common_remainder import derivative_bound
from high_order_saddle import stirling_row


class GaussianTailBoundTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_uniform_tail_has_margin_and_all_conditions(self):
        result = uniform_tail(80)
        self.assertEqual(result['status'], 'uniform_tail_majorants_pass')
        self.assertTrue(all(result['conditions'].values()))
        self.assertLess(arb(result['upper_bounds']['relative_margin_budget']), arb('0.009502'))

    def test_failed_budget_is_unresolved(self):
        result = uniform_tail(60)
        self.assertEqual(result['status'], 'unresolved')
        self.assertFalse(result['conditions']['half_negative_margin'])
        with self.assertRaises(ValueError):
            uniform_tail(19)

    def test_integer_tail_coefficient_majorant(self):
        total = sum(math.factorial(k)//math.factorial(k-j)*2**(j+1)
                    for k in range(7) for j in range(k+1))
        self.assertLess(total, 10**6)

    def test_phase_envelope_against_exact_coefficients(self):
        bound = arb(uniform_tail(80)['upper_bounds']['phase_constant'])
        for anchor_u in (80, 100):
            u = arb(anchor_u)
            a = arb.pi()*u*(2*u).exp()
            A = 2*a*(1+2*u)-arb(9)*u/2
            L = (32*u).sqrt()
            exact_triangle = arb(0)
            for j in range(5, 17):
                T = sum((arb(s)*(2*u)**k for k, s in enumerate(stirling_row(j))), arb(0))
                exact_triangle += abs(arb(9)*u/2-a/u*T)/math.factorial(j)*(L/A.sqrt())**j
            self.assertLess(exact_triangle, bound*u**4/a**arb('1.5'))

    def test_absolute_gaussian_moments(self):
        moments = gaussian_absolute_moments(16)
        self.assertEqual(moments[6], 15)
        self.assertEqual(moments[8], 105)
        self.assertTrue(moments[5].overlaps(8*moments[1]))
        self.assertTrue(moments[7].overlaps(48*moments[1]))
        with self.assertRaises(ValueError):
            gaussian_absolute_moments(0)

    def test_integrated_error_and_larger_disk_close_tail(self):
        result = uniform_tail(40, integrated_errors=True, disk_divisor=2)
        self.assertEqual(result['status'], 'uniform_tail_majorants_pass')
        self.assertEqual(result['disk_divisor'], '2')
        self.assertEqual(result['error_method'], 'gaussian_absolute_moments')
        self.assertTrue(all(result['conditions'].values()))
        self.assertLess(arb(result['upper_bounds']['relative_margin_budget']), arb('0.038351'))
        failed = uniform_tail(35, integrated_errors=True, disk_divisor=4)
        self.assertEqual(failed['status'], 'unresolved')

    def test_complex_disk_parameter_rejection(self):
        with self.assertRaises(ValueError):
            uniform_tail(40, disk_divisor=0)
        with self.assertRaises(ValueError):
            uniform_tail(40, disk_divisor=10**100)

    def test_true_remainder_base_hypotheses(self):
        result = derivative_bound(10**6)
        for row in result['derivatives'][2:]:
            self.assertLess(arb(row['absolute_upper']), 1)
        self.assertGreater((arb(2)*10**6/arb.pi()).lambertw()/2, 1)


if __name__ == '__main__':
    unittest.main()
