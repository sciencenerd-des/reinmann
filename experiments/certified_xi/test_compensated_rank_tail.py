from fractions import Fraction
import unittest
from flint import arb, ctx
from compensated_rank_tail import compensated_budget
from rank_tail_bootstrap import tail_budget
from laboratory import interval


class CompensatedRankTailTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_exact_baseline_telescope(self):
        for n in (3, 10, 100):
            product = Fraction(1)
            for j in range(21):
                self.assertEqual(product, Fraction(n*(n+j-1), (n-1)*(n+j)))
                product *= Fraction((n+j)**2, (n+j)**2-1)

    def test_shift_factor_closes_previously_unresolved_budget(self):
        self.assertEqual(tail_budget(3, '0.2')['status'], 'unresolved')
        result = compensated_budget(20, 2, 3, '0.2', steps=0)
        self.assertEqual(result['status'], 'conditional_compensated_tail_pass')
        self.assertEqual(result['prefix_margins'], [])
        self.assertGreater(interval(result['tail_margin']), 0)
        self.assertIn('Neighboring correction factors', result['hypothesis'])

    def test_adverse_recurrence_with_compensation(self):
        R, m = 20, 2
        d, v = arb(3), arb('0.2')
        result = compensated_budget(R, m, d, v)
        self.assertEqual(result['status'], 'conditional_compensated_tail_pass')
        b = arb(result['sustained_slope_lower'])
        start = d
        for j in range(100):
            n = R+m+j
            z = arb(m)/n*(-d).exp()
            correction = (arb(n)**2/(n*n-1)).log()+2*(-z).log1p()
            v += correction
            d += v
            self.assertGreater(v, b)
            self.assertGreater(d, start+(j+1)*b)

    def test_failed_budget_and_invalid_domains(self):
        self.assertEqual(compensated_budget(2, 2, '0.01', '0.01')['status'], 'unresolved')
        for args in ((0,2,1,1), (1,1,1,1), (1,2,0,1), (1,2,1,0), (True,2,1,1)):
            with self.assertRaises(ValueError):
                compensated_budget(*args)
        for steps in (-1, 1.5, 10001):
            with self.assertRaises(ValueError):
                compensated_budget(1,2,1,1,steps=steps)


if __name__ == '__main__':
    unittest.main()
