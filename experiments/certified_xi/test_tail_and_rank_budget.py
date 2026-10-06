import unittest
from fractions import Fraction as F
from flint import arb,ctx
from test_coupled_cover import Jet
from tail_and_rank_budget import saddle_scale,discrete_samples,cumulative_budgets


class TailAndRankBudgetTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_model_curvature_by_exact_chain_rule(self):
        for x,w in ((F(2),F(1)),(F(7),F(3)),(F(100),F(8))):
            xx,ww=Jet(x,1),Jet(w,w/(x*(1+w)))
            derivative=(Jet(1)/(xx*(1+ww)**2)).derivative
            expected=-(w*w+4*w+1)/(x*x*(1+w)**4)
            self.assertEqual(derivative,expected)
        for x in (1,10,100,10000):
            epsilon,curvature=saddle_scale(x)
            self.assertTrue(0<epsilon<2)
            self.assertTrue(curvature>0)
        with self.assertRaises(ValueError):
            saddle_scale(0)

    def test_contiguous_rank_budget_and_gap_rejection(self):
        ratios={(1,m):arb('1/2') for m in range(1,6)}
        for m in range(2,5):
            b=lambda j:1+arb(j)/2
            ratios[2,m]=arb('1/4')*b(m-1)*b(m+1)/b(m)**2
        rows=cumulative_budgets(ratios)
        self.assertEqual(len(rows),3)
        self.assertTrue(all(r['budget_status']=='positive' for r in rows))
        del ratios[1,3]
        with self.assertRaises(ValueError):
            cumulative_budgets(ratios)

    def test_degenerate_data_is_not_a_tail_certificate(self):
        with self.assertRaises(ValueError):
            discrete_samples([arb(1)]*4)
        with self.assertRaises(ArithmeticError):
            discrete_samples([arb(1)]*5)
        with self.assertRaises(ArithmeticError):
            cumulative_budgets({(1,2):arb(1)})


if __name__=='__main__':
    unittest.main()
