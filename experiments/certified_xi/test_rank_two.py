import math
import unittest
from flint import arb, ctx
from coefficients import taylor_coefficients
from laboratory import interval
from rank_two import analyze, boundary


class RankTwoTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_xi_scaled_deficit_and_variance_budgets(self):
        rows=analyze(taylor_coefficients(8,1024))
        self.assertEqual(len(rows),5)
        for row in rows:
            self.assertEqual(row['epsilon_logconcavity_status'],'positive')
            for key in ('gamma_logconcavity_slack','normalized_rank2_slack',
                        'tilted_squared_variable_cv2','rank1_cv_budget_slack',
                        'rank2_log_budget_slack'):
                self.assertTrue(interval(row[key])>0,key)

    def test_first_shift_boundary(self):
        self.assertEqual(boundary(taylor_coefficients(4,512))['status'],'positive')
        exp=[arb(1)/math.factorial(n) for n in range(4)]
        self.assertTrue(interval(boundary(exp)['A2_logconcavity_slack']).contains(0))
        with self.assertRaises(ValueError):
            boundary(exp[:3])

    def test_rank_one_information_is_insufficient(self):
        mu=[arb(1)]+[arb(2)/math.factorial(n) for n in range(1,8)]
        row=analyze(mu)[0]
        self.assertEqual(row['center_m'],2)
        self.assertEqual(row['epsilon_logconcavity_status'],'negative')
        self.assertTrue(interval(row['epsilon_logconcavity_slack']).contains(arb('-1/2')))
        self.assertTrue(interval(row['normalized_rank2_slack']).contains(-8))

    def test_exponential_reference_epsilon_is_constant(self):
        mu=[arb(1)/math.factorial(n) for n in range(9)]
        for row in analyze(mu):
            self.assertTrue(interval(row['epsilon']).contains(1))
            self.assertTrue(interval(row['epsilon_logconcavity_slack']).contains(0))
            self.assertTrue(interval(row['rank1_cv_budget_slack']).contains(0))

    def test_fail_closed_on_insufficient_or_uncertain_data(self):
        with self.assertRaises(ValueError):
            analyze([arb(1)]*4)
        with self.assertRaises(ValueError):
            analyze([arb(0,1)]*5)

if __name__=='__main__':
    unittest.main()
