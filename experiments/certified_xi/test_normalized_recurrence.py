from fractions import Fraction as F
import copy
import math
import unittest
from flint import arb,ctx
from laboratory import endpoints,minor
from normalized_recurrence import load_ratios,transport


class NormalizedRecurrenceTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_exponential_reference_and_prefactors(self):
        mu=[arb(1)/math.factorial(n) for n in range(15)]
        p=lambda r,m: F(math.prod(math.factorial(j) for j in range(r)),
                        math.prod(math.factorial(m+j) for j in range(r)))
        for r in range(1,5):
            for m in range(1,5):
                self.assertEqual(p(r+1,m)*p(r-1,m)/p(r,m)**2,F(r,m+r))
                self.assertEqual(p(r,m-1)*p(r,m+1)/p(r,m)**2,F(m,m+r))
                self.assertTrue(minor(mu,r,m).overlaps(arb(str(p(r,m)))))
        predicted,inherited,correction=transport(3,4,*[arb(1)]*4)
        self.assertTrue(predicted.contains(1))
        self.assertTrue(inherited.is_zero())
        self.assertTrue(correction.is_zero())

    def test_transport_from_fresh_nontrivial_determinants(self):
        mu=[arb(3+4**n)/math.factorial(2*n) for n in range(15)]
        def t(r,m):
            return arb(m+r)/m*minor(mu,r,m-1)*minor(mu,r,m+1)/minor(mu,r,m)**2
        predicted,inherited,correction=transport(2,3,t(1,3),t(2,3),t(2,2),t(2,4))
        self.assertTrue(predicted.overlaps(t(3,3)))
        self.assertTrue((inherited+correction).overlaps(-t(3,3).log()))

    def test_reject_invalid_or_inconsistent_inputs(self):
        row={'rank':2,'shift':3,'candidate_slack':endpoints(arb('1/100')),
             'relative_margin':endpoints(arb('41/100'))}
        data={'schema_version':1,'status':'finite_ball_results_not_unbounded_order_proof',
              'recurrence_windows':[row]}
        self.assertTrue(load_ratios(data)[2,3]>0)
        bad=copy.deepcopy(data)
        bad['recurrence_windows'].append(row)
        with self.assertRaises(ValueError):
            load_ratios(bad)
        bad=copy.deepcopy(data)
        bad['recurrence_windows'][0]['candidate_slack']=endpoints(arb(0))
        with self.assertRaises(ValueError):
            load_ratios(bad)
        with self.assertRaises(ValueError):
            transport(2,1,*[arb(1)]*4)
        with self.assertRaises(ValueError):
            transport(2,3,arb(0),arb(1),arb(1),arb(1))
        with self.assertRaises(ArithmeticError):
            transport(2,3,*[arb(4)]*4)


if __name__=='__main__':
    unittest.main()
