from fractions import Fraction as F
import math
import unittest
from flint import arb,ctx
from laboratory import interval
from effective_theta_remainder import uniform_bound
from boundary_budget import boundary_ratios,boundary_prefixes
from dual_rank_budget import dual_grid


class EffectiveRemainderBoundaryTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_uniform_remainder_constants_and_monotone_low_mass(self):
        first=uniform_bound(256)
        second=uniform_bound(512)
        for a,b in zip(first['moments'],second['moments']):
            self.assertLess(F(a['relative_error_upper']),F(1,10**29))
            self.assertTrue(interval(b['low_region_mass_ratio'])<interval(a['low_region_mass_ratio']))
        for X,U,limit in ((4096,2,F(1,10**222)),(65536,3,F(1,10**1650))):
            self.assertTrue(all(F(v['relative_error_upper'])<limit for v in uniform_bound(X,U)['moments']))

    def test_high_region_ratio_against_finite_sums(self):
        record=uniform_bound(256)
        bound=interval(record['pointwise_high_region_ratio'])
        pi=arb.pi()
        for u in map(arb,(1,2,3)):
            E=(2*u).exp()
            # Exact quotient expression for the first 8 omitted terms.
            ratio=sum((j**4-3*j*j/(2*pi*E))*(-pi*(j*j-1)*E).exp()
                      for j in range(2,10))/(1-3/(2*pi*E))
            self.assertTrue(ratio<bound)

    def test_remainder_rejects_bad_domains_and_insufficient_threshold(self):
        for args in ((-1,), (256,'1/2'), (256,1,0)):
            with self.assertRaises(ValueError):
                uniform_bound(*args)
        with self.assertRaises(ValueError):
            uniform_bound(256,max_order=5)
        with self.assertRaises(ArithmeticError):
            uniform_bound(1)

    def test_dual_grid_reference_and_range_guard(self):
        reference=[arb(1)/math.factorial(n) for n in range(8)]
        ratios=dual_grid(reference,max_rank=3,max_shift=3)
        self.assertEqual(len(ratios),9)
        self.assertTrue(all(v.contains(1) for v in ratios.values()))
        with self.assertRaises(ValueError):
            dual_grid(reference,max_rank=7,max_shift=3)
        with self.assertRaises(ArithmeticError):
            dual_grid([arb(1)]*5,max_rank=2,max_shift=2)

    def test_boundary_reference_and_adversarial_control(self):
        reference=[arb(1)/math.factorial(n) for n in range(8)]
        ratios,rows=boundary_ratios(reference)
        self.assertTrue(all(v.contains(1) for v in ratios.values()))
        self.assertTrue(all(interval(v['strengthened_boundary_slack']).contains(0) for v in rows))
        control=list(map(arb,('1','1','0.9','0.801')))
        _,rows=boundary_ratios(control)
        self.assertEqual(rows[1]['boundary_status'],'negative')
        with self.assertRaises(ValueError):
            boundary_ratios(reference[:3])
        with self.assertRaises(ArithmeticError):
            boundary_prefixes({1:arb(1)},{})
        with self.assertRaises(ValueError):
            boundary_prefixes({1:arb('1/2')},{})


if __name__=='__main__':
    unittest.main()
