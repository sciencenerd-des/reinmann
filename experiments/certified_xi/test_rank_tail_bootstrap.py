import unittest
from flint import arb, ctx
from laboratory import interval
from normalized_recurrence import transport
from rank_tail_bootstrap import tail_budget


class RankTailBootstrapTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_pass_is_explicitly_conditional(self):
        result = tail_budget(10, '0.2')
        self.assertEqual(result['status'], 'conditional_tail_budget_pass')
        self.assertIn('neighboring correction factors', result['hypothesis'])
        self.assertGreater(interval(result['margin']), 0)

    def test_inadequate_and_invalid_heads(self):
        self.assertEqual(tail_budget('0.1', '0.1')['status'], 'unresolved')
        for d, v in ((0, 1), (1, 0), (-1, 1), (1, -1)):
            with self.assertRaises(ValueError):
                tail_budget(d, v)

    def test_correction_bound_allows_neighbor_ratios_above_one(self):
        d = arb(2)
        _, _, correction = transport(5, 4, arb(1), (-d).exp(), arb('1.5'), arb('1.2'))
        lower = -2*(-d).exp()/(-(-d).expm1())
        self.assertGreater(correction, lower)

    def test_adverse_recurrence_respects_sustained_slope(self):
        d, slope = arb(10), arb('0.2')
        result = tail_budget(d, slope)
        b = arb(result['sustained_slope_lower'])
        start = d
        for j in range(1, 101):
            # The worst allowed correction, without any positive baseline.
            correction = -2*(-d).exp()/(-(-d).expm1())
            slope += correction
            d += slope
            self.assertGreater(slope, b)
            self.assertGreater(d, start+j*b)


if __name__ == '__main__':
    unittest.main()
