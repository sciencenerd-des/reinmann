from pathlib import Path
import unittest

from flint import arb, arb_mat, ctx
from dual_rank_budget import dual_grid
from laboratory import complete_symmetric, interval, load_coefficients
from shift_two_correction import run


ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT/'research/certified_xi/pole_shift_two.json'
COEFFICIENTS = ROOT/'research/certified_xi/coefficients_120.json'


class ShiftTwoCorrectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 2048
        cls.result = run(BASE, COEFFICIENTS)
        cls.mu, _ = load_coefficients(COEFFICIENTS)
        cls.grid = dual_grid(cls.mu, max_rank=114, max_shift=2)

    def test_complete_bridge_and_uniform_margin(self):
        r = self.result
        self.assertEqual([row['rank'] for row in r['finite_bridge']], list(range(1, 90)))
        self.assertLess(arb(r['scaled_tail_error_upper']), arb('0.5'))
        self.assertLess(arb(r['successive_scaled_error_ratio_upper']), 1)
        self.assertLess(arb(r['weighted_tail_upper']), arb('1.5'))
        self.assertGreater(arb(r['weighted_global_lower']), arb('0.11'))

    def test_later_corrections_and_remaining_gain(self):
        beta = interval(self.result['limiting_slope'])
        for r in (90, 100, 113):
            correction = 2*self.grid[r, 2].log()-self.grid[r-1, 2].log()-self.grid[r+1, 2].log()
            self.assertGreater(correction, arb(1)/(2*(r+2)**2))
            self.assertLess(correction, arb(3)/(2*(r+2)**2))
            slope = (self.grid[r-1, 2]/self.grid[r, 2]).log()
            self.assertGreater(beta-slope, arb(1)/(2*(r+2)))
            self.assertLess(beta-slope, arb(3)/(2*(r+1)))

    def test_neighboring_B_identity_and_cumulative_sum(self):
        h = complete_symmetric([x/self.mu[0] for x in self.mu])
        def determinant(rank, shift):
            return arb_mat([[h[rank+i-j] if rank+i-j >= 0 else arb(0)
                             for j in range(shift)] for i in range(shift)]).det()
        for r in (4, 34, 90):
            B = [arb(r+m)/r*determinant(r+1, m)*determinant(r-1, m)/determinant(r, m)**2
                 for m in (1, 2, 3)]
            from_B = 2*B[1].log()-B[0].log()-B[2].log()
            direct = 2*self.grid[r, 2].log()-self.grid[r-1, 2].log()-self.grid[r+1, 2].log()
            self.assertTrue(from_B.overlaps(direct))
        first = -self.grid[1, 2].log()
        partial = sum((2*self.grid[r, 2].log()
                       -(self.grid[r-1, 2].log() if r > 1 else arb(0))
                       -self.grid[r+1, 2].log() for r in range(1, 91)), arb(0))
        slope_91 = (self.grid[90, 2]/self.grid[91, 2]).log()
        self.assertTrue(partial.overlaps(slope_91-first))
        self.assertLess(partial, interval(self.result['infinite_correction_sum']))

    def test_rejects_unresolved_and_invalid_heads(self):
        with self.assertRaises(ArithmeticError):
            run(BASE, COEFFICIENTS, head=80)
        with self.assertRaises(ValueError):
            run(BASE, COEFFICIENTS, head=0)


if __name__ == '__main__':
    unittest.main()
