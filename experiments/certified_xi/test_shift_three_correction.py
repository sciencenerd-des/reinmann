"""Checks the shift-three pole-model correction against direct determinants."""
from __future__ import annotations

from pathlib import Path
import unittest

from flint import arb, ctx

from dual_rank_budget import dual_grid
from laboratory import load_coefficients
from shift_three_correction import load_base, log_error


BASE = Path(__file__).resolve().parents[2]/'research/certified_xi/pole_shift_three.json'
COEFFICIENTS = Path(__file__).resolve().parents[2]/'research/certified_xi/coefficients_200.json'


class ShiftThreeCorrectionTests(unittest.TestCase):
    def test_pole_log_error_contains_direct_ratios(self):
        with ctx.workprec(2048):
            base, amplitude, rate, terms = load_base(BASE, COEFFICIENTS)
            self.assertEqual(base['tail']['start_rank'], 82)
            mu, _ = load_coefficients(COEFFICIENTS)
            grid = dual_grid(mu, max_rank=151, max_shift=3)
            for rank in (82, 137, 150):
                residual = (grid[rank, 3].log()-amplitude.log()
                            -arb(rank+3).log()-rank*rate.log())
                self.assertLess(abs(residual), log_error(terms, rank))
            for rank in (1, 34, 136, 137, 149):
                previous = grid[rank-1, 3] if rank > 1 else arb(1)
                correction = (2*grid[rank, 3].log()-previous.log()
                              -grid[rank+1, 3].log())
                self.assertGreater(correction*(rank+3)**2, arb('0.1'))

    def test_error_rejects_rank_before_pole_domain(self):
        with self.assertRaises(ValueError):
            log_error([[]]*3, 3)


if __name__ == '__main__':
    unittest.main()
