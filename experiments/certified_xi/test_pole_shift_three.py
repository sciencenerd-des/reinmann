"""Five-pole determinant and normalized-ratio regression checks."""
from __future__ import annotations

from itertools import combinations
import math
import unittest

from flint import arb, arb_mat, ctx

from pole_shift_three import tail_bounds
from pole_shift_two import determinant_error_terms, pole_weight


class PoleShiftThreeTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512
        self.rates = [arb(1)/2**(j+1) for j in range(5)]
        self.amplitudes = [arb((-1)**j*(j+1)) for j in range(5)]

    def moment(self, n):
        return sum((a*x**n for a, x in zip(self.amplitudes, self.rates)), arb(0))

    def test_five_pole_formula_through_size_four(self):
        rank = 8
        for size in range(1, 5):
            direct = arb_mat([[self.moment(rank+i-j) for j in range(size)]
                              for i in range(size)]).det()
            expansion = sum((pole_weight(self.amplitudes, self.rates, subset)
                             *math.prod(self.rates[i] for i in subset)**rank
                             for subset in combinations(range(5), size)), arb(0))
            self.assertTrue(direct.overlaps(expansion))

    def test_four_by_four_residual_bound(self):
        M, radius, rank = arb('0.01'), arb(64), 20
        weight, scale, terms = determinant_error_terms(
            4, self.amplitudes, self.rates, M, radius)
        perturbed = lambda n: self.moment(n)+(-1 if n % 3 else 1)*M*radius**(-n)
        actual = arb_mat([[perturbed(rank+i-j) for j in range(4)]
                          for i in range(4)]).det()
        bound = weight*scale**rank*sum((c*q**rank for c, q in terms), arb(0))
        self.assertLess(abs(actual-weight*scale**rank), bound)
        self.assertTrue(all(0 < q < 1 for _, q in terms))

    def test_ratio_tail_uses_decreasing_geometric_errors(self):
        models = [determinant_error_terms(size, self.amplitudes, self.rates,
                                          arb('0.01'), arb(64))
                  for size in range(1, 5)]
        passed, errors, ratio, next_factor = tail_bounds(100, models, self.rates)
        self.assertTrue(passed)
        self.assertTrue(all(0 <= error < 1 for error in errors))
        self.assertLess(ratio, 1)
        self.assertLess(next_factor, 1)
        with self.assertRaises(ValueError):
            tail_bounds(0, models, self.rates)


if __name__ == '__main__':
    unittest.main()
