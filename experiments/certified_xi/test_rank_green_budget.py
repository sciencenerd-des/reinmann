from fractions import Fraction as F
import unittest

from rank_green_budget import budget, green_value, solve_prefix


class RankGreenBudgetTests(unittest.TestCase):
    def test_green_formula_matches_direct_recurrence(self):
        sources = [F((-1)**r, r*r+1) for r in range(1, 40)]
        values = solve_prefix(F(2, 7), sources)
        for r in range(1, 41):
            self.assertEqual(values[r], green_value(r, F(2, 7), sources))

    def test_saturated_bounded_response(self):
        result = budget(F(1, 2), [], 1, 1)
        self.assertEqual(result['status'], 'conditional_all_rank_bounded_scalar_response')
        values = solve_prefix(F(1, 2), [-F(2, r*(r+2)) for r in range(1, 100)])
        for r, value in enumerate(values):
            self.assertEqual(value, F(r, r+1))

    def test_signed_prefix_and_exact_tail_balance(self):
        prefix = [F(1, 3), -F(1, 8), F(1, 15)]
        tail, bound = F(1, 2), F(1)
        start = len(prefix)+1
        initial = tail/F(start*(start+1))-sum((f/F(r+1) for r, f in enumerate(prefix, 1)), F(0))
        self.assertEqual(budget(initial, prefix, tail, bound)['growing_amplitude'], '0')
        sources = prefix+[-2*tail/F(r*(r+2)) for r in range(start, 100)]
        for r, value in enumerate(solve_prefix(initial, sources)):
            self.assertLessEqual(abs(value), bound*F(r, r+1))
        perturbation = F(1, 10**12)
        failed = budget(initial+perturbation, prefix, tail, bound)
        self.assertEqual(failed['status'], 'nonzero_growing_mode_in_scalar_control')
        self.assertEqual(F(failed['growing_amplitude']), perturbation)
        regular = solve_prefix(initial, sources)
        shifted = solve_prefix(initial+perturbation, sources)
        self.assertEqual(shifted[100]-regular[100], perturbation*F(100*102, 3))

    def test_invalid_forcing_and_rank(self):
        with self.assertRaises(ValueError):
            budget(0, [1], 0, 1)
        with self.assertRaises(ValueError):
            budget(0, [], 2, 1)
        with self.assertRaises(ValueError):
            green_value(5, 0, [0])


if __name__ == '__main__':
    unittest.main()
