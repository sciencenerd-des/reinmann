from fractions import Fraction as F
import unittest

from rank_tube_width import rational_width_obstruction, width_forcing_ratio
from two_sided_rank_tube import Envelope, local_tube


class RankTubeWidthTests(unittest.TestCase):
    def test_exact_control_has_no_obstruction(self):
        triple = [Envelope(6-m, 6-m) for m in (1, 2, 3)]
        result = rational_width_obstruction(4, 2, triple, triple)
        self.assertEqual(result['status'], 'no_width_obstruction_not_a_tube_certificate')
        self.assertEqual(F(result['width_acceleration_exp_lower']), 1)
        self.assertEqual(local_tube(4, 2, triple, triple)['status'], 'conditional_two_sided_tube_pass')

    def test_nonzero_central_or_neighbor_width_is_incompatible(self):
        upper = [Envelope(6-m, 6-m) for m in (1, 2, 3)]
        for index in range(3):
            lower = list(upper)
            e = lower[index]
            lower[index] = Envelope(e.amplitude*F(99, 100), e.offset)
            result = rational_width_obstruction(4, 2, lower, upper)
            self.assertEqual(result['status'], 'incompatible_bounded_width_comparison')
            self.assertGreater(F(result['width_acceleration_exp_lower']), 1)
            self.assertEqual(local_tube(4, 2, lower, upper)['status'], 'unresolved')

    def test_touching_at_head_is_not_identical(self):
        lower = [Envelope(1, 2)]*3
        upper = [Envelope(F(7, 6), 3)]*3
        self.assertEqual(width_forcing_ratio(4, 2, [e.value(4) for e in lower],
                                             [e.value(4) for e in upper]), 1)
        self.assertEqual(rational_width_obstruction(4, 2, lower, upper)['status'],
                         'incompatible_bounded_width_comparison')

    def test_exact_forcing_and_invalid_inputs(self):
        lo, hi = [F(1, 4)]*3, [F(1, 2)]*3
        expected = F(19, 18)*F(11, 10)**2*F(25, 22)
        self.assertEqual(width_forcing_ratio(4, 2, lo, hi), expected)
        with self.assertRaises(ValueError):
            width_forcing_ratio(4, 2, hi, lo)
        with self.assertRaises(ValueError):
            width_forcing_ratio(0, 2, lo, hi)
        with self.assertRaises(ValueError):
            rational_width_obstruction(4, 2, [Envelope(2, 2)]*3,
                                      [Envelope(1, 2)]*3)


if __name__ == '__main__':
    unittest.main()
