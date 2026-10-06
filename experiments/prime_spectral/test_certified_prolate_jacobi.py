"""Regression checks for the infinite-tail prolate Sturm certificate."""
from fractions import Fraction
import unittest

from flint import arb

from certified_prolate_jacobi import jacobi_entries, run, sturm_count


class CertifiedProlateJacobiTests(unittest.TestCase):
    def test_sturm_count_on_exact_diagonal_matrix(self):
        diagonal, off_diagonal = [arb(2), arb(3)], [arb(0)]
        self.assertEqual(sturm_count(diagonal, off_diagonal, Fraction(0)), 0)
        self.assertEqual(sturm_count(diagonal, off_diagonal, Fraction(5, 2)), 1)
        self.assertEqual(sturm_count(diagonal, off_diagonal, Fraction(4)), 2)

    def test_cutoff_13_isolates_first_four_even_modes(self):
        result = run(13, 80, 1500)
        self.assertEqual(result['tail_floor'], 25760)
        self.assertTrue(all(Fraction(gap) > 0 for gap in result['consecutive_full_gap_lower']))
        finite = result['finite_eigenvalue_intervals']
        for j, approximate in enumerate((81, 405, 725, 1040)):
            self.assertLess(Fraction(finite[j]['hi']), approximate)

    def test_invalid_parameters_fail_closed(self):
        for cutoff, terms in ((1, 80), (13.0, 80), (13, 3), (13, True)):
            with self.subTest(cutoff=cutoff, terms=terms), self.assertRaises(ValueError):
                jacobi_entries(cutoff, terms)
        with self.assertRaises(ValueError):
            run(13, 80, 25760)


if __name__ == '__main__':
    unittest.main()
