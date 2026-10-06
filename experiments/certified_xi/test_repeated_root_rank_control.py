from fractions import Fraction
import math
import unittest

from flint import arb, ctx, fmpq, fmpq_mat
from compensated_rank_tail import compensated_budget
from rank_tail_bootstrap import tail_budget
from repeated_root_rank_control import control, normalized_minor


class RepeatedRootRankControlTests(unittest.TestCase):
    def test_closed_minors_against_exact_determinants(self):
        for N in (4, 6):
            def coefficient(n):
                return fmpq(math.comb(N, n), N**n) if 0 <= n <= N else fmpq(0)
            for r in range(1, 6):
                for m in range(N+2):
                    determinant = fmpq_mat([[coefficient(m+i-j) for j in range(r)] for i in range(r)]).det()
                    prefactor = math.prod((Fraction(math.factorial(j), math.factorial(m+j)) for j in range(r)), start=Fraction(1))
                    expected = normalized_minor(N, r, m)*prefactor
                    self.assertEqual(determinant, fmpq(expected.numerator, expected.denominator))

    def test_exact_condensation_and_correction_product(self):
        N = 6
        for r in range(1, 10):
            for m in range(1, N+1):
                A = lambda rank, shift: normalized_minor(N, rank, shift)
                self.assertEqual(r*A(r+1, m)*A(r-1, m),
                                 (m+r)*A(r, m)**2-m*A(r, m-1)*A(r, m+1))
        for steps in (0, 1, 20, 100):
            result = control(6, 3, 4, steps)
            self.assertEqual(Fraction(result['exact_prefix_slope_exponential']), Fraction(7+steps, 6+steps))

    def test_bootstraps_reject_finite_control_heads(self):
        with ctx.workprec(512):
            for r in (2, 10, 100, 1000):
                d = (1+arb(r)/3).log()
                v = (arb(r+3)/(r+2)).log()
                self.assertEqual(tail_budget(d, v)['status'], 'unresolved')
                self.assertEqual(compensated_budget(r, 3, d, v)['status'], 'unresolved')

    def test_domain_rejection(self):
        for N, m in ((3, 2), (6, 1), (6, 5)):
            with self.assertRaises(ValueError):
                control(N, m)
        with self.assertRaises(ValueError):
            normalized_minor(0, 1, 1)


if __name__ == '__main__':
    unittest.main()
