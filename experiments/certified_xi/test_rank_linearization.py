import math
import unittest

from flint import fmpq, fmpq_mat, fmpq_poly
from rank_linearization import coefficient_log_tangent, mode, second_difference


class RankLinearizationTests(unittest.TestCase):
    def test_complete_polynomial_modes(self):
        x = fmpq_poly([0, 1])
        for N in range(2, 13):
            for n in range(2, N+1):
                p, y = mode(N, n)
                self.assertEqual(-second_difference(x*(N-x)*p), n*(n-1)*p)
                self.assertEqual(x*(x+N)*second_difference(y), n*(n-1)*y)
                self.assertEqual(y(0), 0)
                self.assertEqual(y(1), 1)
                self.assertEqual(p.degree(), n-2)
                self.assertEqual(y.degree(), n)
                self.assertGreater(y(100), y(99))

    def test_common_shift_mode_grows_quadratically(self):
        x = fmpq_poly([0, 1])
        for N in (2, 4, 20):
            p, y = mode(N, 2)
            self.assertEqual(p, 1)
            self.assertEqual(y, x*(x+N)/(N+1))

    def test_modes_are_actual_determinant_derivatives(self):
        for N in (4, 6):
            for n in (2, N):
                p, y = mode(N, n)
                b = coefficient_log_tangent(N, p)
                a = [fmpq(math.comb(N, k), N**k) for k in range(N+1)]
                def log_derivative(rank, shift):
                    def entry(k, differentiated=False):
                        return (a[k]*b[k] if differentiated else a[k]) if 0 <= k <= N else fmpq(0)
                    matrix = fmpq_mat([[entry(shift+i-j) for j in range(rank)] for i in range(rank)])
                    tangent = fmpq_mat([[entry(shift+i-j, True) for j in range(rank)] for i in range(rank)])
                    product = matrix.inv()*tangent
                    return sum((product[k, k] for k in range(rank)), fmpq(0))
                for r in (1, 2, 4, 6):
                    slopes = [log_derivative(r, m) for m in range(N+1)]
                    for m in range(1, N):
                        actual = 2*slopes[m]-slopes[m-1]-slopes[m+1]
                        self.assertEqual(actual, p(m)*y(r))

    def test_invalid_mode(self):
        for N, n in ((1, 2), (4, 1), (4, 5), (4, 2.0)):
            with self.assertRaises(ValueError):
                mode(N, n)


if __name__ == '__main__':
    unittest.main()
