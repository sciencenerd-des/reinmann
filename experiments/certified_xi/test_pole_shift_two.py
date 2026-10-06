import itertools
import math
import unittest
from flint import arb, arb_mat, ctx
from pole_shift_two import pole_weight, determinant_error_terms


class PoleShiftTwoTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512
        self.rates = [arb(1)/2, arb(1)/4, arb(1)/8]
        self.amplitudes = [arb(1), arb(-2), arb(3)]

    def moment(self, n):
        return sum((a*x**n for a,x in zip(self.amplitudes, self.rates)), arb(0))

    def test_exact_spectral_determinant_formula(self):
        for size in (1,2,3):
            r = 5
            direct = arb_mat([[self.moment(r+i-j) for j in range(size)] for i in range(size)]).det()
            expansion = sum((pole_weight(self.amplitudes, self.rates, subset)
                             *math.prod(self.rates[i] for i in subset)**r
                             for subset in itertools.combinations(range(3), size)), arb(0))
            self.assertTrue(direct.overlaps(expansion))

    def test_residual_determinant_envelope(self):
        M, radius = arb('0.01'), arb(12)
        for size in (1,2,3):
            weight, scale, terms = determinant_error_terms(size, self.amplitudes, self.rates, M, radius)
            for r in (3,10,30):
                # Non-geometric signs exercise the residual-column bound.
                h = lambda n: self.moment(n)+(-1 if n % 3 else 1)*M*radius**(-n)
                actual = arb_mat([[h(r+i-j) for j in range(size)] for i in range(size)]).det()
                bound = weight*scale**r*sum((c*q**r for c,q in terms), arb(0))
                self.assertLess(abs(actual-weight*scale**r), bound)

    def test_repeated_pole_cancellation_is_necessary(self):
        # An entrywise leading-alpha bound would grow relative to D3.
        naive_ratio = self.rates[0]/(self.rates[1]*self.rates[2]*12)
        self.assertGreater(naive_ratio, 1)
        _, _, terms = determinant_error_terms(3, self.amplitudes, self.rates, arb(1), arb(12))
        self.assertTrue(all(q < 1 for _,q in terms))

    def test_fail_closed_without_pole_separation(self):
        with self.assertRaises(ArithmeticError):
            determinant_error_terms(3, self.amplitudes, self.rates, arb(1), arb(8))
        with self.assertRaises(ValueError):
            determinant_error_terms(4, self.amplitudes, self.rates, arb(1), arb(12))


if __name__ == '__main__':
    unittest.main()
