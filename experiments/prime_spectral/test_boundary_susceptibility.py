"""Check the constrained eigenvalue bracket and its spectral identity."""
from fractions import Fraction
from pathlib import Path
import unittest

from flint import arb, ctx

from boundary_susceptibility import restricted_first, run


class BoundarySusceptibilityTests(unittest.TestCase):
    def test_exact_two_mode_secular_control(self):
        # A=diag(1,4), ell=(1,2): ker ell is spanned by (-2,1).
        with ctx.workprec(256):
            lo, hi = restricted_first([[arb(1), arb(0)], [arb(0), arb(4)]],
                                      [arb(1), arb(2)],
                                      (Fraction(1), Fraction(1)),
                                      (Fraction(4), Fraction(4)), 70)
        self.assertLess(lo, Fraction(8, 5))
        self.assertGreater(hi, Fraction(8, 5))
        self.assertLess(hi-lo, Fraction(1, 10**15))
        self.assertEqual(Fraction(1) / (Fraction(8, 5)-1),
                         Fraction(4) / (4-Fraction(8, 5)))

    def test_certified_weil_boundary_margin(self):
        root = Path(__file__).resolve().parents[2]
        result = run(root / 'research/prime_spectral/certified_weil_13_4.json')
        margin = result['boundary_zero_margin']
        susceptibility = result['susceptibility']
        self.assertGreater(Fraction(margin['lo']), 0)
        self.assertLess(Fraction(susceptibility['lo']), Fraction(74))
        self.assertGreater(Fraction(susceptibility['hi']), Fraction(73))


if __name__ == '__main__':
    unittest.main()
