import unittest
from fractions import Fraction
from flint import fmpq_mpoly_ctx
from gaussian_curvature import exact_identities, tail_budget


class GaussianCurvatureTests(unittest.TestCase):
    def test_exact_multivariate_and_lambert_identities(self):
        self.assertEqual(len(exact_identities()), 4)
        self.assertTrue(all(exact_identities().values()))

    def test_cubic_square_is_required_for_fourth_cumulant(self):
        ctx = fmpq_mpoly_ctx.get(('t', 'b'))
        t, b = ctx.gens()
        first = b * (t**3 + 3*t)
        second = b**2 * (t**6 + 15*t**4 + 45*t**2 + 15) / 2
        corrected = first + second - first**2 / 2
        omitted = first - first**2 / 2
        for _ in range(4):
            corrected = corrected.derivative('t')
            omitted = omitted.derivative('t')
        self.assertEqual(corrected, 108*b**2)
        self.assertNotEqual(omitted, corrected)

    def test_uniform_budget_endpoint_and_monotone_control(self):
        result = tail_budget()
        self.assertLess(Fraction(result['relative_error_upper']), Fraction(1, 2))
        self.assertLess(Fraction(result['smallness_upper']), Fraction(1, 10**100))
        self.assertLess(Fraction(102, 2000), Fraction(1, 2))
        self.assertLess(Fraction(tail_budget(2001)['relative_error_upper']),
                        Fraction(result['relative_error_upper']))

    def test_domain_is_not_silently_extended(self):
        for invalid in (0, 1999, 2000.0, True):
            with self.assertRaises(ValueError):
                tail_budget(invalid)


if __name__ == '__main__':
    unittest.main()
