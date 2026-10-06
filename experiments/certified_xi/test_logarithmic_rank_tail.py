from fractions import Fraction
import unittest

from logarithmic_rank_tail import logarithmic_head


class LogarithmicRankTailTests(unittest.TestCase):
    def test_exact_head_equality_is_allowed(self):
        result = logarithmic_head(4, 4, Fraction(1, 32), Fraction(1, 28))
        self.assertEqual(result['status'], 'conditional_logarithmic_tail_pass')
        self.assertEqual(result['amplitude_margin'], '0')
        self.assertEqual(result['slope_cross_product_margin'], '0')

    def test_each_failed_head_condition_is_unresolved(self):
        self.assertEqual(logarithmic_head(4, 4, Fraction(1, 31), 1)['status'], 'unresolved')
        self.assertEqual(logarithmic_head(4, 4, Fraction(1, 32), Fraction(1, 32))['status'], 'unresolved')

    def test_exact_one_step_barrier_inequality(self):
        for x in range(3, 30):
            for beta in (Fraction(0), Fraction(1, 2), Fraction(1)):
                # Exponential of baseline+2log(1-beta/x^2), compared
                # with exp(Delta2 log x). This checks an exact inequality.
                correction_lower = Fraction(x*x, x*x-1)*(1-beta/(x*x))**2
                barrier_correction = Fraction(x*x-1, x*x)
                self.assertGreaterEqual(correction_lower, barrier_correction)

    def test_repeated_root_control_still_fails_amplitude(self):
        # Retaining the positive factorial baseline alone does not recover
        # the neighboring cancellation in the repeated-root example.
        for r in (2, 10, 100):
            result = logarithmic_head(r, 3, Fraction(3, r+3), Fraction(3, r+2))
            self.assertEqual(result['status'], 'unresolved')
            self.assertLess(Fraction(result['amplitude_margin']), 0)

    def test_domains(self):
        for r, m, q, p in ((0, 2, 1, 1), (1, 1, 1, 1), (1, 2, 0, 1), (1, 2, 1, -1)):
            with self.assertRaises(ValueError):
                logarithmic_head(r, m, q, p)


if __name__ == '__main__':
    unittest.main()
