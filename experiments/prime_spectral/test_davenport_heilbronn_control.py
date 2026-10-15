import unittest
from flint import arb, ctx
from davenport_heilbronn_control import (dirichlet_coefficients, generate, kappa,
                                        log_derivative_coefficients)


class DavenportHeilbronnTests(unittest.TestCase):
    def test_independent_radical_normalization(self):
        with ctx.workprec(512):
            phi = (1+arb(5).sqrt())/2
            self.assertTrue(kappa().overlaps((1+phi*phi).sqrt()-phi))
            self.assertTrue(arb('0.28407') < kappa() < arb('0.28409'))

    def test_log_derivative_convolution_identity(self):
        with ctx.workprec(512):
            a = dirichlet_coefficients(32)
            c = log_derivative_coefficients(a)
            for n in range(2, 33):
                lhs = sum((c[d]*a[n//d] for d in range(1, n+1) if n % d == 0), arb(0))
                self.assertTrue(lhs.overlaps(a[n]*arb(n).log()))

    def test_closed_form_first_obstructions_and_zeta_control(self):
        d = generate()
        self.assertEqual(d['first_negative_coefficient'], 3)
        self.assertEqual(d['first_non_prime_power_nonzero_coefficient'], 6)

    def test_reject_unnormalized_series(self):
        with self.assertRaises(ValueError):
            log_derivative_coefficients([arb(0), arb(2)])


if __name__ == '__main__':
    unittest.main()
