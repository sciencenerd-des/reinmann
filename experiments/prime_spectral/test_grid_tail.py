import unittest
from flint import arb, acb, ctx
from certified_weil import run
from grid_tail import disk_error_bound, imaginary_log_lower, quotient_polynomial_profile
from quotient_operator import build, fourier_profile


class GridTailTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_complex_disk_and_imaginary_bounds(self):
        L, N = arb(13).log(), 8
        def tail(z):
            x = z*L/(2*arb.pi())
            finite = acb(1)
            for k in range(1, N+1):
                finite *= 1-(x/k)**2
            return (z*L/2).sinc()/finite
        for z in (acb('0.5', '0.7'), acb(0, 2), acb('1.5', '-0.1')):
            self.assertLess(abs(tail(z)-1), disk_error_bound(L, N, 2))
        for y in (arb('0.5'), arb(2), arb(5)):
            value = tail(acb(0, y))
            self.assertTrue(value.imag.contains(0))
            self.assertGreater(value.real.log(), imaginary_log_lower(L, N, y))

    def test_prime_profile_obeys_lower_bound(self):
        certificate = run(13, 2)
        c, L, B, _ = build(certificate)
        self.assertTrue(quotient_polynomial_profile(B, 0).contains(1))
        for y in (arb(1), arb(3)):
            value = fourier_profile(c, L, acb(0, y))
            self.assertTrue(value.imag.contains(0))
            self.assertGreater(value.real.log(), imaginary_log_lower(L, 2, y))
        z = acb('0.7', '1.1')
        grid_factor = (z*L/2).sinc()
        for k in (1, 2):
            grid_factor /= 1-(z*L/(2*arb.pi()*k))**2
        self.assertTrue((fourier_profile(c, L, z)
                         -quotient_polynomial_profile(B, z)*grid_factor).contains(0))

    def test_scaling_diagnostics_do_not_claim_convergence(self):
        # Samples validate formulas, not the infinite-path theorem.
        critical = disk_error_bound(100, 10000, 1)
        finer = disk_error_bound(100, 1000000, 1)
        self.assertGreater(critical, arb('0.025'))
        self.assertLess(finer, arb('0.000254'))
        self.assertTrue(disk_error_bound(1, 1, 0).is_zero())

    def test_invalid_parameters(self):
        with self.assertRaises(ValueError):
            quotient_polynomial_profile([[1, 2]], 0)
        with self.assertRaises(ArithmeticError):
            quotient_polynomial_profile([[0]], 1)
        for L, N, R in ((0, 1, 1), (1, 0, 1), (1, True, 1), (1, 1, -1)):
            with self.assertRaises(ValueError):
                disk_error_bound(L, N, R)
            with self.assertRaises(ValueError):
                imaginary_log_lower(L, N, R)


if __name__ == '__main__':
    unittest.main()
