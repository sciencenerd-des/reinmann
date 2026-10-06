import json
from pathlib import Path
import unittest
from flint import arb, acb, ctx
from eigenvector_coefficients import direct_coefficients, compare
from quotient_operator import build
from grid_tail import quotient_polynomial_profile
from certified_mode_comparison import box


class EigenvectorCoefficientTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_exact_small_vector_and_scaling(self):
        # c=(-1/2, 2, -1/2), sum c=1 and L=2*pi: R=1-z^2/2.
        c = [arb(2), -arb(1)/2]
        result = direct_coefficients(c, 2*arb.pi(), 1)
        self.assertTrue((result[1]+arb(1)/2).contains(0))
        scaled = direct_coefficients([7*x for x in c], 2*arb.pi(), 1)
        self.assertTrue((scaled[1]-result[1]).contains(0))

    def test_full_polynomial_against_actual_determinant(self):
        root = Path(__file__).resolve().parents[2]
        for N in (4, 8):
            certificate = json.loads((root/f'research/prime_spectral/certified_weil_13_{N}.json').read_text())
            c, L, B, _ = build(certificate)
            coefficients = direct_coefficients(c[N:], L, N)
            for z in (acb('0.6', '0.9'), acb(0, 1)):
                polynomial = sum((value*z**(2*k) for k, value in enumerate(coefficients)), acb(0))
                self.assertTrue((polynomial-quotient_polynomial_profile(B, z)).contains(0))

    def test_prime_trace_comparison_and_width_improvement(self):
        root = Path(__file__).resolve().parents[2]
        certificates = [json.loads((root/f'research/prime_spectral/certified_weil_13_{N}.json').read_text()) for N in (4, 8)]
        result = compare(*certificates)
        self.assertLess(arb(result['unit_disk_difference_upper']), arb('0.0033'))
        row = result['rows'][1]
        direct, old = box(row['spectral_sum']), box(row['inverse_trace_spectral_sum'])
        self.assertTrue(direct.overlaps(old))
        self.assertLess(direct.rad(), old.rad()/10**10)

    def test_invalid_domains(self):
        for c, L, K in (([1], 1, 1), ([0, 1], 1, 1), ([1, 1], 0, 1), ([1, 1], 1, 2)):
            with self.assertRaises(ValueError):
                direct_coefficients(c, L, K)


if __name__ == '__main__':
    unittest.main()
