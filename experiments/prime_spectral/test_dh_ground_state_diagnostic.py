import unittest

import mpmath as mp
from flint import arb, ctx

from certified_weil import certified_matrix
from dh_ground_state_diagnostic import (dh_candidate, fourier_even, real_roots,
                                        spectrum, zeta_assemble)
from davenport_heilbronn_control import kappa


class DHSpectralDiagnosticTests(unittest.TestCase):
    def test_fourier_basis_integrals_including_removable_poles(self):
        with mp.workdps(60):
            length = mp.log(13)
            for n in range(4):
                coefficients = [mp.mpf(0)]*4
                coefficients[n] = mp.mpf(1)
                def basis(t):
                    if n == 0:
                        return 1/mp.sqrt(length)
                    return mp.sqrt(2/length)*mp.cos(2*mp.pi*n*(t+length/2)/length)
                for z in (mp.mpf(0), mp.mpf('1.3'), 2*mp.pi*n/length):
                    direct = mp.quad(lambda t: basis(t)*mp.cos(z*t),
                                     [-length/2, 0, length/2])
                    self.assertLess(abs(fourier_even(coefficients, length, z)-direct),
                                    mp.mpf('1e-55'))

    def test_constant_transform_roots(self):
        with mp.workdps(50):
            roots = real_roots([mp.mpf(1)], mp.mpf(2), maximum=10)
            self.assertEqual(len(roots), 3)
            for n, root in enumerate(roots, 1):
                self.assertLess(abs(root-n*mp.pi), mp.mpf('1e-28'))

    def test_zeta_parity_recurrence_against_direct_integrals(self):
        with ctx.workprec(512):
            _, direct_even, direct_odd = certified_matrix(7, 3)
            even, odd = zeta_assemble(7, 3, 512)
            for lhs, rhs in ((even, direct_even), (odd, direct_odd)):
                for i in range(len(lhs)):
                    for j in range(len(lhs)):
                        self.assertTrue(lhs[i][j].overlaps(rhs[i][j]))

    def test_midpoint_eigenvector_selects_lowest_not_smallest_absolute_value(self):
        with ctx.workprec(256), mp.workprec(256):
            values, vector = spectrum([[arb(-2), arb(0)], [arb(0), arb(1)]])
            self.assertEqual(values, [-2, 1])
            self.assertEqual(abs(vector[0]), 1)

    def test_DH_gaussian_reflection_and_odd_gamma_convention(self):
        # Independent Poisson/theta check for the limiting candidate; using
        # zeta's even Gaussian or omitting conductor 5 fails this check.
        with ctx.workprec(256), mp.workdps(60):
            k = mp.mpf(kappa().mid().str(65, radius=False))
            a = [0, 1, k, -k, -1]
            def theta(t):
                u = mp.exp(t)
                return u**mp.mpf('1.5')*mp.fsum(
                    a[n % 5]*n*mp.exp(-mp.pi*n*n*u*u/5)
                    for n in range(1, 101))
            for t in (mp.mpf('0.2'), mp.mpf('0.7')):
                self.assertLess(abs(theta(t)-theta(-t)), mp.mpf('1e-55'))
            s = mp.mpc(2, '.3')
            integral = mp.quad(lambda x: x**s*mp.exp(-mp.pi*x*x/5), [0, 1, mp.inf])
            gamma = (mp.mpf('0.5')*(5/mp.pi)**((s+1)/2)*mp.gamma((s+1)/2))
            self.assertLess(abs(integral-gamma), mp.mpf('1e-55'))

    def test_DH_candidate_projection_refinement(self):
        with ctx.workprec(256):
            a = dh_candidate(14, 16, terms=64, nodes=64)
            b = dh_candidate(14, 16, terms=96, nodes=96)
            c = dh_candidate(20, 16, terms=96, nodes=96)
        self.assertLess(max(abs(x-y) for x, y in zip(
            a['unit_coefficients'], b['unit_coefficients'])), 1e-12)
        self.assertLess(abs(a['reflection_defect_ratio']-b['reflection_defect_ratio']), 1e-12)
        self.assertLess(c['reflection_defect_ratio'], b['reflection_defect_ratio']/100)
        self.assertGreater(b['projected_l2_fraction'], .999)


if __name__ == '__main__':
    unittest.main()
