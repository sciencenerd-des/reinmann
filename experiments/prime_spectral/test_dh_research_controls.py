import json
from pathlib import Path
import unittest

from flint import acb, arb, ctx

from certified_weil import inertia
from davenport_heilbronn_control import dirichlet_coefficients, log_derivative_coefficients
from dh_toeplitz_scan import coefficients, solid_minor
from dh_weil_certificate import geometric_entry, negative_ldl_witness
from dh_zero_and_gates import zero_certificate
from threshold_ground_gap import box


class DHResearchControls(unittest.TestCase):
    def test_solid_minor_detects_positive_coefficient_nonreal_root_polynomial(self):
        # 1+z+z^2 has positive coefficients but a negative order-three minor.
        mu = [arb(1), arb(1), arb(1), arb(0), arb(0)]
        self.assertTrue(solid_minor(mu, 3, 1) < 0)
        self.assertTrue(solid_minor(mu, 2, 1).is_zero())

    def test_DH_normalization_and_small_minors(self):
        with ctx.workprec(512):
            mu = coefficients(10)
            self.assertTrue(mu[0].contains(1))
            self.assertTrue(all(x > 0 for x in mu))
            for rank in range(1, 5):
                for shift in range(1, 6):
                    self.assertTrue(solid_minor(mu, rank, shift) > 0)

    def test_divided_difference_assembly_against_direct_DH_integrals(self):
        with ctx.workprec(512):
            C = 7
            L = arb(C).log()
            c = log_derivative_coefficients(dirichlet_coefficients(C))
            b = [arb(0)]+[n*geometric_entry(n, 0, L, c, C) for n in range(1, 4)]
            for m, n in [(1, 2), (1, 3), (2, 3)]:
                d = geometric_entry(m, n, L, c, C)
                e = geometric_entry(m, -n, L, c, C)
                self.assertTrue((d+e).overlaps(2*(n*b[n]-m*b[m])/(n*n-m*m)))
                self.assertTrue((d-e).overlaps(2*(m*b[n]-n*b[m])/(n*n-m*m)))

    def test_gamma_change_kernel_matches_independent_digamma_transform(self):
        # Fourier transform of 1/(2cosh(y/2)) on R is pi/cosh(pi*t).
        with ctx.workprec(512):
            for t in [0, 1, 3]:
                lhs = (acb('3/4', arb(t)/2).digamma()
                       -acb('1/4', arb(t)/2).digamma()).real
                self.assertTrue(lhs.overlaps(arb.pi()/(arb.pi()*t).cosh()))

    def test_saved_negative_witness_recomputed_from_full_geometric_matrix(self):
        path = Path('research/prime_spectral/verification_2026_10_12_remaining/dh_weil_C31_N60.json')
        data = json.loads(path.read_text())
        with ctx.workprec(768):
            for s in data['sectors']:
                A = [[box(x) for x in row] for row in s['matrix']]
                if s['parity'] == 'even':
                    self.assertEqual(s['first_negative_pivot_index'], 60)
                    self.assertEqual(inertia([row[:60] for row in A[:60]])[0], 0)
                    v = list(map(arb, s['exact_trial_coefficients']))
                    q = sum((v[i]*A[i][j]*v[j] for i in range(61)
                             for j in range(61)), arb(0))/sum((x*x for x in v), arb(0))
                    self.assertTrue(q < arb('-15e-32'))
                else:
                    self.assertEqual(inertia(A)[0], 0)

    def test_negative_LDL_witness_not_just_a_negative_diagonal(self):
        A = [[arb(1), arb(2)], [arb(2), arb(1)]]
        data = negative_ldl_witness(A)
        self.assertEqual(data['first_negative_pivot_index'], 1)
        self.assertTrue(box(data['normalized_full_form']) < 0)

    def test_off_line_zero_Rouche_certificate_replay(self):
        data = zero_certificate()
        with ctx.workprec(768):
            self.assertTrue(box(data['rouche_left']) < box(data['rouche_right']))
            self.assertTrue(box(data['real_part_above_half']) > arb('.3085'))

    def test_DH_finite_gates_survive_the_negative_control(self):
        data = json.loads(Path(
            'research/prime_spectral/verification_2026_10_12_remaining/dh_zero_and_finite_gates.json'
        ).read_text())['finite_gates']
        with ctx.workprec(768):
            self.assertTrue(box(data['lowest_even']) > 0)
            self.assertTrue(box(data['ground_gap']) > 0)
            self.assertTrue(all(box(x) > 0 for x in data['boundary_kernel_positive_pivots']))


if __name__ == '__main__':
    unittest.main()
