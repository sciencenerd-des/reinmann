import json
import unittest
from flint import arb, ctx

from adjoint_fourier_certificate import sequence_bound
from full_cluster_certificate import OUT
from full_cluster_residual import generate, tail_column
from threshold_ground_gap import box


class FullClusterResidualTests(unittest.TestCase):
    def test_both_infinite_tail_formulas_dominate_known_omitted_modes(self):
        from pathlib import Path
        seq = json.loads(Path('research/prime_spectral/verification_2026_10_11_boundary_moment/matrix_C3_N32_M256.json').read_text())
        saved = json.loads((OUT/'C3_rank_four_full_residual.json').read_text())
        with ctx.workprec(512):
            b = [box(x) for x in seq['b_sequence']]
            B, P = sequence_bound(3), 32
            for sector in saved['sectors']:
                parity = sector['parity']
                for exact in sector['exact_columns']:
                    v = [arb(x) for x in exact]
                    values = []
                    for m in range(P+1, 257):
                        if parity == 'even':
                            value = arb(2).sqrt()*b[m]*v[0]/m+sum((
                                2*(m*b[m]-n*b[n])*v[n]/(m*m-n*n) for n in range(1,len(v))), arb(0))
                        else:
                            value = sum((2*(n*b[m]-m*b[n])*v[n-1]/(m*m-n*n)
                                         for n in range(1,len(v)+1)), arb(0))
                        values.append(value)
                    known = sum((x*x for x in values), arb(0)).sqrt()
                    self.assertTrue(known < tail_column(parity, v, b, P, B))

    def test_full_certificate_replay_and_nontrivial_angle(self):
        result = generate()
        with ctx.workprec(512):
            self.assertTrue(0 < box(result['projection_norm_distance_upper']) < arb('.531'))
            self.assertEqual([s['retained'] for s in result['sectors']], [2,2])
            self.assertTrue(box(result['orthonormalized_full_residual_HS_upper']) > 0)
            for sector in result['sectors']:
                self.assertTrue(box(sector['gram_lower']) > arb('.999'))
                self.assertTrue(all(box(c['infinite_residual_tail_norm_upper']) > 0 for c in sector['columns']))

    def test_invalid_tail_cutoff_rejected(self):
        with self.assertRaises(ValueError):
            tail_column('even', [arb(1),arb(1)], [arb(0),arb(1)], 1, arb(1))
        with self.assertRaises(ValueError):
            tail_column('unknown', [arb(1)], [arb(0),arb(1)], 2, arb(1))

    def test_zero_vector_has_zero_action_tail(self):
        for parity in ['even','odd']:
            self.assertTrue(tail_column(parity, [arb(0),arb(0)],
                                       [arb(0),arb(1),arb(1)], 4, arb(2)).is_zero())


if __name__ == '__main__':
    unittest.main()
