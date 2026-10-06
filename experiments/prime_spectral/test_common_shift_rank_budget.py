"""Verify the common-parameter identity, including a misleading joint bound."""
from fractions import Fraction
import json
from pathlib import Path
import unittest
from flint import acb, arb, arb_mat, ctx
from certified_mode_comparison import box
from common_shift_rank_budget import chain_budget, conditional_ground_tail_upper, nonnegative, run, spectral_gram
from eigenvalue_response import _fourier_functional
from weil_eigenfamily import center_basis

DATA = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


class CommonShiftRankTests(unittest.TestCase):
    def test_conditional_ground_cauchy_bound_on_actual_nested_grounds(self):
        with ctx.workprec(256):
            matrices = [arb_mat([['0.5', '0.2'], ['0.2', 2]]),
                        arb_mat([['0.5', '0.2', '0.3'], ['0.2', 2, '0.05'], ['0.3', '0.05', 3]])]
            eigenvalues, vectors = [], []
            for matrix in matrices:
                values, basis = center_basis(matrix)
                self.assertLess(values[0], arb('0.5'))
                tail = arb_mat([[matrix[i, j] for j in range(1, matrix.nrows())]
                                for i in range(1, matrix.nrows())])
                tail_values, _ = center_basis(tail)
                self.assertGreater(tail_values[0]-values[0], 1)
                eigenvalues.append(values[0])
                vectors.append([basis[i, 0]/basis[0, 0] for i in range(matrix.nrows())])
            length = arb(13).log()
            bound = conditional_ground_tail_upper(length, arb(2)/5,
                                                  eigenvalues[0]-eigenvalues[1], arb('0.4'), arb(1))
            for z in (acb(4), acb(8), acb(0, arb(1)/4)):
                profiles = [sum((a*b for a, b in zip(v, _fourier_functional(n, length, z))), arb(0))
                            for v, n in zip(vectors, (1, 2))]
                self.assertLess(abs(profiles[1]-profiles[0]).upper(), bound)
            self.assertEqual(conditional_ground_tail_upper(length, arb(0), arb(0), arb(1), arb(1)), 0)
            with self.assertRaises(ValueError):
                conditional_ground_tail_upper(length, arb(0), arb(1), arb(1), arb(-1))

    def test_diagonal_chain_energies_and_signed_cancellation(self):
        with ctx.workprec(256):
            t = arb_mat([[1, 0, 0], [0, 2, 0], [0, 0, 4]])
            result = chain_budget(t, [[arb(1), arb(2), arb(4)],
                                     [arb(1), arb(1), arb(-1)]], [1, 2, 3])
            transfer = result['profile_transfers'][0]
            # New contributions are -2/2=-1 and -4*(-1)/4=+1.
            self.assertTrue(box(transfer['signed_cumulative_profile_change']).contains(0))
            self.assertTrue(box(transfer['signed_increment_intervals'][0]).contains(-1))
            self.assertTrue(box(transfer['signed_increment_intervals'][1]).contains(1))
            self.assertTrue(box(result['primal_energy_increment_intervals'][0]).contains(2))
            self.assertTrue(box(result['primal_energy_increment_intervals'][1]).contains(4))
            self.assertLess(Fraction(transfer['paired_increment_cauchy_sum_upper']), Fraction('2.00000001'))
            self.assertGreater(Fraction(transfer['joint_telescoped_cauchy_upper']), Fraction('2.12'))

    def test_nondiagonal_chain_matches_independent_direct_inversion(self):
        with ctx.workprec(256):
            t = arb_mat([[5, 1, -1], [1, 6, 2], [-1, 2, 8]])
            sources = [[arb(1), arb(2), arb(-3)], [arb(2), arb(-1), arb(4)]]
            result = chain_budget(t, sources, [1, 2, 3])
            cross = []
            for n in (1, 2, 3):
                block = arb_mat([[t[i, j] for j in range(n)] for i in range(n)])
                matrix = arb_mat([[s[i] for s in sources] for i in range(n)])
                direct = matrix.transpose()*block.solve(matrix)
                stored = result['source_gram_matrices'][n-1]
                for i in range(2):
                    for j in range(2):
                        self.assertTrue(box(stored[i][j]).overlaps(direct[i, j]))
                cross.append(direct[0, 1])
            self.assertTrue(box(result['profile_transfers'][0]['signed_cumulative_profile_change']).overlaps(cross[0]-cross[-1]))

    def test_zero_source_and_invalid_operators(self):
        with ctx.workprec(128):
            result = chain_budget(arb_mat([[1, 0], [0, 2]]), [[arb(0), arb(0)]]*2, [1, 2])
            self.assertEqual(Fraction(result['profile_transfers'][0]['joint_telescoped_cauchy_upper']), 0)
            self.assertIsNone(result['profile_transfers'][0]['joint_to_paired_ratio_lower'])
            with self.assertRaises(ArithmeticError):
                nonnegative(arb(-1))
            with self.assertRaises(ArithmeticError):
                spectral_gram(arb_mat([[-1, 0], [0, 2]]), [[arb(1), arb(1)]])
            with self.assertRaises(ValueError):
                spectral_gram(arb_mat([[1, 1], [0, 2]]), [[arb(1), arb(1)]])
            with self.assertRaises(ValueError):
                chain_budget(arb_mat([[1, 0], [0, 2]]), [[arb(1), arb(1)]], [2, 1])

    def test_saved_weil_chain_replays_and_joint_bound_is_worse(self):
        paths = [DATA/f'certified_weil_13_{n}.json' for n in (4, 8, 12)]
        result = run(paths)
        saved = json.loads((DATA/'common_shift_rank_budget_13_4_8_12.json').read_text())
        self.assertEqual(result, saved)
        for item in result['profile_transfers'].values():
            self.assertGreater(Fraction(item['joint_to_paired_ratio_lower']), 1000)
        item = result['profile_transfers']['real_4']
        self.assertGreater(Fraction(item['joint_telescoped_cauchy_upper']), 33064)
        self.assertLess(Fraction(item['paired_increment_cauchy_sum_upper']), 29)
        different = paths[:1]+[DATA/'certified_weil_17_8.json']
        with self.assertRaises(ValueError):
            run(different)


if __name__ == '__main__':
    unittest.main()
