"""Check signed deflation against direct Schur solves and exact examples."""
from fractions import Fraction
import json
from pathlib import Path
import unittest
from flint import acb, arb, arb_mat, ctx
from certified_mode_comparison import box
from deflated_rank_response import compare, deflate, run
from eigenvalue_response import _fourier_functional
from ground_schur import origin_schur_vector

DATA = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


class DeflatedRankTests(unittest.TestCase):
    def test_replay_and_independent_ground_profile_differences(self):
        for small, large in ((4, 8), (8, 12)):
            with self.subTest(pair=(small, large)):
                paths = [DATA / f'certified_weil_13_{n}.json' for n in (small, large)]
                result = run(*paths)
                saved = json.loads((DATA / f'deflated_rank_response_13_{small}_{large}.json').read_text())
                self.assertEqual(result, saved)
                self.assertGreater(Fraction(result['complementary_spectral_lower']), 0)
                self.assertEqual(len(result['constrained_spectrum'])-result['deflated_modes'], large-2)
                with ctx.workprec(1024):
                    vectors = [origin_schur_vector(json.loads(p.read_text()))[0] for p in paths]
                    for label, z in (('real_4', acb(4)), ('real_8', acb(8)), ('imag_1', acb(0, 1))):
                        pairings = [sum((x*y for x, y in zip(vector, _fourier_functional(n, arb(13).log(), z))), arb(0))
                                    for vector, n in zip(vectors, (small, large))]
                        direct = pairings[1]-pairings[0]
                        profile = result['profile_change'][label]
                        self.assertTrue(box(profile['deflated_profile_change_interval']).contains(direct))
                        self.assertTrue(box(profile['full_spectral_profile_change_check']).overlaps(direct))
                        self.assertGreater(Fraction(profile['unseparated_energy_profile_upper']) /
                                           Fraction(profile['deflated_absolute_profile_upper']), 60)

    def test_signed_low_pairings_cancel_before_absolute_values(self):
        with ctx.workprec(256):
            operator = arb_mat([[1, 0, 0], [0, 2, 0], [0, 0, 10]])
            result = deflate(operator, [arb(1), arb(2), arb(1)], arb(31)/10, 2,
                             {'cancel': [arb(1), arb(-1), arb(0)]})
            profile = result['profile_change']['cancel']
            self.assertTrue(box(profile['deflated_profile_change_interval']).contains(0))
            self.assertLess(Fraction(profile['deflated_absolute_profile_upper']), Fraction('1e-60'))
            self.assertGreater(Fraction(result['complementary_energy_upper_used']), Fraction(9, 100))

    def test_norm_bound_and_count_zero(self):
        with ctx.workprec(256):
            operator = arb_mat([[1, 0, 0], [0, 4, 0], [0, 0, 9]])
            for count in (0, 1, 2):
                result = deflate(operator, [arb(1), arb(2), arb(3)], arb(3), count,
                                 {'f': [arb(1), arb(-1), arb(2)]})
                direct = -(arb(1)-arb(1)/2+arb(2)/3)
                self.assertTrue(box(result['profile_change']['f']['deflated_profile_change_interval']).contains(direct))
                bound = arb(result['deflated_total_inverse_vector_norm_upper'])
                self.assertGreaterEqual(bound, (arb(1)+arb(1)/4+arb(1)/9).sqrt())

    def test_invalid_spectrum_energy_and_dimensions_fail_closed(self):
        with ctx.workprec(128):
            for count in (-1, 2):
                with self.assertRaises(ValueError):
                    deflate(arb_mat([[1, 0], [0, 2]]), [arb(1)]*2, arb(1), count, {})
            with self.assertRaises(ValueError):
                deflate(arb_mat([[1, 1], [0, 2]]), [arb(1)]*2, arb(1), 1, {})
            with self.assertRaises(ArithmeticError):
                deflate(arb_mat([[-1, 0], [0, 2]]), [arb(1)]*2, arb(1), 1, {})
            with self.assertRaises(ArithmeticError):
                deflate(arb_mat([[1, 0], [0, 2]]), [arb(1)]*2, arb(10), 1, {})
        first, second = [json.loads((DATA / f'certified_weil_13_{n}.json').read_text()) for n in (4, 8)]
        with self.assertRaises(ValueError):
            compare(first, second, sigma=-1)


if __name__ == '__main__':
    unittest.main()
