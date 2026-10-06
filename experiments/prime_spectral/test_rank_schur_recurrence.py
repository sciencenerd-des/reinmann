"""Replay the coupled fixed-support rank increment."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from rank_schur_recurrence import compare, run


ROOT = Path(__file__).resolve().parents[2]
RESEARCH = ROOT / 'research/prime_spectral'


def overlaps(left: dict, right: dict) -> bool:
    return (Fraction(left['lo']) <= Fraction(right['hi'])
            and Fraction(right['lo']) <= Fraction(left['hi']))


class RankSchurRecurrenceTests(unittest.TestCase):
    def test_coupled_change_matches_independent_ground_profiles(self):
        first = RESEARCH / 'certified_weil_13_4.json'
        second = RESEARCH / 'certified_weil_13_8.json'
        result = run(first, second)
        saved = json.loads((RESEARCH / 'rank_schur_13_4_8.json').read_text())
        self.assertEqual(result, saved)
        reduced = result['feshbach']
        energy = reduced['effective_new_mode_coupling_energy']
        self.assertTrue(overlaps(energy,
                                 reduced['old_secular_function_at_new_eigenvalue']))
        self.assertLess(Fraction(reduced['energy_lower_from_eigenvalue_shift']['hi']),
                        Fraction(energy['lo']))
        self.assertLess(Fraction(energy['hi']),
                        Fraction(reduced['energy_upper_from_eigenvalue_shift']['lo']))
        self.assertGreater(Fraction(reduced['normalized_coupling_energy']['lo']), 0)
        self.assertLess(Fraction(reduced['normalized_coupling_energy']['hi']),
                        Fraction(result['ground_eigenvalue_shift']['lo']))
        transfer = result['coupled_rank_energy']
        self.assertTrue(overlaps(transfer['residual_inverse_energy'],
                                 transfer['eigenvalue_shift_times_old_origin_norm_squared']))
        old_norm = reduced['old_origin_norm_squared']
        expected = (Fraction(result['ground_eigenvalue_shift']['lo'])
                    * Fraction(old_norm['lo']))
        self.assertLessEqual(
            Fraction(transfer['eigenvalue_shift_times_old_origin_norm_squared']['lo']),
            expected)
        old = json.loads((RESEARCH / 'ground_schur_13_4.json').read_text())
        new = json.loads((RESEARCH / 'ground_schur_13_8.json').read_text())
        for name in ('real_4', 'real_8', 'imag_1'):
            with self.subTest(argument=name):
                change = result['profile_change'][name]
                direct = {
                    'lo': str(Fraction(new['profile'][name]['lo'])
                              - Fraction(old['profile'][name]['hi'])),
                    'hi': str(Fraction(new['profile'][name]['hi'])
                              - Fraction(old['profile'][name]['lo'])),
                }
                self.assertTrue(overlaps(change['coupled_change'], direct))
                self.assertGreater(Fraction(
                    change['separate_to_coupled_absolute_ratio_lower']), 1000)
                self.assertGreater(Fraction(change['cauchy_to_actual_ratio_lower']), 180)
                self.assertGreater(Fraction(change['cauchy_profile_upper']['lo']),
                                   max(abs(Fraction(change['coupled_change']['lo'])),
                                       abs(Fraction(change['coupled_change']['hi']))))

    def test_non_nested_input_rejected(self):
        first = json.loads((RESEARCH / 'certified_weil_13_4.json').read_text())
        with self.assertRaises(ValueError):
            compare(first, first)


if __name__ == '__main__':
    unittest.main()
