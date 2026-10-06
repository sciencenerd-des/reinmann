"""Replay finite support steps and independent prolate-alignment profiles."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from support_schur_recurrence import certify, run


RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


def overlaps(first: dict[str, str], second: dict[str, str]) -> bool:
    return (Fraction(first['lo']) <= Fraction(second['hi'])
            and Fraction(second['lo']) <= Fraction(first['hi']))


class SupportSchurRecurrenceTests(unittest.TestCase):
    def test_cutoff_17_to_19_replays_at_three_ranks(self):
        real_prolate_defects = {}
        for modes in (8, 12, 16):
            with self.subTest(modes=modes):
                result = run(RESEARCH / f'isolated_kernel_17_{modes}.json',
                             RESEARCH / f'isolated_kernel_19_{modes}.json')
                saved = json.loads((RESEARCH / f'support_schur_17_19_{modes}.json').read_text())
                self.assertEqual(result, saved)
                for name, entry in result['profile_change'].items():
                    self.assertTrue(overlaps(entry['total_support_step'],
                                             entry['direct_profile_change']))
                    first = json.loads((RESEARCH / f'prolate_ground_alignment_17_{modes}.json').read_text())
                    second = json.loads((RESEARCH / f'prolate_ground_alignment_19_{modes}.json').read_text())
                    old = first['selected_profile_differences'][name]['ground_profile']
                    new = second['selected_profile_differences'][name]['ground_profile']
                    independent = {
                        'lo': str(Fraction(new['lo']) - Fraction(old['hi'])),
                        'hi': str(Fraction(new['hi']) - Fraction(old['lo'])),
                    }
                    self.assertTrue(overlaps(entry['direct_profile_change'], independent))
                    old_error = first['selected_profile_differences'][name]['ground_minus_exact_prolate']
                    new_error = second['selected_profile_differences'][name]['ground_minus_exact_prolate']
                    defect = (Fraction(new_error['lo']) - Fraction(old_error['hi']),
                              Fraction(new_error['hi']) - Fraction(old_error['lo']))
                    if name == 'real_4':
                        self.assertLess(defect[1], 0)
                        real_prolate_defects[modes] = defect
                real = result['profile_change']['real_4']
                self.assertLess(Fraction(real['basis_length_drift']['hi']), 0)
                self.assertGreater(Fraction(real['coupled_ground_change']['lo']), 0)
                self.assertLess(Fraction(real['total_support_step']['hi']), 0)
                self.assertLess(Fraction(real['total_support_step']['hi'])
                                - Fraction(real['total_support_step']['lo']),
                                Fraction(1, 10**6))
                if modes == 16:
                    direct_inverse = real['direct_interval_inverse_ground_change']
                    self.assertGreater(Fraction(direct_inverse['hi'])
                                       - Fraction(direct_inverse['lo']), 10_000)
        self.assertLess(real_prolate_defects[8][1], real_prolate_defects[12][0])
        self.assertLess(real_prolate_defects[12][1], real_prolate_defects[16][0])

    def test_requires_increasing_support_at_same_rank(self):
        first = json.loads((RESEARCH / 'isolated_kernel_17_8.json').read_text())
        second = json.loads((RESEARCH / 'isolated_kernel_19_12.json').read_text())
        with self.assertRaises(ValueError):
            certify(first, second)
        with self.assertRaises(ValueError):
            certify(first, first)


if __name__ == '__main__':
    unittest.main()
