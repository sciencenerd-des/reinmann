"""Replay the finite spectral pairing and its improvement over Cauchy."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from spectral_alignment import compare, run


ROOT = Path(__file__).resolve().parents[2]
RESEARCH = ROOT / 'research/prime_spectral'


class SpectralAlignmentTests(unittest.TestCase):
    def test_saved_pairing_replays_and_bounds_direct_change(self):
        result = run(RESEARCH / 'certified_weil_13_4.json',
                     RESEARCH / 'certified_weil_13_8.json')
        saved = json.loads((RESEARCH / 'spectral_alignment_13_4_8.json').read_text())
        self.assertEqual(result, saved)
        recurrence = json.loads((RESEARCH / 'rank_schur_13_4_8.json').read_text())
        for name, entry in result['profile_change'].items():
            with self.subTest(argument=name):
                direct = entry['direct_profile_change']
                coupled = recurrence['profile_change'][name]['coupled_change']
                self.assertLessEqual(Fraction(direct['lo']), Fraction(coupled['hi']))
                self.assertLessEqual(Fraction(coupled['lo']), Fraction(direct['hi']))
                spectral = Fraction(entry['spectral_absolute_sum_upper'])
                self.assertGreater(spectral, max(abs(Fraction(direct['lo'])),
                                                 abs(Fraction(direct['hi']))))
                self.assertLess(Fraction(entry['alignment_to_actual_ratio_upper']),
                                Fraction(4, 3))
                self.assertGreater(Fraction(entry['global_cauchy_upper']),
                                   100 * spectral)

    def test_additional_supports_and_larger_rank_replay(self):
        for cutoff, small, large in ((13, 8, 12), (17, 4, 8), (19, 4, 8)):
            with self.subTest(cutoff=cutoff, modes=(small, large)):
                result = run(RESEARCH / f'certified_weil_{cutoff}_{small}.json',
                             RESEARCH / f'certified_weil_{cutoff}_{large}.json')
                saved = json.loads((RESEARCH / f'spectral_alignment_{cutoff}_{small}_{large}.json').read_text())
                self.assertEqual(result, saved)
                for entry in result['profile_change'].values():
                    signed = entry['signed_spectral_profile_change']
                    direct = entry['direct_profile_change']
                    self.assertLessEqual(Fraction(signed['lo']), Fraction(direct['hi']))
                    self.assertLessEqual(Fraction(direct['lo']), Fraction(signed['hi']))
                    self.assertTrue(entry['spectral_improves_global_cauchy_certified'])
                    self.assertGreater(Fraction(entry['alignment_to_actual_ratio_upper']), 1)
        # The direct interval inverse is badly conditioned at rank 12;
        # summing isolated spectral terms still encloses a sharp change.
        saved = json.loads((RESEARCH / 'spectral_alignment_13_8_12.json').read_text())
        direct = saved['profile_change']['real_4']['direct_profile_change']
        signed = saved['profile_change']['real_4']['signed_spectral_profile_change']
        self.assertGreater(Fraction(direct['hi']) - Fraction(direct['lo']), 1000)
        self.assertLess(Fraction(signed['hi']) - Fraction(signed['lo']),
                        Fraction(1, 10**6))

    def test_non_nested_input_rejected(self):
        first = json.loads((RESEARCH / 'certified_weil_13_4.json').read_text())
        with self.assertRaises(ValueError):
            compare(first, first)


if __name__ == '__main__':
    unittest.main()
