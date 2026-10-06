"""Replay coupled response increments against spectral rank increments."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from rank_response_determinant import compare, run


ROOT = Path(__file__).resolve().parents[2]
RESEARCH = ROOT / 'research/prime_spectral'


def overlaps(first: dict[str, str], second: dict[str, str]) -> bool:
    return (Fraction(first['lo']) <= Fraction(second['hi'])
            and Fraction(second['lo']) <= Fraction(first['hi']))


class RankResponseDeterminantTests(unittest.TestCase):
    def test_coupled_rank_steps_replay(self):
        for small, large in ((4, 8), (8, 12)):
            with self.subTest(modes=(small, large)):
                result = run(
                    RESEARCH / f'eigenvalue_response_13_{small}.json',
                    RESEARCH / f'eigenvalue_response_13_{large}.json',
                    RESEARCH / f'certified_weil_13_{small}.json',
                    RESEARCH / f'certified_weil_13_{large}.json')
                saved = json.loads((RESEARCH / f'rank_response_13_{small}_{large}.json').read_text())
                self.assertEqual(result, saved)
                spectral = json.loads((RESEARCH / f'spectral_alignment_13_{small}_{large}.json').read_text())
                for name, entry in result['profile_change'].items():
                    self.assertTrue(overlaps(
                        entry['profile_increment'],
                        spectral['profile_change'][name]['signed_spectral_profile_change']))
                    self.assertGreater(Fraction(entry['separate_to_coupled_ratio_lower']), 1)
                self.assertGreater(Fraction(result['profile_change']['imag_1'][
                    'separate_to_coupled_ratio_lower']), 100)

    def test_non_nested_responses_rejected(self):
        first = json.loads((RESEARCH / 'eigenvalue_response_13_4.json').read_text())
        with self.assertRaises(ValueError):
            compare(first, first)


if __name__ == '__main__':
    unittest.main()
