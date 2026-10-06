"""Replay gap-free finite profile enclosures from concave eigenvalue secants."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from eigenvalue_response import certify, run


ROOT = Path(__file__).resolve().parents[2]
RESEARCH = ROOT / 'research/prime_spectral'


def overlaps(first: dict[str, str], second: dict[str, str]) -> bool:
    return (Fraction(first['lo']) <= Fraction(second['hi'])
            and Fraction(second['lo']) <= Fraction(first['hi']))


class EigenvalueResponseTests(unittest.TestCase):
    def test_secant_profiles_replay_and_match_independent_profiles(self):
        for modes, step in ((4, Fraction('1e-17')),
                            (8, Fraction('1e-25')),
                            (12, Fraction('1e-30'))):
            with self.subTest(modes=modes):
                result = run(RESEARCH / f'certified_weil_13_{modes}.json', step)
                saved = json.loads((RESEARCH / f'eigenvalue_response_13_{modes}.json').read_text())
                self.assertEqual(result, saved)
                self.assertGreater(Fraction(result['origin_response_derivative']['lo']), 0)
                for name, response in result['profile'].items():
                    profile = response['origin_normalized_profile']
                    self.assertLess(Fraction(profile['hi'])-Fraction(profile['lo']),
                                    Fraction(1, 10**5))
                    if modes in (4, 8):
                        ground = json.loads((RESEARCH / f'ground_schur_13_{modes}.json').read_text())
                        independent = ground['profile'][name]
                    else:
                        ground = json.loads((RESEARCH / 'ground_schur_13_8.json').read_text())
                        increment = json.loads((RESEARCH / 'spectral_alignment_13_8_12.json').read_text())
                        change = increment['profile_change'][name]['signed_spectral_profile_change']
                        independent = {
                            'lo': str(Fraction(ground['profile'][name]['lo'])
                                      + Fraction(change['lo'])),
                            'hi': str(Fraction(ground['profile'][name]['hi'])
                                      + Fraction(change['hi'])),
                        }
                    self.assertTrue(overlaps(profile, independent))

    def test_nonpositive_step_rejected(self):
        certificate = json.loads((RESEARCH / 'certified_weil_13_4.json').read_text())
        with self.assertRaises(ValueError):
            certify(certificate, Fraction(0))


if __name__ == '__main__':
    unittest.main()
