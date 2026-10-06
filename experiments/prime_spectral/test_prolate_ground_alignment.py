"""Replay finite prolate-ground orientation and coupled strip transfer."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from prolate_ground_alignment import run


ROOT = Path(__file__).resolve().parents[2]
RESEARCH = ROOT / 'research/prime_spectral'
JACOBI = RESEARCH / 'prolate_jacobi_13_80.json'
VECTORS = RESEARCH / 'prolate_vectors_13_80.json'


def overlaps(first: dict[str, str], second: dict[str, str]) -> bool:
    return (Fraction(first['lo']) <= Fraction(second['hi'])
            and Fraction(second['lo']) <= Fraction(first['hi']))


class ProlateGroundAlignmentTests(unittest.TestCase):
    def test_exact_prolate_ground_alignment_replays(self):
        previous_distance = Fraction(1)
        previous_strip = Fraction(1)
        for modes in (4, 8, 12, 16):
            with self.subTest(modes=modes):
                spectrum = RESEARCH / f'{"certified_weil" if modes <= 8 else "isolated_kernel"}_13_{modes}.json'
                candidate = (RESEARCH / f'prolate_candidate_13_{modes}.json'
                             if modes <= 8 else None)
                result = run(RESEARCH / f'exact_prolate_gate_13_{modes}.json',
                             spectrum, RESEARCH / f'prolate_cluster_13_{modes}.json',
                             JACOBI, VECTORS, candidate)
                saved = json.loads((RESEARCH / f'prolate_ground_alignment_13_{modes}.json').read_text())
                self.assertEqual(result, saved)
                distance = Fraction(result['unit_distance_upper'])
                strip = Fraction(result['coupled_uniform_strip_profile_difference_upper'])
                self.assertLess(distance, previous_distance)
                self.assertLess(strip, previous_strip)
                self.assertLess(strip, Fraction(result['uniform_strip_profile_difference_upper']))
                previous_distance, previous_strip = distance, strip
                for name in ('real_4', 'real_8'):
                    entry = result['selected_profile_differences'][name]
                    self.assertLess(Fraction(entry['absolute_difference_upper']), strip)
                if modes <= 8:
                    ground = json.loads((RESEARCH / f'ground_schur_13_{modes}.json').read_text())
                    for name, entry in result['selected_profile_differences'].items():
                        self.assertTrue(overlaps(entry['ground_profile'], ground['profile'][name]))
                if modes == 12:
                    response = json.loads((RESEARCH / 'eigenvalue_response_13_12.json').read_text())
                    for name, entry in result['selected_profile_differences'].items():
                        self.assertTrue(overlaps(
                            entry['ground_profile'],
                            response['profile'][name]['origin_normalized_profile']))

    def test_cross_support_rank_comparison_replays(self):
        results = {}
        for cutoff, terms in ((17, 80), (19, 100)):
            for modes in (8, 12, 16):
                with self.subTest(cutoff=cutoff, modes=modes):
                    cluster = (RESEARCH / f'prolate_cluster_{cutoff}_{modes}.json'
                               if cutoff == 17 or modes == 8 else None)
                    result = run(
                        RESEARCH / f'exact_prolate_gate_{cutoff}_{modes}.json',
                        RESEARCH / f'isolated_kernel_{cutoff}_{modes}.json',
                        cluster,
                        RESEARCH / f'prolate_jacobi_{cutoff}_{terms}.json',
                        RESEARCH / f'prolate_vectors_{cutoff}_{terms}.json')
                    saved = json.loads((RESEARCH / f'prolate_ground_alignment_{cutoff}_{modes}.json').read_text())
                    self.assertEqual(result, saved)
                    self.assertEqual('prolate_cluster' in result['input_sha256'],
                                     cluster is not None)
                    self.assertLess(Fraction(result['unit_distance_lower']),
                                    Fraction(result['unit_distance_upper']))
                    results[cutoff, modes] = result

        for modes in (8, 12, 16):
            first = json.loads((RESEARCH / f'prolate_ground_alignment_13_{modes}.json').read_text())
            for earlier, later in ((first, results[17, modes]),
                                   (results[17, modes], results[19, modes])):
                # These disjoint enclosures certify actual worsening at fixed rank.
                self.assertLess(Fraction(earlier['unit_distance_upper']),
                                Fraction(later['unit_distance_lower']))
                self.assertLess(
                    Fraction(earlier['origin_normalized_coefficient_distance_upper']),
                    Fraction(later['origin_normalized_coefficient_distance_lower']))
        for cutoff in (17, 19):
            for lower_rank, higher_rank in ((8, 12), (12, 16)):
                self.assertLess(
                    Fraction(results[cutoff, higher_rank]['unit_distance_upper']),
                    Fraction(results[cutoff, lower_rank]['unit_distance_lower']))
                self.assertLess(
                    Fraction(results[cutoff, higher_rank]['origin_normalized_coefficient_distance_upper']),
                    Fraction(results[cutoff, lower_rank]['origin_normalized_coefficient_distance_lower']))


if __name__ == '__main__':
    unittest.main()
