"""Check the spectral filter inequality and its input domain."""
from fractions import Fraction
from pathlib import Path
import unittest

from flint import arb, ctx

from filtered_candidate_transfer import filter_distance_upper, run


class FilteredCandidateTransferTests(unittest.TestCase):
    def test_inverse_filter_contracts_the_orthogonal_angle(self):
        with ctx.workprec(256):
            unshifted = filter_distance_upper(arb('0.6'), arb('0.8'),
                                               arb(1), arb(10))
            shifted = filter_distance_upper(arb('0.6'), arb('0.8'),
                                             arb(1), arb(10), arb(1))
            self.assertTrue(unshifted < arb('0.19'))
            self.assertTrue(shifted > unshifted)

    def test_rejects_missing_overlap_or_gap(self):
        for alpha, lowest, second in ((0, 1, 10), (1, 10, 10), (1, -1, 10)):
            with self.assertRaises(ValueError):
                filter_distance_upper(arb(alpha), arb(0), arb(lowest), arb(second))

    def test_filter_can_change_prolate_fourier_profile(self):
        root = Path(__file__).resolve().parents[2]
        with ctx.workprec(512):
            result = run(root / 'research/prime_spectral/certified_weil_13_4.json',
                         root / 'research/prime_spectral/prolate_candidate_13_4.json')
        distortion = result['profile_distortion_at_real_frequency']['4']
        self.assertGreater(Fraction(distortion['prolate_filtered_difference_lower']),
                           Fraction(22, 100))


if __name__ == '__main__':
    unittest.main()
