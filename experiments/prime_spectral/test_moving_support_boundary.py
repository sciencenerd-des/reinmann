"""Replay the moving-support boundary identity and its prime-kick match."""
import json
from fractions import Fraction
from pathlib import Path
import unittest

from flint import arb, ctx

from cross_support_physical_overlap import cross_gram
from moving_support_boundary import gram_log_length_derivative, run


RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


class MovingSupportBoundaryTests(unittest.TestCase):
    def test_rank_one_symmetric_part_and_gram_secants(self):
        with ctx.workprec(256):
            boundary = [arb(1)] + [arb(2).sqrt() for _ in range(4)]
            length = arb(17).log()
            step = arb(1) / 100_000
            for i in range(5):
                for j in range(5):
                    with self.subTest(i=i, j=j):
                        forward = gram_log_length_derivative(i, j)
                        reverse = gram_log_length_derivative(j, i)
                        self.assertTrue((forward + reverse
                                         + boundary[i] * boundary[j]).contains(0))
                        secant = (cross_gram(i, j, length, length + step)
                                  - cross_gram(i, j, length, length)) / step
                        self.assertLess(abs(float((secant - forward / length).mid())),
                                        2e-4)

    def test_saved_threshold_certificates_replay(self):
        for cutoff, modes in ((17, 8), (17, 16), (19, 16)):
            with self.subTest(cutoff=cutoff, modes=modes):
                result = run(RESEARCH / f'isolated_kernel_{cutoff}_{modes}.json',
                             RESEARCH / f'prime_threshold_jump_{cutoff}_{modes}.json')
                saved = json.loads((RESEARCH / f'moving_boundary_{cutoff}_{modes}.json').read_text())
                self.assertEqual(result, saved)
                overlap_slope = result['physical_overlap_right_derivative']
                prime_kick = result['prime_eigenvalue_derivative_jump']
                self.assertLess(Fraction(overlap_slope['hi']), 0)
                self.assertLess(Fraction(prime_kick['hi']), 0)
                self.assertGreater(Fraction(
                    result['origin_matched_norm_squared_right_derivative']['lo']), 0)
                if modes == 16:
                    direct = result['direct_interval_gram_contraction']
                    self.assertLess(Fraction(direct['lo']), 0)
                    self.assertGreater(Fraction(direct['hi']), 0)

    def test_rejects_mismatched_threshold(self):
        from moving_support_boundary import certify
        isolated = json.loads((RESEARCH / 'isolated_kernel_17_8.json').read_text())
        threshold = json.loads((RESEARCH / 'prime_threshold_jump_19_8.json').read_text())
        with self.assertRaises(ValueError):
            certify(isolated, threshold)


if __name__ == '__main__':
    unittest.main()
