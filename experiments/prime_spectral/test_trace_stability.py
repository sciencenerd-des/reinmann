"""Check enclosure signs, truncation stability, and both full-gap witnesses."""
import hashlib
import json
from pathlib import Path
import unittest

from flint import arb, ctx

from certified_weil import certified_matrix
from renewal_trace_enclosures import conditional_trace, kappa, renewal_mass
from threshold_ground_gap import box, minmax_second_bound


class TraceEnclosureTests(unittest.TestCase):
    def test_signed_quotients(self):
        with ctx.workprec(192):
            for lo, hi in [('2','3'), ('-3','-2'), ('-2','3')]:
                left, right = conditional_trace(lo,hi,'1/10','1','2')
                for p in [arb(lo),arb(hi)]:
                    for v in [arb(1),arb(2)]:
                        for error in [-arb('1/5')*v, arb('1/5')*v]:
                            self.assertTrue(left <= p/v+error <= right)

    def test_invalid_bounds_fail_closed(self):
        for args in [('2','1','0','1','2'), ('1','2','-1','1','2'),
                     ('1','2','0','0','2'), ('1','2','0','2','1')]:
            with self.assertRaises(ValueError):
                conditional_trace(*args)
        with self.assertRaises(ValueError):
            renewal_mass(0)

    def test_whole_tail_and_quadrature_stability(self):
        with ctx.workprec(192):
            # Different truncated integrals, each with its own WHOLE-tail bound.
            wide = kappa(0,64)
            narrow = kappa(0,128)
            self.assertTrue(wide.overlaps(narrow))
            self.assertTrue(wide > 0 and narrow > 0)


class ThresholdGapTests(unittest.TestCase):
    def test_full_complement_and_trial_replay(self):
        root = Path('research/prime_spectral/verification_2026_10_07_trace_stability')
        record = json.loads((root/'threshold_ground_gaps.json').read_text())
        self.assertEqual(record['source_sha256'],
                         hashlib.sha256(Path('experiments/prime_spectral/threshold_ground_gap.py')
                                        .read_bytes()).hexdigest())
        with ctx.workprec(384):
            for row in record['results']:
                source = Path(row['lower_operator_input'])
                self.assertEqual(row['lower_operator_sha256'],
                                 hashlib.sha256(source.read_bytes()).hexdigest())
                second, sectors = minmax_second_bound(json.loads(source.read_text()),row['shift'])
                self.assertEqual([s['negative_count'] for s in sectors],[1,0])
                _, even, _ = certified_matrix(row['threshold_prime'],8)
                coefficients = [arb(s) for s in row['trial_even_cosine_coefficients']]
                norm_sq = sum((x*x for x in coefficients),arb(0))
                upper = sum((coefficients[i]*even[i][j]*coefficients[j]
                             for i in range(len(even)) for j in range(len(even))),arb(0))/norm_sq
                self.assertTrue(second.overlaps(box(row['second_eigenvalue_lower'])))
                self.assertTrue(upper.overlaps(box(row['trial_ground_eigenvalue_upper'])))
                if row['threshold_prime'] == 2:
                    self.assertTrue(second > arb('999/100000'))
                    self.assertTrue(upper < arb('142/100000'))
                else:
                    self.assertTrue(second > arb('109/1000000000'))
                    self.assertTrue(upper < arb('103/1000000000'))
                self.assertTrue(second-upper > 0)


if __name__ == '__main__':
    unittest.main()
