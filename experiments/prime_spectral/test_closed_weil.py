"""Independent integral comparisons and high-index archimedean tails."""
from fractions import Fraction
import json
from pathlib import Path
import unittest

from flint import arb, ctx

from closed_weil import entry_closed, run
from weil_matrix import prime_powers


RESEARCH = Path(__file__).resolve().parents[2] / 'research/prime_spectral'


class ClosedWeilTests(unittest.TestCase):
    def test_saved_integral_comparison_replays(self):
        self.assertEqual(run(17, 8), json.loads((RESEARCH / 'closed_weil_17_8.json').read_text()))
        for cutoff in (2, 13, 19):
            result = run(cutoff, 2)
            self.assertEqual(len(result['comparisons']), 5)

    def test_high_index_tail_encloses_refined_formula(self):
        with ctx.workprec(512):
            length = arb(17).log()
            powers = [(p, prime) for p, prime in prime_powers(17) if p < 17]
            for indices in ((1000, 1000), (1000, 999), (1000, -1000), (0, 1000)):
                coarse = entry_closed(*indices, length, powers, 2)
                fine = entry_closed(*indices, length, powers, 40)
                self.assertLessEqual(Fraction(str(coarse.lower().fmpq())), Fraction(str(fine.lower().fmpq())))
                self.assertGreaterEqual(Fraction(str(coarse.upper().fmpq())), Fraction(str(fine.upper().fmpq())))


if __name__ == '__main__':
    unittest.main()
