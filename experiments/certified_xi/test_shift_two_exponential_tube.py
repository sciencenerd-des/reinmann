from fractions import Fraction
import json
from pathlib import Path
import tempfile
import unittest

from flint import arb, ctx
from dual_rank_budget import dual_grid
from laboratory import load_coefficients
from shift_two_exponential_tube import load_base, log_error, run


ROOT = Path(__file__).resolve().parents[2]
COEFFICIENTS = ROOT/'research/certified_xi/coefficients_120.json'
BASE = ROOT/'research/certified_xi/pole_shift_two.json'


class ShiftTwoExponentialTubeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 2048
        cls.result = run(BASE, COEFFICIENTS)

    def test_all_rank_slope_and_full_finite_bridge(self):
        r = self.result
        self.assertEqual(r['status'], 'analytic_numerical_all_rank_shift_two_slope_and_boundary_tube')
        self.assertEqual([row['rank'] for row in r['finite_slope_bridge']], list(range(1, 60)))
        self.assertGreater(arb(r['constants']['global_slope_lower']), arb('0.06085'))
        self.assertGreater(arb(r['constants']['tail_slope_lower']), arb('0.06085'))
        self.assertLess(arb(r['geometric_error_rate']), 1)

    def test_decay_and_integrated_width(self):
        terms = [[(Fraction(1, 100), Fraction(1, 2))]]*3
        at_head = log_error(terms, 3)
        for j in (1, 2, 10):
            self.assertLess(log_error(terms, 3+j), at_head*arb('0.5')**j)
        sigma, E = Fraction(3, 4), Fraction(1, 10)
        W = lambda j: E*(1-sigma**(j+1))/(1-sigma)
        self.assertEqual(W(-1), 0)
        for j in range(11):
            self.assertEqual(W(j)-W(j-1), E*sigma**j)

    def test_tube_against_fresh_later_determinants(self):
        with ctx.workprec(2048):
            result = self.result
            c = {k: arb(v) for k, v in result['constants'].items()}
            R = result['head_rank']
            sigma, E = arb(result['geometric_error_rate']), c['head_slope_error_upper']
            mu, _ = load_coefficients(COEFFICIENTS)
            grid = dual_grid(mu, max_rank=100, max_shift=2)
            for rank in (60, 61, 80, 100):
                width = E*(1-sigma**(rank-R+1))/(1-sigma)
                lower = -c['amplitude_upper'].log()-arb(rank+2).log()-rank*c['rate_upper'].log()-width
                upper = -c['amplitude_lower'].log()-arb(rank+2).log()-rank*c['rate_lower'].log()+width
                actual = -grid[rank, 2].log()
                self.assertLess(lower, actual)
                self.assertGreater(upper, actual)
                slope_error = E*sigma**(rank-R)
                slope_lower = -c['rate_upper'].log()-(arb(rank+2)/(rank+1)).log()-slope_error
                slope_upper = -c['rate_lower'].log()-(arb(rank+2)/(rank+1)).log()+slope_error
                slope = (grid[rank-1, 2]/grid[rank, 2]).log()
                self.assertLess(slope_lower, slope)
                self.assertGreater(slope_upper, slope)

    def test_rejects_wrong_inputs_and_unsafe_decay(self):
        with self.assertRaises(ValueError):
            run(BASE, COEFFICIENTS, head=45)
        with self.assertRaises(ArithmeticError):
            log_error([[(Fraction(10), Fraction(1, 2))]]*3, 2)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary)/'bad.json'
            base = json.loads(BASE.read_text())
            base['input_sha256'] = 'wrong'
            path.write_text(json.dumps(base))
            with self.assertRaisesRegex(ValueError, 'input hash mismatch'):
                load_base(path, COEFFICIENTS)
            base = json.loads(BASE.read_text())
            base['determinant_models'][0]['error_terms'][0]['geometric_ratio_upper'] = '1'
            path.write_text(json.dumps(base))
            with self.assertRaisesRegex(ValueError, 'geometric error'):
                load_base(path, COEFFICIENTS)


if __name__ == '__main__':
    unittest.main()
