import json
from pathlib import Path
import unittest

from flint import arb, ctx

from certified_weil import entry
from refine_cluster import OUT, generate
from threshold_ground_gap import box


class RefinedClusterTests(unittest.TestCase):
    def test_full_threshold_and_residual_replay(self):
        result = generate()
        with ctx.workprec(512):
            self.assertEqual(result['threshold_count']['count'], 4)
            self.assertEqual(result['block']['parity_ranks'], {'even': 2, 'odd': 2})
            self.assertTrue(box(result['block']['outside_lower']) > arb('.629'))
            self.assertTrue(box(result['projection_norm_distance_upper']) < arb('.425'))
            self.assertEqual(result['action_prefix'], 256)
            self.assertTrue(all(box(s['gram_lower']) > arb('.999')
                                for s in result['sectors']))

    def test_high_degree_matrix_cells_against_independent_integration(self):
        saved = json.loads((OUT/'ritz_C3_N32.json').read_text())
        with ctx.workprec(512):
            even, odd = [s['matrix'] for s in saved['sectors']]
            L, powers = arb(3).log(), [(2, 2), (3, 3)]
            self.assertTrue(box(odd[31][31]).overlaps(
                entry(32, 32, L, powers, 3)-entry(32, -32, L, powers, 3)))
            self.assertTrue(box(even[1][32]).overlaps(
                entry(1, 32, L, powers, 3)+entry(1, -32, L, powers, 3)))


if __name__ == '__main__':
    unittest.main()
