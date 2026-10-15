"""Cluster min--max, full residual, parity and provenance checks."""
import copy
import json
import unittest

from flint import arb, ctx

from certified_weil import certified_matrix
from full_cluster_certificate import (OUT, BASE, actual_ritz, close_cluster,
    energy_cluster_mass, proposed_rank, residual_cluster_angle)
from threshold_ground_gap import box


class FullClusterTests(unittest.TestCase):
    def test_energy_bound_with_negative_cluster_floor_is_sharp(self):
        with ctx.workprec(256):
            # diag(-2,-1,5), unit f=(12/13,0,5/13), P has rank two.
            mass = arb(25)/169
            mu = -2*(1-mass)+5*mass
            got = energy_cluster_mass(mu, -2, 5)
            self.assertTrue(abs(got-mass) < arb(2)**-200)
            self.assertTrue(got.upper() >= mass.lower())

    def test_block_residual_does_not_use_tiny_internal_gap(self):
        with ctx.workprec(256):
            # V=[(12/13,0,5/13),(0,1,0)], A=diag(1,1+e,5),
            # B=diag(1,1+e). Full residual HS norm=20/13.
            for e in ['0', '1e-40', '1/10']:
                angle = residual_cluster_angle(arb(20)/13, 1+arb(e), 5)
                self.assertTrue(angle.upper() >= (arb(5)/13).lower())
                self.assertTrue(angle < arb('0.40'))
            self.assertTrue(residual_cluster_angle(0, 1, 5).is_zero())

    def test_projected_residual_is_insufficient(self):
        with ctx.workprec(256):
            # A=diag(0,4), v=(12/13,5/13), B=<v,Av>.
            # V*(Av-VB)=0, but its full residual and true outside angle are nonzero.
            x, y = arb(12)/13, arb(5)/13
            B = 4*y*y
            r0, r1 = -B*x, (4-B)*y
            self.assertTrue((x*r0+y*r1).contains(0))
            full = (r0*r0+r1*r1).sqrt()
            self.assertTrue(full > 0)
            self.assertTrue(residual_cluster_angle(full, B, 4) > y)

    def test_both_parity_formulas_match_adaptive_geometric_entries(self):
        with ctx.workprec(512):
            even, odd, _ = actual_ritz('3', 3)
            _, expected_even, expected_odd = certified_matrix(3, 3)
            for A, B in [(even, expected_even), (odd, expected_odd)]:
                self.assertTrue(all(x.overlaps(y) for row, other in zip(A, B)
                                    for x, y in zip(row, other)))

    def test_invalid_energy_and_gap_fail_closed(self):
        for args in [(3, 0, 3), (-1, 0, 3), ('nan', 0, 3)]:
            with self.assertRaises((ValueError, ArithmeticError)):
                energy_cluster_mass(*args)
        for args in [(-1, 0, 3), (1, 3, 3), (1, 4, 3), ('nan', 0, 3)]:
            with self.assertRaises(ValueError):
                residual_cluster_angle(*args)

    def test_rank_proposal_is_only_an_exact_staircase(self):
        self.assertEqual([proposed_rank(C) for C in ['2', '3', '16/5']], [3, 5, 5])
        self.assertEqual(proposed_rank('27/8'), 6)
        self.assertEqual(proposed_rank('33749/10000'), 5)

    def test_all_saved_full_clusters_replay(self):
        saved = json.loads((OUT/'full_clusters.json').read_text())
        with ctx.workprec(512):
            for row in saved['results']:
                C = row['C']; name = {'2': 'two', '3': 'three'}.get(C)
                path = BASE/f'band128_{name}_lower_operator.json' if name else OUT/'C3p2_lower_operator.json'
                lower = json.loads(path.read_text())
                ritz = json.loads((OUT/f'ritz_C{C.replace("/", "_")}.json').read_text())
                checked = close_cluster(lower, ritz, C, row['rank'],
                                        row['cluster_top_upper']['hi'], row['comparison_shift'])
                self.assertEqual(checked['parity_ranks'], row['parity_ranks'])
                self.assertTrue(box(checked['outer_gap_lower']) > 0)
                self.assertFalse(row['rank_proposal_assumed'])

    def test_complement_parity_rank_and_provenance_tampering_rejected(self):
        lower = json.loads((BASE/'band128_two_lower_operator.json').read_text())
        ritz = json.loads((OUT/'ritz_C2.json').read_text())
        variants = []
        x = copy.deepcopy(lower); x['infinite_coupling_bound'] = {'lo':'0', 'hi':'0'}; variants.append((x, ritz, 3))
        x = copy.deepcopy(lower); x['sectors'] = x['sectors'][:1]; variants.append((x, ritz, 3))
        x = copy.deepcopy(ritz); x['sectors'].reverse(); variants.append((lower, x, 3))
        x = copy.deepcopy(ritz); x['source_sha256'] = {}; variants.append((lower, x, 3))
        variants.append((lower, ritz, 4))
        with ctx.workprec(512):
            for low, high, rank in variants:
                with self.assertRaises((ValueError, ArithmeticError)):
                    close_cluster(low, high, '2', rank, '67/100', '9/10')

    def test_small_rayleigh_witness_recomputes_in_actual_form(self):
        saved = json.loads((OUT/'full_clusters.json').read_text())
        with ctx.workprec(512):
            row = next(x for x in saved['results'] if x['C'] == '16/5')
            A = [[box(x) for x in r] for r in json.loads((OUT/'ritz_C16_5.json').read_text())['sectors'][0]['matrix']]
            witness = row['small_rayleigh_witness']
            v = [arb(x) for x in witness['exact_even_cosine_coefficients']]
            norm = sum((x*x for x in v), arb(0))
            mu = sum((v[i]*A[i][j]*v[j] for i in range(len(v)) for j in range(len(v))), arb(0))/norm
            self.assertTrue(box(witness['full_form_rayleigh']).contains(mu))
            self.assertTrue(mu > 0)


if __name__ == '__main__':
    unittest.main()
