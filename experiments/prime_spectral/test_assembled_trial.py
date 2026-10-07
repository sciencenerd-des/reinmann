"""Full-residual failure evidence and stronger infinite-complement witnesses."""
import hashlib
import json
from pathlib import Path
import unittest

from flint import arb, arb_mat, ctx

from assembled_trial_certificate import ROOT, assembled_bounds, cutoff_graph_bounds
from certified_weil import certified_matrix
from threshold_ground_gap import box, minmax_second_bound


class AssembledTrialTests(unittest.TestCase):
    def test_actual_trial_record_and_unavoidable_trace_gate_failure(self):
        data=json.loads((ROOT/'assembled_trials.json').read_text())
        with ctx.workprec(384):
            for path,digest in data['source_hashes'].items():
                self.assertEqual(hashlib.sha256(Path(path).read_bytes()).hexdigest(),digest)
            for row,U in zip(data['results'],('0.00142','0.000000103'),strict=True):
                self.assertTrue(box(row['norm_enclosure']).contains(1))
                self.assertTrue(box(row['actual_rayleigh_enclosure']) < arb(U))
                self.assertTrue(box(row['both_exact_trial_trace_enclosures']) > 0)
                rlo=arb(row['actual_full_L2_residual_enclosure']['lo'])
                A=box(row['L2_trace_coefficient'])
                tracehi=arb(row['both_exact_trial_trace_enclosures']['hi'])
                self.assertTrue(A*rlo > tracehi)
                if row['threshold_prime']==3:
                    self.assertTrue(rlo > box(row['weakened_full_complementary_clearance']))

    def test_outside_mode_is_not_a_projected_residual_upper_bound(self):
        # A selfadjoint two-dimensional example: the head residual is zero
        # while the FULL residual is nonzero in the omitted test direction.
        with ctx.workprec(192):
            A=arb_mat([[1,'1/10'],['1/10',2]])
            g=arb_mat([[1],[0]])
            residual=A*g-g
            self.assertTrue(residual[0,0].is_zero())
            self.assertTrue(residual[1,0] > 0)
            norm=(residual[0,0]**2+residual[1,0]**2).sqrt()
            self.assertTrue((norm-residual[1,0]).contains(0))

    def test_full_gap_witnesses_and_all_entry_reassembly(self):
        data=json.loads((ROOT/'assembled_trials.json').read_text())
        replay=json.loads((ROOT/'all_entry_reassembly.json').read_text())
        with ctx.workprec(384):
            for row,again in zip(data['results'],replay['results'],strict=True):
                source=Path(row['lower_operator_input'])
                self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(),row['lower_operator_sha256'])
                second,sectors=minmax_second_bound(json.loads(source.read_text()),row['shift'])
                self.assertTrue(second.overlaps(box(row['full_second_eigenvalue_lower'])))
                self.assertEqual(sum(s['negative_count'] for s in sectors),1)
                self.assertEqual(again['entries_compared'],3200 if row['threshold_prime']==2 else 12800)
                self.assertEqual(sum(again['negative_counts']),1)
                self.assertTrue(box(again['alternate_gap_lower']) > box(row['weakened_full_complementary_clearance']))

    def test_saved_probe_repeats_in_a_larger_test_space(self):
        with ctx.workprec(384):
            for row in json.loads((ROOT/'assembled_trials.json').read_text())['results']:
                _,matrix,_=certified_matrix(row['threshold_prime'],10)
                c=list(map(arb,row['cosine_coefficients']))
                norm=sum((x*x for x in c),arb(0)).sqrt()
                probe=sum((matrix[9][j]*c[j]/norm for j in range(9)),arb(0))
                saved=box(row['normalization_details']['omitted_mode_coupling'])
                self.assertTrue(probe.overlaps(saved))

    def test_fail_closed_trial_inputs(self):
        with self.assertRaises(ValueError):
            assembled_bounds(1,[0]*9,[[0]*10 for _ in range(10)],0,1,1,1,0,1)
        with self.assertRaises(ValueError):
            assembled_bounds(1,[0]*9,[[0]*10 for _ in range(10)],1,1,1,1,0,1)

    def test_fixed_trace_with_small_full_graph_norm(self):
        with ctx.workprec(384):
            for row in json.loads((ROOT/'assembled_trials.json').read_text())['results']:
                examples=row['fixed_trace_small_graph_examples']
                self.assertTrue(box(examples[0]['graph_upper']) > box(examples[1]['graph_upper']))
                self.assertTrue(box(examples[1]['graph_upper']) > box(examples[2]['graph_upper']))
                for example in examples:
                    self.assertTrue(box(example['exact_trace']) > 3)
                last=examples[-1]
                self.assertTrue(box(last['exact_trace']) > arb('1e20')*box(last['graph_upper']))
            with self.assertRaises(ValueError):
                cutoff_graph_bounds('nan',1,1,1)


if __name__=='__main__':
    unittest.main()
