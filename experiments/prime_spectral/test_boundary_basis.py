"""Cross-discretization profiles, normalization, and signed trace gates."""
import hashlib
import json
from pathlib import Path
import unittest

from flint import arb, ctx

from renewal_boundary_basis import evaluate_newton, spectral_panel
from renewal_trace_enclosures import kappa
from residual_endpoint_certificate import (bounds_for_interval,
    residual_constants, residual_trace_interval)
from threshold_ground_gap import box

ROOT=Path('research/prime_spectral/verification_2026_10_07_boundary_basis')


class BoundaryBasisTests(unittest.TestCase):
    def test_changed_discretization_and_laplace_normalization(self):
        primary=json.loads((ROOT/'renewal_basis.json').read_text())
        alternate=json.loads((ROOT/'renewal_basis_alternate.json').read_text())
        old=json.loads(Path('research/prime_spectral/renewal_trace_enclosures_2026_10_07.json').read_text())
        self.assertNotEqual(primary['nodes_per_panel'],alternate['nodes_per_panel'])
        self.assertNotEqual(primary['panel_width'],alternate['panel_width'])
        with ctx.workprec(256):
            J=box(primary['exact_basis_trace'])
            self.assertTrue((J*kappa((arb(1)/2).log(),64)).contains(1))
            for data in (primary,alternate):
                for path,digest in data['source_hashes'].items():
                    self.assertEqual(hashlib.sha256(Path(path).read_bytes()).hexdigest(),digest)
            for first,second in zip(primary['rows'],alternate['rows'],strict=True):
                self.assertEqual(first['distance_label'],second['distance_label'])
                for key in ('renewal','basis'):
                    self.assertTrue(box(first[key]).overlaps(box(second[key])))
                V,h,x=(box(first[k]) for k in ('renewal','basis','distance'))
                self.assertTrue(h < J*V)
                self.assertTrue(h > (-x/2).exp()*J*V)
                previous=next((r for r in old['rows'] if r['distance_label']==first['distance_label']),None)
                if previous:
                    bound=previous['renewal_mass']
                    self.assertTrue(V > arb(bound['lo']))
                    self.assertTrue(V < arb(bound['hi']))

    def test_cauchy_remainder_at_non_node_points(self):
        # Sample checks supplement, rather than establish, the written uniform proof.
        with ctx.workprec(256):
            for left in (-8,0,8):
                nodes,coefficients,error=spectral_panel(left,left+1,12,64)
                for offset in ('1/7','1/2','6/7'):
                    z=arb(left)+arb(offset)
                    actual=kappa((1+z.exp()).log()/2,64)
                    difference=evaluate_newton(z,nodes,coefficients).real-actual
                    self.assertTrue(abs(difference) < error)

    def test_signed_trace_corners_include_actual_state(self):
        with ctx.workprec(192):
            for trial in (-2,0,2):
                lo,hi=residual_trace_interval(trial,trial,'3/5',0,1,1,0)
                for overlap in ('4/5','9/10','1'):
                    for remainder in ('-3/5','0','3/5'):
                        actual=(arb(trial)-arb(remainder))/arb(overlap)
                        # Arb rounds rational arithmetic, so compare enclosure overlap.
                        self.assertTrue(actual.upper() >= lo)
                        self.assertTrue(actual.lower() <= hi)
            lo,hi=residual_trace_interval(-2,-2,'3/5',0,1,1,0)
            self.assertTrue(lo <= arb('-13/4'))
            self.assertTrue(hi >= arb('-7/5'))

    def test_full_residual_clearance_and_input_failure_gates(self):
        for args in [(0,0,1,0,1,1,1),(0,0,2,0,1,1,1),
                     (1,0,0,0,1,1,1),(0,0,0,-1,1,1,1),
                     (0,0,0,0,0,1,1),('nan',0,0,0,1,1,1)]:
            with self.assertRaises(ValueError):
                residual_trace_interval(*args)
        with self.assertRaises(ValueError):
            bounds_for_interval(1,0,'inf',2)

    def test_actual_envelopes_and_split_residual_budget(self):
        saved=json.loads((ROOT/'residual_trace_constants.json').read_text())
        with ctx.workprec(256):
            for path,digest in saved['source_hashes'].items():
                self.assertEqual(hashlib.sha256(Path(path).read_bytes()).hexdigest(),digest)
            for row,ceiling in zip(saved['records'],(4336,41395),strict=True):
                self.assertTrue(box(row['one_sided_two_minimizer_bounds']['trace']) < ceiling)
                A,B=(box(row[k]) for k in ('L2_residual_trace_coefficient',
                                          'Linfty_residual_trace_coefficient'))
                e2,ei=(arb(row[k]['lo']) for k in (
                    'split_L2_budget_for_complement_trace_error_1e-3',
                    'split_Linfty_budget_for_complement_trace_error_1e-3'))
                self.assertTrue((A*e2+B*ei).upper() <= arb('1e-3').upper())
                h=box(row['fixed_threshold_clearance'])
                self.assertTrue(e2/h < arb('1e-2'))
                with self.assertRaises(ValueError):
                    residual_constants({},0)


if __name__=='__main__':
    unittest.main()
