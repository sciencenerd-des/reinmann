"""Independent determinant checks and fail-closed atlas gates."""
import json
import unittest
from flint import arb, ctx
from dh_high_rank_scan import condensate
from dh_toeplitz_scan import solid_minor
from dh_zero_atlas import OUT, H, jet, root_center, segment_image, tail_strip
from threshold_ground_gap import box


class SectorProgram(unittest.TestCase):
    def test_tail_strip(self):
        self.assertLess(float(box(tail_strip()['absolute_tail']).upper()), .738)

    def test_l_function_and_hurwitz_agree(self):
        from flint import acb
        with ctx.workprec(320):
            for s in [acb('.8', '85.7'), acb('1.5', '340'), acb('-.5', '20')]:
                self.assertTrue((H(s)-jet(s, 1)[0]).contains(0))

    def test_condensation_against_direct_determinants(self):
        with ctx.workprec(512):
            mu = [arb(1), arb(1), arb(1)]+[arb(0)]*18
            result = condensate(mu, 8, 8)
            self.assertEqual(result['first_negative_in_grid_order']['rank'], 3)
            self.assertEqual(result['first_negative_in_grid_order']['shift'], 1)
            self.assertLess(solid_minor(mu, 3, 1), 0)
            # Rank-two structural zero divisors must poison descendants.
            result = condensate([arb(1)]*21, 8, 8)
            self.assertGreater(result['per_rank'][-1]['unresolved'], 0)

    def test_sharp_quadratic_rank(self):
        with ctx.workprec(512):
            atlas = json.loads((OUT/'atlas_H340.json').read_text())
            phi = box(atlas['steepest_candidate']['folded_deviation_angle'])
            c = phi.cos()
            older, prev = arb(1), 2*c
            for k in range(2, 437):
                value = 2*c*prev-older
                analytic = ((k+1)*phi).sin()/phi.sin()
                self.assertTrue((value-analytic).contains(0))
                if k <= 435:
                    self.assertGreater(analytic, 0)
                else:
                    self.assertLess(analytic, 0)
                if k <= 16:
                    direct = solid_minor([arb(1), 2*c, arb(1)]+[arb(0)]*20, k, 1)
                    self.assertTrue((direct-value).contains(0))
                older, prev = prev, value

    def test_atlas_count_and_steepest(self):
        with ctx.workprec(256):
            a = json.loads((OUT/'atlas_H340.json').read_text())
            self.assertEqual(a['global_rectangle_count'], 249)
            self.assertEqual(a['critical_line_bracket_count']+2*a['right_off_line_disks'], 249)
            self.assertEqual(a['remaining_count'], 0)
            self.assertEqual(a['conditional_sector_guaranteed_PF_rank'], 435)
            phi = box(a['steepest_candidate']['folded_deviation_angle'])
            self.assertGreater(phi, box(a['maximum_high_zero_deviation']))
            self.assertGreater(arb.pi()/phi, 436)
            self.assertLess(arb.pi()/phi, 437)
            self.assertAlmostEqual(float(root_center(a['steepest_candidate']).imag.mid()), 85.6993484853776, places=10)


if __name__ == '__main__':
    unittest.main()
