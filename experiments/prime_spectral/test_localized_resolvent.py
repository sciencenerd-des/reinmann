"""Noncommuting inverse identity, enclosure failure gates, and scale checks."""
import unittest

from flint import arb, arb_mat, ctx

from localized_resolvent_enclosures import localization_bounds


class LocalizedResolventTests(unittest.TestCase):
    def test_noncommuting_second_identity_and_both_linear_signs(self):
        with ctx.workprec(192):
            T = arb_mat([[3,1],[1,2]])
            F = arb_mat([['1/4','2/5'],['2/5','-1/4']])
            D = T+F
            # Gershgorin gives D>=1/4; ||F|| <= ||F||_F <1.
            gamma, W = arb(1)/4, arb(1)
            ti, di = T.inv(), D.inv()
            commutator = T*F-F*T
            self.assertFalse(commutator[0,1].contains(0))
            difference = di-(ti-ti*F*ti+ti*F*di*F*ti)
            for i in range(2):
                for j in range(2):
                    self.assertTrue(difference[i,j].contains(0))
            signs = set()
            for a in range(-3,4):
                for b in range(-3,4):
                    if (a,b) == (0,0):
                        continue
                    v = arb_mat([[a],[b]])
                    linear = (v.transpose()*ti*F*ti*v)[0,0]
                    if linear > 0:
                        signs.add(1)
                    if linear < 0:
                        signs.add(-1)
                    actual = (v.transpose()*di*v)[0,0]
                    upper = (v.transpose()*(ti+(W+W*W/gamma)*ti*ti)*v)[0,0]
                    self.assertTrue(actual < upper)
            self.assertEqual(signs,{-1,1})

    def test_fail_closed_parameters(self):
        for args in [(31,1,1,1),(32,0,1,1),(32,-1,1,1),
                     (32,1,-1,1),(32,1,1,-1),('nan',1,1,1)]:
            with self.assertRaises(ValueError):
                localization_bounds(*args)

    def test_sharp_scaled_enclosure_for_small_gap(self):
        with ctx.workprec(256):
            # Tests the asymptotic constants with a gap smaller than prime 3's.
            row = localization_bounds(10**16,'1e-10',18,3651)
            scaled = row['scaled_by_log_inverse_width']
            self.assertTrue(arb(scaled['lo']) > arb('0.999999'))
            self.assertTrue(arb(scaled['hi']) < arb('1.001'))

    def test_lower_projection_cost_and_upper_gap_cap(self):
        with ctx.workprec(192):
            row = localization_bounds(32,'1e-10',18,3651)
            self.assertEqual(arb(row['localized_resolvent']['lo']),arb(0))
            self.assertEqual(arb(row['scaled_by_log_inverse_width']['lo']),arb(0))
            self.assertTrue(arb(row['localized_resolvent']['hi']) <= arb('1e10'))


if __name__ == '__main__':
    unittest.main()
