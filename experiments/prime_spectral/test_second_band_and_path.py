"""Substantive tail, determinant-boundary and exact-witness replay tests."""
from fractions import Fraction
import json
from pathlib import Path
import unittest
import sys
sys.set_int_max_str_digits(0)  # Trusted, size-bounded 32768-bit certificate endpoints.
from flint import acb,arb,ctx
from character_zero_atlas import CharacterControl
from dh_split_pair_column import reciprocal,small_det
from near_line_mixture_path import OUT,MixtureControl,matrices
from threshold_ground_gap import box


class NewRoundChecks(unittest.TestCase):
    def test_positive_tail_enclosures_against_fresh_radius_value(self):
        d=json.loads((OUT/'dh_coefficients_2050_cauchy_32768bits.json').read_text())
        with ctx.workprec(33280):
            c=CharacterControl(5,2);R=arb(d['radius']);F=c.completed(acb(arb('1/2')+R.sqrt())).real/c.completed(acb('1/2')).real
            self.assertTrue(F.overlaps(box(d['F_radius'])))
            for n,record in enumerate(d['coefficients'][1451:],1451):
                # Stored endpoints must enclose the originally evaluated upper
                # bound, not just overlap a positive middle point.
                upper=Fraction(record['hi']);lo=Fraction(record['lo'])
                original=Fraction(d['F_radius']['hi'])/int(d['radius'])**n
                self.assertLessEqual(lo,0);self.assertGreaterEqual(upper,original)

    def test_both_second_band_boundaries_directly(self):
        d=json.loads((OUT/'dh_coefficients_2050_cauchy_32768bits.json').read_text())
        with ctx.workprec(33280):
            mu=[box(x) for x in d['coefficients']];mu[0]=arb(1);h=reciprocal(mu)
            for rank,sign in [(1535,1),(1536,-1),(1972,-1),(1973,1)]:self.assertTrue(sign*small_det(h,rank)>0)

    def test_three_exact_negative_witnesses_reassembled(self):
        for key in ['b015','b008','b004']:
            folder=OUT/key;summary=json.loads((folder/'window_search.json').read_text());record=next(x for x in summary['records'] if x['C']==summary['negative_certificate_C'])
            d=json.loads(Path(record['file']).read_text());control=MixtureControl(d['t'])
            with ctx.workprec(d['bits']+256):
                E,O,_=matrices(control,d['C'],d['modes'],d['archimedean_tail_terms'])
                checked=0
                for sector in d['sectors']:
                    if 'normalized_full_form' not in sector:continue
                    v=[arb(x) for x in sector['exact_trial_coefficients']];A=E if sector['parity']=='even' else O
                    q=sum((v[i]*A[i][j]*v[j] for i in range(len(v)) for j in range(len(v))),arb(0))/sum((x*x for x in v),arb(0))
                    self.assertTrue(q<0 and q.overlaps(box(sector['normalized_full_form'])));checked+=1
                self.assertGreater(checked,0)


if __name__=='__main__':unittest.main()
