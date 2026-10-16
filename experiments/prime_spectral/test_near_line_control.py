"""Independent geometric and normalization checks for the small-offset control."""
import json
from pathlib import Path
import unittest
from flint import acb,arb,ctx
from near_line_mixture_control import OUT,MixtureControl
from near_line_window_calibration import matrices
from dh_weil_certificate import geometric_entry
from davenport_heilbronn_control import log_derivative_coefficients
from threshold_ground_gap import box


class NearLineChecks(unittest.TestCase):
    def control(self):
        return MixtureControl(json.loads((OUT/'near_line_mixture_definition.json').read_text())['t'])

    def test_normalization_and_functional_equation(self):
        with ctx.workprec(512):
            c=self.control()
            self.assertEqual(c.parameters()[2][1],arb(1))
            self.assertTrue(sum(c.parameters()[2],arb(0)).contains(0))
            for s in [acb('.7','12'),acb('.3','40'),acb('1.3','23')]:
                self.assertTrue((c.completed(s)-c.completed(1-s)).contains(0))

    def test_entries_against_independent_geometric_integral(self):
        with ctx.workprec(768):
            c=self.control();C='13/2';S=arb(C).log()
            _,_,cell=matrices(c,C,4,160)
            a=c.parameters()[2];coef=log_derivative_coefficients([arb(0)]+[a[n%13] for n in range(1,8)])
            for m,n in [(0,0),(2,0),(2,2),(2,-2)]:
                direct=geometric_entry(m,n,S,coef,7)+(arb(13)/5).log()*(m==n)
                self.assertTrue(direct.overlaps(cell(m,n)))

    def test_negative_witness_reassembled_at_higher_precision(self):
        summary=json.loads((OUT/'mixture13_windows/search_N192_2048bits.json').read_text())
        rec=next(x for x in summary['records'] if x['C']==summary['negative_certificate_C'])
        data=json.loads(Path(rec['file']).read_text())
        with ctx.workprec(data['bits']+128):
            c=self.control();E,O,_=matrices(c,data['C'],data['modes'],data['archimedean_tail_terms'])
            for sector in data['sectors']:
                if 'normalized_full_form' not in sector:continue
                v=[arb(x) for x in sector['exact_trial_coefficients']];A=E if sector['parity']=='even' else O
                quotient=sum((v[i]*A[i][j]*v[j] for i in range(len(v)) for j in range(len(v))),arb(0))/sum((x*x for x in v),arb(0))
                self.assertTrue(quotient<0 and quotient.overlaps(box(sector['normalized_full_form'])))


if __name__=='__main__':
    unittest.main()
