"""Higher-precision reconstruction of held-out exact rational witnesses."""
from pathlib import Path
import json,sys
sys.set_int_max_str_digits(0)
from flint import arb,ctx
from near_line_mixture_control import MixtureControl
from near_line_window_calibration import matrices
from threshold_ground_gap import box
from certified_weil import endpoints
from full_ground_fourier import sha256
from plain_l13_decay import OUT


def run():
    rows=[]
    for key in ['b002','b001']:
        folder=OUT/key;summary_path=folder/'window_search.json';summary=json.loads(summary_path.read_text())
        record=next(r for r in summary['records'] if r['C']==summary['negative_certificate_C'] and r['modes']==192)
        p=Path(record['file']);d=json.loads(p.read_text());control=MixtureControl(d['t'])
        with ctx.workprec(d['bits']+256):
            E,O,_=matrices(control,d['C'],d['modes'],d['archimedean_tail_terms'])
            checked=[]
            for sector in d['sectors']:
                if 'normalized_full_form' not in sector:continue
                A=E if sector['parity']=='even' else O;v=[arb(x) for x in sector['exact_trial_coefficients']]
                q=sum((v[i]*A[i][j]*v[j] for i in range(len(v)) for j in range(len(v))),arb(0))/sum((x*x for x in v),arb(0))
                if not q<0 or not q.overlaps(box(sector['normalized_full_form'])):raise ValueError('fresh negative witness replay failed')
                checked.append({'parity':sector['parity'],'quotient':endpoints(q),'quotient_display':q.str(18)})
            if not checked:raise ValueError('no negative witness')
        rows.append({'key':key,'C':d['C'],'bits':d['bits']+256,'checked':checked,'input_sha256':{str(q):sha256(q) for q in [p,summary_path]}})
        print('PASS',key,'fresh exact rational witness at',d['bits']+256,'bits',flush=True)
    result={'status':'both_held_out_exact_witnesses_reassembled_at_higher_precision','records':rows,'source_sha256':{Path(__file__).name:sha256(Path(__file__))},'scope':'Same Arb backend and closed generator, independently reconstructed rational trial; not a second arithmetic implementation or a full-support lower bound.'}
    (OUT/'fresh_witness_replay.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':run()
