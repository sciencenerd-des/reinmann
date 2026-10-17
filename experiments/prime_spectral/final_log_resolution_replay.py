"""Larger retained-degree sensitivity and fresh exact witness reconstruction."""
import argparse,json,sys
from fractions import Fraction
from pathlib import Path
sys.set_int_max_str_digits(0)
from flint import arb,ctx
from final_log_mixture_path import OUT,path
from near_line_mixture_control import MixtureControl
from near_line_window_calibration import matrices
from certified_weil import endpoints
from threshold_ground_gap import box
from full_ground_fourier import sha256

def resolution(key):
    folder=OUT/key;p=folder/'window_search.json';old=json.loads(p.read_text());high=Fraction(old['negative_certificate_C']);step=Fraction(1,2);records=[]
    def evaluate(C):
        d,q=path.trial(key,C,modes=256);records.append({'file':str(q),'sha256':sha256(q),'C':str(C),'status':d['status']});return d['status']
    if evaluate(high)!='negative_full_form_trial':raise ValueError('N256 high endpoint is not negative')
    for _ in range(6):
        low=high-step;status=evaluate(low)
        if status=='positive_finite_sections_only':break
        if status!='negative_full_form_trial':raise ValueError('unresolved sensitivity endpoint')
        high=low;step*=2
    else:raise ValueError('bounded sensitivity search exhausted')
    while high-low>Fraction(1,64):
        mid=(low+high)/2;status=evaluate(mid)
        if status=='negative_full_form_trial':high=mid
        elif status=='positive_finite_sections_only':low=mid
        else:raise ValueError('unresolved sensitivity midpoint')
    result={'status':'N256_finite_family_endpoint_resolved','key':key,'modes':256,'bits':4096,'positive_finite_evidence_C':str(low),'negative_certificate_C':str(high),'records':records,'N192_to_N256_negative_endpoint_difference':str(Fraction(old['negative_certificate_C'])-high),'input_sha256':{str(p):sha256(p)},'source_sha256':{Path(__file__).name:sha256(Path(__file__))},'scope':'Retained-degree sensitivity; finite-positive side is not a minimum-support lower bound.'}
    (folder/'resolution_N256.json').write_text(json.dumps(result,indent=2)+'\n');print(key,'N256 negative',high,flush=True)

def replay(key):
    folder=OUT/key;sp=folder/'window_search.json';s=json.loads(sp.read_text());r=next(r for r in s['records'] if r['C']==s['negative_certificate_C'] and r['modes']==192);p=Path(r['file']);d=json.loads(p.read_text());control=MixtureControl(d['t']);checked=[]
    with ctx.workprec(4352):
        E,O,_=matrices(control,d['C'],d['modes'],d['archimedean_tail_terms'])
        for sector in d['sectors']:
            if 'normalized_full_form' not in sector:continue
            A=E if sector['parity']=='even' else O;v=[arb(x) for x in sector['exact_trial_coefficients']]
            q=sum((v[i]*A[i][j]*v[j] for i in range(len(v)) for j in range(len(v))),arb(0))/sum((x*x for x in v),arb(0))
            if not q<0 or not q.overlaps(box(sector['normalized_full_form'])):raise ValueError('fresh witness reconstruction failed')
            checked.append({'parity':sector['parity'],'quotient':endpoints(q),'quotient_display':q.str(18)})
    if not checked:raise ValueError('no negative witness')
    result={'status':'final_exact_rational_witness_reassembled_at_higher_precision','key':key,'C':d['C'],'bits':4352,'checked':checked,'input_sha256':{str(q):sha256(q) for q in [p,sp]},'source_sha256':{Path(__file__).name:sha256(Path(__file__))},'scope':'Fresh reconstruction on the same Arb backend, not an independent arithmetic implementation.'}
    (folder/'fresh_witness_replay.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',key,'4352bit fresh witness',flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--key',choices=path.TARGETS,required=True);a=p.parse_args();resolution(a.key);replay(a.key)
