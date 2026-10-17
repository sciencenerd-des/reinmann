"""Compare the final held-out endpoints against immutable forecasts; never refit."""
import json
from fractions import Fraction
from pathlib import Path
from final_log_mixture_path import OUT
from full_ground_fourier import sha256
from freeze_final_log_forecast import mid

def main():
    fp=OUT/'preregistered_forecast.json';f=json.loads(fp.read_text());inputs={str(fp):sha256(fp)};rows=[]
    assert sha256(fp)=='d8dc2a26b3d9981b8df6dab574b9ef708ae993a03065ec697b16ba735f535616'
    for key in ['b0005','b00025']:
        folder=OUT/key;paths=[folder/'window_search.json',folder/'resolution_N256.json',folder/'fresh_witness_replay.json',folder/'atlas_H160/atlas.json',folder/'atlas_replay.json'];s,n,w,a,r=[json.loads(p.read_text()) for p in paths]
        assert a['remaining_count']==0 and r['status']=='all_contours_and_root_gates_replayed'
        assert w['status']=='final_exact_rational_witness_reassembled_at_higher_precision'
        low=float(Fraction(s['positive_finite_evidence_C']));high=float(Fraction(s['negative_certificate_C']));pred=s['prediction']['mechanism_C'];err=high-pred
        passed=abs(err)<=f['acceptance_absolute_C'];bracket_passed=max(abs(low-pred),abs(high-pred))<=f['acceptance_absolute_C']
        rows.append({'key':key,'b':mid(s['b']),'gamma':mid(s['gamma']),'mechanism_C':pred,'descriptive_C':s['prediction']['descriptive_C'],'finite_positive_C_N192':low,'negative_C_N192':high,'negative_C_N256':float(Fraction(n['negative_certificate_C'])),'mechanism_error_C':err,'passes_fixed_endpoint_tolerance':passed,'whole_finite_bracket_within_tolerance':bracket_passed,'r':mid(s['r']),'atlas':{'height':a['height'],'global_count':a['global_count'],'critical_line_count':r['critical_line_count'],'right_off_line_count':r['right_off_line_count']},'witness_replay':w['checked']})
        inputs.update({str(p):sha256(p) for p in paths})
    failed=not all(r['passes_fixed_endpoint_tolerance'] for r in rows)
    d={'status':'final_matched_mechanism_forecast_assessed_without_refit','rows':rows,'fixed_tolerance':f['acceptance_absolute_C'],'all_forecasts_pass':not failed,'forecasting_closed':True,'conclusion':'Final mechanism forecasts failed; retain the logarithmic law as descriptive only and stop forecasting.' if failed else 'Both final finite-family forecasts passed. Forecasting ends with this requested final round; no asymptotic or universal support law is established.','input_sha256':inputs,'source_sha256':{Path(__file__).name:sha256(Path(__file__))},'scope':'Negative cutoffs are certified finite-family support upper bounds; positive finite sections are not full support lower bounds. No post-test refit, extra target, publication or RH claim.'}
    (OUT/'forecast_assessment.json').write_text(json.dumps(d,indent=2)+'\n');print(d['conclusion']);print(json.dumps([{k:r[k] for k in ['key','mechanism_C','negative_C_N192','negative_C_N256','mechanism_error_C','passes_fixed_endpoint_tolerance']} for r in rows],indent=2))
if __name__=='__main__':main()
