"""Assess both frozen models without refitting either forecast."""
import json,math
from fractions import Fraction
from pathlib import Path
import numpy as np
from full_ground_fourier import sha256
from plain_l13_decay import OUT


def midpoint(e):return float((Fraction(e['lo'])+Fraction(e['hi']))/2)


def run():
    fp=OUT/'preregistered_forecast.json';forecast=json.loads(fp.read_text());inputs={str(fp):sha256(fp)};rows=[]
    for key in ['b002','b001']:
        folder=OUT/key;sp=folder/'window_search.json';rp=folder/'resolution_N256.json';wp=OUT/'fresh_witness_replay.json'
        s=json.loads(sp.read_text());r=json.loads(rp.read_text());fresh=json.loads(wp.read_text());target=s['prediction'];C=float(Fraction(s['negative_certificate_C']))
        q=next(x for x in fresh['records'] if x['key']==key)['checked']
        rows.append({'key':key,'b':midpoint(s['b']),'gamma':midpoint(s['gamma']),'C_N192_exact':s['negative_certificate_C'],'C_N192':C,'C_N256_exact':r['negative_certificate_C'],'C_N256':float(Fraction(r['negative_certificate_C'])),'r_N192':midpoint(s['r']),'prediction':target,'signed_errors_C':{model:C-target[model+'_C'] for model in ['mechanism','descriptive']},'within_registered_tolerance':{model:abs(C-target[model+'_C'])<=target['assessment_tolerance_C'] for model in ['mechanism','descriptive']},'fresh_quotients':q})
        inputs.update({str(p):sha256(p) for p in [sp,rp,wp]})
    values=[]
    for C in [40,48,56,64]:
        p=OUT/f'plain_quadratic_L13_C{C}_N192_768bits.json';d=json.loads(p.read_text());values.append(midpoint(d['sectors'][0]['lowest_eigenvalues'][0]));inputs[str(p)]=sha256(p)
    slope,intercept=np.polyfit([40,48,56,64],np.log(values),1)
    result={'status':'both_frozen_log_models_assessed_without_refit','kappa13_primary':forecast['kappa13'],'mechanism_slope_primary':forecast['mechanism_slope'],'rows':rows,'posthoc_wider_C_fit':{'C':[40,48,56,64],'N':192,'kappa':float(-slope),'implied_slope':float(-2/slope),'classification':'post hoc diagnostic, not a forecast'},'observed_step_slope':(rows[1]['C_N192']-rows[0]['C_N192'])/math.log(2),'input_sha256':inputs,'source_sha256':{Path(__file__).name:sha256(Path(__file__))},'conclusion':'The primary plain-L kappa transfer misses both registered tolerances; the descriptive fit misses one and meets one. Both remain finite calibration models. Neither gives a universal exchange law or a full-support minimum.'}
    (OUT/'forecast_assessment.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['kappa13_primary','observed_step_slope','conclusion']},indent=2))


if __name__=='__main__':run()
