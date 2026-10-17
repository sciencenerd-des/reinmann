"""Freeze plain-control and descriptive forecasts before either target is computed."""
from pathlib import Path
from fractions import Fraction
import datetime,json,math
import numpy as np
from full_ground_fourier import sha256
from plain_l13_decay import OUT


def midpoint(e):return (float(Fraction(e['lo']))+float(Fraction(e['hi'])))/2


def freeze():
    p=OUT/'preregistered_forecast.json'
    if p.exists():raise FileExistsError('Forecast already fixed; do not rewrite it')
    records=[];inputs={};fits={}
    for N in [96,128]:
        rows=[]
        for C in [16,20,24,28,32]:
            q=OUT/f'plain_quadratic_L13_C{C}_N{N}_768bits.json';d=json.loads(q.read_text());inputs[str(q)]=sha256(q)
            values={s['parity']:[midpoint(x) for x in s['lowest_eigenvalues']] for s in d['sectors']}
            rows.append({'C':C,'ground':min(values['even'][0],values['odd'][0]),**values})
        def fit(vals):
            x=np.array([r['C'] for r in rows]);y=np.log(vals);a,b=np.polyfit(x,y,1)
            return {'kappa':float(-a),'intercept':float(b),'log_RMSE':float(np.sqrt(np.mean((y-a*x-b)**2))),'adjacent_slopes':[float(-(y[i+1]-y[i])/(x[i+1]-x[i])) for i in range(len(x)-1)]}
        fits[str(N)]={'ground':fit([r['ground'] for r in rows]),'parities':{s:[fit([r[s][j] for r in rows]) for j in range(3)] for s in ['even','odd']}}
        records.append({'N':N,'rows':rows})
    k=fits['128']['ground']['kappa'];slope=2/k
    targets=[]
    for b in [Fraction(1,500),Fraction(1,1000)]:
        mechanism=float(Fraction(1373,32))+slope*math.log(float(Fraction(1,250)/b))
        descriptive=37.296088+2.885535*math.log(.03/float(b))
        targets.append({'b':str(b),'mechanism_C':mechanism,'descriptive_C':descriptive,'assessment_tolerance_C':.25})
    result={'status':'forecasts_fixed_before_target_parameter_selection_atlases_and_windows','recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'control':'primitive even real quadratic Conrey(13,12), actual single Euler-product L-function','kappa13':k,'mechanism_slope':slope,'fits':fits,'measurement_rows':records,'targets':targets,'anchor':{'b':'1/250','C':'1373/32','modes':192},'protocol':'Complete H160 atlas and replay before either target window. Common N192 with 4096-bit exact-rational witnesses; bisect support to 1/32, then N256 endpoints. Positive finite sections give no full-support lower bound. Forecasts remain fixed even on failure.','input_sha256':inputs,'source_sha256':{'preregister_log_forecast.py':sha256(Path(__file__))},'limits':'Local timestamp only, not a public preregistration. Finite-control kappa, short C range, finite-family eigenvalues, even/odd gamma mismatch and conductor-only transfer all limit interpretation. Agreement cannot establish a universal two-term theorem.'}
    p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'kappa13':k,'slope':slope,'targets':targets},indent=2))


if __name__=='__main__':freeze()
