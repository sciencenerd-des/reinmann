"""Freeze the final two predictions from the predeclared matched measurements."""
import datetime, hashlib, json, math
from fractions import Fraction
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'research/prime_spectral/verification_2026_10_17_final_mechanism'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def mid(v):return float((Fraction(v['lo'])+Fraction(v['hi']))/2)
def fit(rows):
    x=[r[0] for r in rows];y=[math.log(r[1]) for r in rows];xm=sum(x)/len(x);ym=sum(y)/len(y)
    slope=sum((a-xm)*(b-ym) for a,b in zip(x,y))/sum((a-xm)**2 for a in x)
    return {'negative_log_slope':-slope,'intercept':ym-slope*xm,'adjacent_negative_log_slopes':[-(y[i+1]-y[i])/(x[i+1]-x[i]) for i in range(len(x)-1)],'rows':rows}
def main():
    target=OUT/'preregistered_forecast.json'
    if target.exists():raise FileExistsError('forecast is immutable')
    inputs=[OUT/'measurement_design.json',OUT/'saved_witness_derivatives.json'];spectra={}
    for key in ['b001','b002']:
        for N,grid in [(192,[32,34,36,38,40,42]),(128,[32,38,42])]:
            rows=[]
            for C in grid:
                p=OUT/f'mixture_{key}_C{C}_N{N}_1024bits.json';d=json.loads(p.read_text());inputs.append(p)
                assert all(s['all_finite_eigenvalues_positive'] for s in d['sectors'])
                rows.append([C,min(mid(s['lowest_eigenvalues'][0]) for s in d['sectors'])])
            spectra[f'{key}_N{N}']=fit(rows)
    witnesses=json.loads(inputs[1].read_text())['records'];derivative=fit([[float(Fraction(r['C'])),mid(r['derivative_squared'])] for r in witnesses])
    x=[math.log(1/mid(r['b'])) for r in witnesses];y=[float(Fraction(r['C'])) for r in witnesses];xm=sum(x)/6;ym=sum(y)/6
    ds=sum((a-xm)*(b-ym) for a,b in zip(x,y))/sum((a-xm)**2 for a in x);di=ym-ds*xm
    k=spectra['b001_N192']['negative_log_slope'];kp=derivative['negative_log_slope'];gap=k-kp
    mechanism=2/gap if gap>0 else None
    targets=[{'key':key,'b':b,'mechanism_C':float(Fraction(6015,128))+mechanism*math.log(.001/float(Fraction(b))) if mechanism else None,'descriptive_C':di+ds*math.log(1/float(Fraction(b)))} for key,b in [('b0005','1/2000'),('b00025','1/4000')]]
    result={'status':'final_forecast_fixed_before_target_selection_or_search','recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'kappa':k,'kappa_prime':kp,'kappa_minus_kappa_prime':gap,'mechanism_slope':mechanism,'anchor':{'b':'1/1000','C':'6015/128'},'targets':targets,'acceptance_absolute_C':.25,'matched_spectrum_fits':spectra,'saved_derivative_fit':derivative,'six_point_descriptive_fit':{'slope':ds,'intercept':di},'input_sha256':{str(p.relative_to(ROOT)):digest(p) for p in inputs},'source_sha256':{str(Path(__file__).relative_to(ROOT)):digest(Path(__file__))},'scope':'Predeclared finite-family OLS diagnostics, not rigorous asymptotic exponents. Saved witnesses vary with b and C; neither fit isolates a universal operator mechanism. The 0.25 C tolerance and stop rule are unchanged.'}
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['kappa','kappa_prime','mechanism_slope','targets']},indent=2));print('forecast SHA256',digest(target))
if __name__=='__main__':main()
