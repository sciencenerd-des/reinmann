"""Matched mixture decay and saved-witness derivative calibration.

All inputs predate the final two held-out parameters. Finite spectra and a
fitted balance model are not full-operator decay or infinite-tail theorems.
"""
import argparse,datetime,json,math,sys,time
sys.set_int_max_str_digits(0)
from fractions import Fraction
from pathlib import Path
from flint import acb,acb_series,arb,arb_mat,ctx
import numpy as np
from near_line_mixture_control import MixtureControl
from near_line_window_calibration import matrices
from certified_weil import endpoints
from threshold_ground_gap import box
from full_ground_fourier import sha256

OUT=Path('research/prime_spectral/verification_2026_10_17_final_mechanism')
PREV=Path('research/prime_spectral/verification_2026_10_17_log_forecast')
ROUND2=Path('research/prime_spectral/verification_2026_10_15_second_band')
ROUND1=Path('research/prime_spectral/verification_2026_10_15_split_pair')


def sources():return {n:sha256(Path(__file__).with_name(n)) for n in ['final_log_mechanism.py','near_line_window_calibration.py','near_line_mixture_control.py','control_window_calibration.py','control_zero_attribution.py']}


def design():
    p=OUT/'measurement_design.json'
    if p.exists():raise FileExistsError('fixed design already exists')
    d={'status':'final_mechanism_design_fixed_before_measurements_and_future_targets','recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'matched_controls':['b001','b002'],'C_grid':[32,34,36,38,40,42],'modes_primary':192,'modes_sensitivity':128,'sensitivity_C':[32,38,42],'bits':1024,'primary_kappa':'OLS negative slope of log lowest finite eigenvalue vs C for fixed b001 mixture, common N192; both parity blocks must be positive','kappa_prime':'OLS negative slope of log normalized squared transform derivative at the lowest pair height, across all six saved N192 negative witnesses b030,b015,b008,b004,b002,b001; display adjacent slopes and transform value as diagnostics','prediction':'Anchor C=6015/128 at b=1/1000; slope=2/(kappa-kappa_prime) if positive. If nonpositive or unresolved, explicitly mark mechanism unavailable and use the six-point descriptive model only as fallback, with no mechanism-success claim. No target parameter or trial before fixed forecast JSON.','targets':['1/2000','1/4000'],'acceptance_absolute_C':0.25,'window_protocol':'Complete replayed H160 atlas before each target search. Common N1924096bit trials; start48 and56, expand high to at most128 if needed; bisect to width<=1/32; N256 sensitivity and4352bit witness reconstruction.','stop_rule':'If either final mechanism forecast misses its fixed tolerance, or the mechanism is undefined, stop mechanism forecasting and retain log law as descriptive only. No refit or further held-out target.','source_sha256':sources()}
    OUT.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')


def measure(key):
    definition=PREV/key/'definition.json';d=json.loads(definition.read_text());control=MixtureControl(d['t'])
    for N in [192,128]:
        for C in ([32,34,36,38,40,42] if N==192 else [32,38,42]):
            path=OUT/f'mixture_{key}_C{C}_N{N}_1024bits.json'
            if path.exists():continue
            start=time.monotonic()
            with ctx.workprec(1024):
                terms=max(32,math.ceil((1024*math.log(2)+20)/(2*float(arb(C).log().lower()))))
                E,O,_=matrices(control,str(C),N,terms);sectors=[]
                for parity,A in [('even',E),('odd',O)]:
                    vals=arb_mat(A).eig();assert all(v.imag.contains(0) for v in vals)
                    vals=sorted([v.real for v in vals],key=lambda x:float(x.mid()))
                    if any(not v>0 for v in vals):raise ValueError('positive matched-control spectrum unresolved')
                    sectors.append({'parity':parity,'lowest_eigenvalues':[endpoints(v) for v in vals[:4]],'lowest_display':[v.str(20) for v in vals[:4]],'all_finite_eigenvalues_positive':True})
                result={'status':'positive_matched_mixture_finite_spectrum_enclosed','key':key,'t':d['t'],'C':C,'modes':N,'bits':1024,'sectors':sectors,'seconds':time.monotonic()-start,'input_sha256':{str(p):sha256(p) for p in [definition,OUT/'measurement_design.json']},'source_sha256':sources(),'scope':'Same conductor and odd gamma as the mixture; finite spectra below detection, not full positivity or a limiting spectral exponent.'}
            path.write_text(json.dumps(result,indent=2)+'\n');print(key,C,N,sectors[0]['lowest_display'][0],flush=True)


def transform_jet(z,length,v,parity):
    old=ctx.cap
    try:
        ctx.cap=3;w=acb_series([z,1])*length/2
        if parity=='even':
            value=v[0]/w
            for n in range(1,len(v)):value+=arb(2).sqrt()*v[n]*w/(w*w+(arb.pi()*n)**2)
            return length.sqrt()*w.sinh()*value
        value=sum((v[n-1]*arb.pi()*n/(w*w+(arb.pi()*n)**2) for n in range(1,len(v)+1)),acb_series([0]))
        return -(2*length).sqrt()*w.sinh()*value
    finally:ctx.cap=old


def witness_decay():
    paths=[('b030',ROUND1/'mixture13_windows/search_N192_2048bits.json',ROUND1/'mixture13_H160/atlas.json')]
    paths += [(key,ROUND2/key/'window_search.json',ROUND2/key/'atlas_H160/atlas.json') for key in ['b015','b008','b004']]
    paths += [(key,PREV/key/'window_search.json',PREV/key/'atlas_H160/atlas.json') for key in ['b002','b001']]
    rows=[];inputs={str(OUT/'measurement_design.json'):sha256(OUT/'measurement_design.json')}
    for key,sp,ap in paths:
        s=json.loads(sp.read_text());C=s['negative_certificate_C'];tp=Path(next(r['file'] for r in s['records'] if r['C']==C and r['status']=='negative_full_form_trial'))
        d=json.loads(tp.read_text());atlas=json.loads(ap.read_text());z=atlas['lowest_right_off_line_zero']
        with ctx.workprec(3072):
            gamma=box(z['imag'])+arb(0,arb(z['radius']));b=box(z['real'])-arb('1/2')+arb(0,arb(z['radius']));length=arb(C).log()
            sector=next(q for q in d['sectors'] if 'normalized_full_form' in q)
            v=[arb(x) for x in sector['exact_trial_coefficients']];norm=sum((x*x for x in v),arb(0)).sqrt();v=[x/norm for x in v]
            jet=transform_jet(acb(0,gamma),length,v,sector['parity']);D=abs(jet[1])**2
            if not D>0:raise ValueError('positive derivative norm unresolved')
            from control_zero_attribution import transform
            off=transform(acb(b,gamma),length,v,sector['parity']);sign=1 if sector['parity']=='even' else -1
            quartet=4*sign*(off*off).real
            rows.append({'key':key,'C':C,'b':endpoints(b),'gamma':endpoints(gamma),'parity':sector['parity'],'vector_dimension':len(v),'derivative_squared':endpoints(D),'derivative_squared_display':D.str(20),'center_value_squared':endpoints(abs(jet[0])**2),'exact_finite_quartet':endpoints(quartet),'leading_negative_approximation':endpoints(-4*b*b*D),'scope':'Saved unit-L2 rational witness derivative at its own lowest-pair height; no independent infinite-tail attribution.'})
        inputs.update({str(p):sha256(p) for p in [sp,ap,tp]});print(key,C,'derivative squared',rows[-1]['derivative_squared_display'],flush=True)
    result={'status':'all_six_saved_normalized_witness_derivatives_enclosed','records':rows,'input_sha256':inputs,'source_sha256':sources()}
    (OUT/'saved_witness_derivatives.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('action',choices=['design','b001','b002','derivatives']);a=p.parse_args()
    if a.action=='design':design()
    elif a.action=='derivatives':witness_decay()
    else:measure(a.action)
