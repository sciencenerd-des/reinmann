"""Held-out small-offset mixtures; forecast must exist before selection."""
import argparse,json
from fractions import Fraction
from pathlib import Path
from flint import ctx,arb
import near_line_mixture_path as path
from full_ground_fourier import sha256
from certified_weil import endpoints
from threshold_ground_gap import box

OUT=Path('research/prime_spectral/verification_2026_10_17_log_forecast')
path.OUT=OUT
path.TARGETS={'b002':'1/500','b001':'1/1000'}
path.SOURCES=path.SOURCES+['held_out_log_mixture_path.py']


def windows(key):
    folder=OUT/key;a=folder/'atlas_H160/atlas.json';r=folder/'atlas_replay.json'
    atlas=json.loads(a.read_text());replay=json.loads(r.read_text())
    if atlas['remaining_count']!=0 or replay['status']!='all_contours_and_root_gates_replayed':raise ValueError('complete replayed atlas required')
    low,high=Fraction(40),Fraction(50);records=[]
    def evaluate(C,N=192):
        d,p=path.trial(key,C,modes=N,bits=4096);records.append({'file':str(p),'sha256':sha256(p),'C':str(C),'modes':N,'status':d['status']});return d['status']
    if evaluate(low)!='positive_finite_sections_only':raise ValueError('initial finite-positive endpoint failed')
    if evaluate(high)!='negative_full_form_trial':raise ValueError('initial negative endpoint failed')
    for _ in range(9):
        mid=(low+high)/2;status=evaluate(mid)
        if status=='negative_full_form_trial':high=mid
        elif status=='positive_finite_sections_only':low=mid
        else:raise ValueError('unresolved support trial')
    forecast=json.loads((OUT/'preregistered_forecast.json').read_text())
    predicted=next(x for x in forecast['targets'] if x['b']==path.TARGETS[key])
    with ctx.workprec(768):
        z=atlas['lowest_right_off_line_zero'];b=box(z['real'])-arb('1/2');gamma=box(z['imag'])
        result={'status':'held_out_N192_support_endpoint_certified','key':key,'b':endpoints(b),'gamma':endpoints(gamma),'positive_finite_evidence_C':str(low),'negative_certificate_C':str(high),'r':endpoints(2*arb.pi()*arb(str(high))/(13*gamma)),'prediction':predicted,'mechanism_error_C':float(high)-predicted['mechanism_C'],'descriptive_error_C':float(high)-predicted['descriptive_C'],'records':records,'input_sha256':{str(p):sha256(p) for p in [a,r,OUT/'preregistered_forecast.json']},'source_sha256':path.sources(),'scope':'Finite-family negative-support upper bound; positive sections are not a lower bound on the full minimum support. Comparison cannot establish an asymptotic law.'}
    (folder/'window_search.json').write_text(json.dumps(result,indent=2)+'\n')
    evaluate(low,256);evaluate(high,256)
    (folder/'N256_endpoint_checks.json').write_text(json.dumps({'records':records[-2:],'scope':'Retained-degree sensitivity only.'},indent=2)+'\n')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--key',choices=path.TARGETS,required=True);p.add_argument('--action',choices=['select','atlas','windows','all'],default='all');a=p.parse_args()
    if not (OUT/'preregistered_forecast.json').exists():raise ValueError('fixed forecast required first')
    if a.action in ['select','all']:path.select(a.key)
    if a.action in ['atlas','all']:path.atlas(a.key)
    if a.action in ['windows','all']:windows(a.key)
