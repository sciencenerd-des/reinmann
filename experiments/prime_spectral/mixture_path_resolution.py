"""N256 finite-family endpoint sensitivity, never a full-support lower bound."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
from near_line_mixture_path import OUT,trial
from full_ground_fourier import sha256


def run(key):
    folder=OUT/key;p=folder/'window_search.json';old=json.loads(p.read_text());high=Fraction(old['positive_finite_evidence_C']);step=Fraction(1,2);records=[]
    def evaluate(C):
        d,path=trial(key,C,modes=256);records.append({'file':str(path),'sha256':sha256(path),'C':str(C),'status':d['status']});return d['status']
    if evaluate(high)!='negative_full_form_trial':raise ValueError('existing N256 upper endpoint not negative')
    for _ in range(6):
        low=high-step;status=evaluate(low)
        if status=='positive_finite_sections_only':break
        if status!='negative_full_form_trial':raise ArithmeticError('unresolved trial')
        high=low;step*=2
    else:raise ArithmeticError('bounded finite resolution search exhausted')
    for _ in range(6):
        mid=(low+high)/2;status=evaluate(mid)
        if status=='negative_full_form_trial':high=mid
        elif status=='positive_finite_sections_only':low=mid
        else:raise ArithmeticError('unresolved midpoint')
    result={'status':'N256_finite_family_endpoint_resolved','key':key,'modes':256,'bits':4096,'positive_finite_evidence_C':str(low),'negative_certificate_C':str(high),'records':records,
            'N192_to_N256_negative_endpoint_difference':str(Fraction(old['negative_certificate_C'])-high),
            'input_sha256':{str(p):sha256(p)},'source_sha256':{Path(__file__).name:sha256(Path(__file__))},
            'scope':'Finite-family resolution sensitivity; positive endpoint does not certify a full positive window or bound minimum support.'}
    (folder/'resolution_N256.json').write_text(json.dumps(result,indent=2)+'\n');print(key,'N256 negative',high,'positive finite',low,flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--key',choices=['b015','b008','b004'],required=True);run(p.parse_args().key)
