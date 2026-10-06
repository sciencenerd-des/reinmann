"""Certified finite curvature transport; no all-rank propagation claim."""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
from flint import arb, ctx
from laboratory import endpoints, interval, sign, load_coefficients, minor


def transport(r, m, previous, center, left, right):
    """Inputs are neighboring normalized determinant ratios t, all positive."""
    if r < 1 or m < 2 or not all(v > 0 for v in (previous, center, left, right)):
        raise ValueError('positive ratios and interior rank/shift required')
    factors = [1+arb(j)/r*(1-v) for j,v in ((m-1,left),(m,center),(m+1,right))]
    if not all(v > 0 for v in factors):
        raise ArithmeticError('positive correction factor unresolved')
    correction = 2*factors[1].log()-factors[0].log()-factors[2].log()
    inherited = -2*center.log()+previous.log()
    predicted = center**2/previous*factors[0]*factors[2]/factors[1]**2
    return predicted, inherited, correction


def load_ratios(data):
    if data.get('schema_version') != 1 or data.get('status') != 'finite_ball_results_not_unbounded_order_proof':
        raise ValueError('unsupported laboratory provenance')
    ratios = {}
    for row in data['recurrence_windows']:
        r,m = row['rank'],row['shift']
        if type(r) is not int or type(m) is not int or min(r,m)<1 or (r,m) in ratios:
            raise ValueError('invalid or duplicate rank/shift')
        slack = interval(row['candidate_slack'])
        eta = interval(row['relative_margin'])
        if not (eta-arb(r)/(m+r)).overlaps(slack):
            raise ValueError('inconsistent candidate and raw margins')
        # eta = 1 - D_left D_right / D_center^2.
        value = 1-arb(m+r)/m*slack
        if not value > 0:
            raise ArithmeticError('positive normalized ratio unresolved')
        ratios[r,m] = value
    if not ratios:
        raise ValueError('empty recurrence table')
    return ratios


def run(laboratory_path, coefficients_path):
    ctx.prec = 2048
    raw = laboratory_path.read_bytes()
    data = json.loads(raw)
    coefficient_hash = hashlib.sha256(coefficients_path.read_bytes()).hexdigest()
    if data.get('input_sha256') != coefficient_hash:
        raise ValueError('laboratory and coefficient input hashes differ')
    mu,_ = load_coefficients(coefficients_path)
    ratios = load_ratios(data)
    rows = []
    for (r,m),center in sorted(ratios.items()):
        keys = ((r-1,m),(r+1,m),(r,m-1),(r,m+1))
        if r<2 or m<2 or any(key not in ratios for key in keys):
            continue
        previous, actual, left, right = (ratios[key] for key in keys)
        predicted, inherited, correction = transport(r,m,previous,center,left,right)
        if not predicted.overlaps(actual):
            raise ArithmeticError('normalized recurrence disagrees with determinant data')
        total = inherited+correction
        if not total.overlaps(-actual.log()):
            raise ArithmeticError('logarithmic transport disagrees')
        rows.append({'rank':r, 'shift':m, 'inherited_curvature':endpoints(inherited),
                     'correction_curvature':endpoints(correction), 'transported_curvature':endpoints(total),
                     'correction_status':sign(correction), 'transport_status':sign(total)})
    if not rows:
        raise ValueError('no complete interior transport windows')
    negative = next((row for row in rows if row['correction_status']=='negative'),None)
    direct = None
    if negative:
        r,m = negative['rank'],negative['shift']
        direct_ratios = {}
        for j in (m-1,m,m+1):
            a,b,c = (minor(mu,r,k) for k in (j-1,j,j+1))
            if not all(v>0 for v in (a,b,c)):
                raise ArithmeticError('direct positive determinant unresolved')
            direct_ratios[j] = arb(j+r)/j*a*c/b**2
        factors = [1+arb(j)/r*(1-direct_ratios[j]) for j in (m-1,m,m+1)]
        if not all(v>0 for v in factors):
            raise ArithmeticError('direct correction domain unresolved')
        curvature = 2*factors[1].log()-factors[0].log()-factors[2].log()
        if not curvature < 0 or not curvature.overlaps(interval(negative['correction_curvature'])):
            raise ArithmeticError('negative correction not independently reproduced from coefficients')
        direct = {'rank':r,'shift':m,'correction_curvature':endpoints(curvature),
                  'status':sign(curvature),'method':'fresh determinants from coefficient balls; shared FLINT trust'}
    return {'schema_version':1,'status':'finite_curvature_transport_not_unbounded_proof',
            'laboratory_input_sha256':hashlib.sha256(raw).hexdigest(), 'coefficient_input_sha256':coefficient_hash,
            'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                             for name in ('normalized_recurrence.py','laboratory.py','coefficients.py')},
            'working_bits':ctx.prec,'window_count':len(rows),
            'correction_counts':dict(Counter(v['correction_status'] for v in rows)),
            'transport_counts':dict(Counter(v['transport_status'] for v in rows)),
            'direct_negative_check':direct,'windows':rows,
            'trust_boundary':'FLINT coefficient enclosures and classical determinant algebra; numerical overlap checks are not identity proofs.',
            'remaining':'Uniform lower bound for inherited plus correction curvature at all ranks and shifts, with separate boundary control.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--laboratory',type=Path,required=True)
    parser.add_argument('--coefficients',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    result = run(args.laboratory,args.coefficients)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(result['window_count'],result['correction_counts'],result['transport_counts'])
    print(result['direct_negative_check'])


if __name__ == '__main__':
    main()
