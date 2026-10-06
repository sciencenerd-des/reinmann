"""Shift-one boundary via reciprocal coefficients and B_r(0)=1."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb,ctx
from laboratory import load_coefficients,complete_symmetric,endpoints,sign,minor
from normalized_recurrence import load_ratios


def boundary_ratios(mu):
    if len(mu)<4 or not all(v>0 for v in mu):
        raise ValueError('four or more positive coefficient balls required')
    h=complete_symmetric([v/mu[0] for v in mu])
    if not all(v>0 for v in h):
        raise ArithmeticError('positive reciprocal coefficients unresolved')
    rows=[]
    ratios={}
    for r in range(1,len(h)-1):
        q=h[r-1]*h[r+1]/h[r]**2
        t=(r+1)*(1-q)
        ratios[r]=t
        rows.append({'rank':r,'normalized_boundary_ratio':endpoints(t),
                     'rank_positive_status':sign(t),'strengthened_boundary_slack':endpoints(1-t),
                     'boundary_status':sign(1-t)})
    # Independent direct determinant checks of the dual identities.
    for r in sorted({r for r in (1,2,3,12) if r<=len(h)-2}):
        if not h[r].overlaps(minor(mu,r,1)):
            raise ArithmeticError('first-column dual identity disagreement')
        if not (h[r]**2-h[r-1]*h[r+1]).overlaps(minor(mu,r,2)):
            raise ArithmeticError('second-column dual identity disagreement')
    return ratios,rows


def boundary_prefixes(boundary,interior):
    if 1 not in boundary or not 0<boundary[1]<1:
        raise ArithmeticError('positive base boundary curvature unresolved')
    base=-boundary[1].log()
    total,loss=arb(0),arb(0)
    rows=[]
    r=1
    while r in boundary and r+1 in boundary and (r,2) in interior:
        now,nxt=boundary[r],boundary[r+1]
        previous=arb(1) if r==1 else boundary[r-1]
        if not all(v>0 for v in (now,nxt,previous,interior[r,2])):
            raise ArithmeticError('positive boundary ratios unresolved')
        b1=1+(1-now)/r
        b2=1+arb(2)/r*(1-interior[r,2])
        if not b1>0 or not b2>0:
            raise ArithmeticError('positive boundary factors unresolved')
        correction=2*b1.log()-b2.log()  # B_r(0)=1 exactly.
        predicted=now**2/previous*b2/b1**2
        if not predicted.overlaps(nxt):
            raise ArithmeticError('boundary rank transport disagreement')
        total+=correction
        loss+=(-correction).max(arb(0))
        slope=base+total
        if not slope.overlaps(-nxt.log()+now.log()):
            raise ArithmeticError('boundary cumulative slope disagreement')
        rows.append({'last_correction_rank':r,'correction':endpoints(correction),
                     'negative_loss_over_base':endpoints(loss/base),
                     'half_base_budget':endpoints(base/2-loss),'budget_status':sign(base/2-loss)})
        r+=1
    if not rows:
        raise ValueError('no boundary prefixes available')
    return rows


def run(coefficients_path,laboratory_path):
    ctx.prec=2048
    raw=laboratory_path.read_bytes()
    data=json.loads(raw)
    digest=hashlib.sha256(coefficients_path.read_bytes()).hexdigest()
    if data.get('input_sha256')!=digest:
        raise ValueError('coefficient provenance mismatch')
    mu,_=load_coefficients(coefficients_path)
    ratios,rows=boundary_ratios(mu)
    prefixes=boundary_prefixes(ratios,load_ratios(data))
    return {'schema_version':1,'status':'finite_boundary_checks_not_uniform_rank_proof',
            'coefficient_input_sha256':digest,'laboratory_input_sha256':hashlib.sha256(raw).hexdigest(),
            'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                             for name in ('boundary_budget.py','normalized_recurrence.py','laboratory.py','coefficients.py')},
            'boundary_rows':rows,'boundary_prefixes':prefixes,
            'remaining':'Uniform positivity and reciprocal-coefficient ratio band, and cumulative budget for every rank.',
            'trust_boundary':'FLINT coefficient balls and dual determinant algebra; no all-rank analytic estimate.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients',type=Path,required=True)
    parser.add_argument('--laboratory',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run(args.coefficients,args.laboratory)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(len(result['boundary_rows']),'boundary ranks;',len(result['boundary_prefixes']),'prefixes')
    print('positive budgets',sum(v['budget_status']=='positive' for v in result['boundary_prefixes']))


if __name__=='__main__':
    main()
