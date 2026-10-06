"""Finite tests of a saddle curvature scale and cumulative rank budgets.

No fitted error bar is used. Certified samples do not certify an infinite tail.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb,ctx
from laboratory import load_coefficients, endpoints, sign
from normalized_recurrence import load_ratios, transport


def saddle_scale(x):
    x=arb(x)
    if not x>0:
        raise ValueError('positive saddle parameter required')
    w=(2*x/arb.pi()).lambertw()
    epsilon=2*w/(1+w)
    curvature=(w*w+4*w+1)/(x*x*(1+w)**4)
    if not epsilon>0 or not curvature>0:
        raise ArithmeticError('saddle domain unresolved')
    return epsilon,curvature


def discrete_samples(mu):
    if len(mu)<5 or not all(v>0 for v in mu):
        raise ValueError('five or more positive coefficient balls required')
    eps={m:(m+1)*(1-mu[m-1]*mu[m+1]/mu[m]**2) for m in range(1,len(mu)-1)}
    if not all(v>0 for v in eps.values()):
        raise ArithmeticError('positive deficit unresolved')
    rows=[]
    for m in range(2,len(mu)-2):
        model,scale=saddle_scale(m)
        curvature=2*eps[m].log()-eps[m-1].log()-eps[m+1].log()
        rows.append({'shift':m,'epsilon':endpoints(eps[m]),'model_epsilon':endpoints(model),
                     'discrete_log_curvature':endpoints(curvature),'model_curvature_scale':endpoints(scale),
                     'curvature_to_scale_ratio':endpoints(curvature/scale),'status':sign(curvature)})
    return rows


def cumulative_budgets(ratios):
    """Only contiguous rank prefixes are allowed; every prefix starts at rank 1."""
    rows=[]
    for m in sorted({m for r,m in ratios if r==1 and m>=2}):
        base=-ratios[1,m].log()
        if not base>0:
            raise ArithmeticError('positive rank-one curvature unresolved')
        cumulative,loss=arb(0),arb(0)
        k=1
        while all(key in ratios for key in ((k,m),(k+1,m),(k,m-1),(k,m+1))):
            previous=arb(1) if k==1 else ratios[k-1,m]
            predicted,_,correction=transport(k,m,previous,ratios[k,m],ratios[k,m-1],ratios[k,m+1])
            if not predicted.overlaps(ratios[k+1,m]):
                raise ArithmeticError('rank ratio disagreement')
            cumulative+=correction
            loss+=(-correction).max(arb(0))
            slope=base+cumulative
            actual=-ratios[k+1,m].log()+ratios[k,m].log()
            if not slope.overlaps(actual):
                raise ArithmeticError('cumulative slope disagreement')
            budget=base/2-loss
            rows.append({'shift':m,'last_correction_rank':k,'next_rank':k+1,
                         'cumulative_correction':endpoints(cumulative),
                         'slope':endpoints(slope),'slope_status':sign(slope),
                         'negative_loss_over_base':endpoints(loss/base),
                         'half_base_loss_budget':endpoints(budget),'budget_status':sign(budget)})
            k+=1
    if not rows:
        raise ValueError('no contiguous interior rank prefixes')
    return rows


def run(coefficients_path,laboratory_path):
    ctx.prec=2048
    raw=laboratory_path.read_bytes()
    data=json.loads(raw)
    digest=hashlib.sha256(coefficients_path.read_bytes()).hexdigest()
    if data.get('input_sha256')!=digest:
        raise ValueError('coefficient provenance mismatch')
    mu,_=load_coefficients(coefficients_path)
    samples=discrete_samples(mu)
    budgets=cumulative_budgets(load_ratios(data))
    return {'schema_version':1,'status':'finite_saddle_and_cumulative_budget_checks_not_tail_proof',
            'coefficient_input_sha256':digest,'laboratory_input_sha256':hashlib.sha256(raw).hexdigest(),
            'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                             for name in ('tail_and_rank_budget.py','normalized_recurrence.py','laboratory.py','coefficients.py')},
            'saddle_samples':samples,'cumulative_budgets':budgets,
            'remaining':'No explicit asymptotic threshold, differentiated theta remainder, or all-rank summable loss bound has been established.',
            'trust_boundary':'FLINT coefficient balls and classical algebra; sampled model agreement is not an asymptotic error estimate.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients',type=Path,required=True)
    parser.add_argument('--laboratory',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run(args.coefficients,args.laboratory)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(len(result['saddle_samples']),'saddle samples;',len(result['cumulative_budgets']),'rank prefixes')
    print('positive half-base budgets',sum(v['budget_status']=='positive' for v in result['cumulative_budgets']))


if __name__=='__main__':
    main()
