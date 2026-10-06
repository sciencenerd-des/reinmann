"""High-rank, small-shift budget checks via dual Jacobi-Trudi determinants."""
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb,arb_mat,ctx
from laboratory import load_coefficients,complete_symmetric,minor
from tail_and_rank_budget import cumulative_budgets
from boundary_budget import boundary_ratios,boundary_prefixes


def dual_grid(mu,max_rank=113,max_shift=7):
    if not 1<=max_rank or not 2<=max_shift or max_rank+max_shift+1>len(mu):
        raise ValueError('dual grid exceeds coefficient range')
    h=complete_symmetric([v/mu[0] for v in mu])
    d={}
    for r in range(1,max_rank+1):
        for m in range(max_shift+2):
            d[r,m]=arb(1) if m==0 else arb_mat([
                [h[r+i-j] if r+i-j>=0 else arb(0) for j in range(m)] for i in range(m)]).det()
            if not d[r,m]>0:
                raise ArithmeticError('dual determinant positivity unresolved')
    t={(r,m):arb(r+m)/m*d[r,m-1]*d[r,m+1]/d[r,m]**2
       for r in range(1,max_rank+1) for m in range(1,max_shift+1)}
    for r,m in ((1,1),(2,2),(min(12,max_rank),min(4,max_shift))):
        if r<=max_rank and m<=max_shift and not d[r,m].overlaps(minor(mu,r,m)):
            raise ArithmeticError('dual/direct determinant disagreement')
    return t


def run(path):
    ctx.prec=2048
    mu,_=load_coefficients(path)
    ratios=dual_grid(mu)
    interior=cumulative_budgets(ratios)
    boundary,_=boundary_ratios(mu)
    prefixes=boundary_prefixes(boundary,ratios)
    return {'schema_version':1,'status':'finite_dual_rank_budget_not_uniform_proof',
            'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                             for name in ('dual_rank_budget.py','boundary_budget.py','tail_and_rank_budget.py',
                                          'normalized_recurrence.py','laboratory.py','coefficients.py')},
            'max_rank':113,'max_ratio_shift':7,'interior_prefixes':interior,'boundary_prefixes':prefixes,
            'trust_boundary':'FLINT coefficient balls and dual determinant identities; bounded ranks and shifts only.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run(args.coefficients)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(len(result['interior_prefixes']),'interior prefixes;',len(result['boundary_prefixes']),'boundary prefixes')
    print('all budgets positive',all(r['budget_status']=='positive' for r in result['interior_prefixes']+result['boundary_prefixes']))


if __name__=='__main__':
    main()
