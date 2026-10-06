"""Uniform sign proof for the leading Lambert model, not the full Xi model."""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from flint import arb,ctx
from laboratory import endpoints


def leading_tail(threshold=256):
    X=Fraction(threshold)
    if X<1:
        raise ValueError('threshold >=1 required')
    with ctx.workprec(512):
        x=arb(str(X))
        w=(2*x/arb.pi()).lambertw()
        budget=(2/x+1/x**2)*(1+w)**2
        if not budget<arb('0.5'):
            raise ArithmeticError('uniform leading-model half-margin unresolved')
        return {'threshold':str(X),'budget_upper':str(budget.upper().fmpq()),
                'margin_fraction_lower':str((1-budget).lower().fmpq()),
                'status':'proved_uniform_leading_lambert_model_sign_only',
                'claim':'For every real x>=threshold, f0_second(x)<=-(1-budget_upper)*Q(x)<0, for f0=log((x+1)*(1-exp(-2w/(x*(1+w))))) and Q=(w*w+4*w+1)/(x*x*(1+w)**4).',
                'remaining':'The degree-16 model and true Xi moments require the coupled residual derivative bounds; they are not inferred here.'}


def real_zero_control(x):
    x=Fraction(x)
    if x<3:
        raise ValueError('control domain x>=3 required')
    epsilon=lambda y:(y*y+3*y+1)/(y+1)**2
    curvature=(2*x**3+x**2-8*x-5)/((x+1)**2*(x*x+3*x+1)**2)
    slack=epsilon(x)**2-epsilon(x-1)*epsilon(x+1)
    return {'x':str(x),'epsilon':str(epsilon(x)),
            'continuous_log_curvature':str(curvature),'discrete_logconcavity_slack':str(slack),
            'gamma_turan_difference':'1','double_turan_difference':'0'}


def run():
    return {'schema_version':1,'status':'leading_model_theorem_and_exact_nonimplication_control_not_RH_proof',
            'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                             for name in ('lambert_curvature.py','laboratory.py','coefficients.py')},
            'leading_tail':leading_tail(),
            'control':{'function':'(1+z)*exp(z)','ordinary_coefficients':'(n+1)/n!',
                       'only_zero':'-1','records':[real_zero_control(x) for x in (3,4,10)]},
            'trust_boundary':'Elementary analytic proof in RH_LAMBERT_SIGN_AND_SCOPE_2026_09_15.md plus FLINT threshold evaluation; separate Lean algebra controls.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(result['leading_tail'])
    print(result['control']['records'])


if __name__=='__main__':
    main()
