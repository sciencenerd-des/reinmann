"""Effective first-summand moments using saddle-centered quadrature and tangent tails.

The tails are analytic bounds, not fitted Laplace errors. Each run certifies
only its listed points, not the unbounded continuum or an asymptotic model.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from flint import arb,acb,ctx
from laboratory import endpoints
from effective_theta_remainder import uniform_bound
from curvature_error import propagate_moment_errors


def phase(t,x):
    u=t.exp()
    return (2*x+1)*t+arb(9)*u/2-arb.pi()*(2*u).exp()


def phase_slope(t,x):
    u=t.exp()
    return 2*x+1+arb(9)*u/2-2*arb.pi()*u*(2*u).exp()


def polynomial_tangent_tail(endpoint,slope,exponent,k):
    if not slope>0 or type(k) is not int or not 0<=k<=2:
        raise ValueError('positive decay rate and moment order 0..2 required')
    # Integral_0^infinity exp(-slope*v) (2(|endpoint|+v))^k dv.
    return exponent.exp()*2**k*sum((arb(math.factorial(k)//math.factorial(k-j))*
        abs(endpoint)**(k-j)/slope**(j+1) for j in range(k+1)),arb(0))


def first_summand_models(x,spread=16):
    x=arb(x)
    if not x.is_finite() or not x>=256 or not 4<=spread<=64:
        raise ValueError('finite x>=256 and spread 4..64 required')
    u=(2*x/arb.pi()).lambertw()/2
    center=u.log()
    second=arb(9)*u/2-2*arb.pi()*u*(2*u).exp()*(1+2*u)
    if not second<0:
        raise ArithmeticError('negative phase curvature unresolved')
    width=arb(spread)/(-second).sqrt()
    left,right=center-width,center+width
    p0=phase(center,x)
    left_rate,right_rate=phase_slope(left,x),-phase_slope(right,x)
    if not left_rate>0 or not right_rate>0:
        raise ArithmeticError('tangent tail slope signs unresolved')
    scale=4*arb.pi()**2*p0.exp()
    models,errors,records=[],[],[]
    for k in range(3):
        def integrand(t,_analytic):
            u=t.exp()
            return (phase(t,x)-p0).exp()*(1-3/(2*arb.pi())*(-2*u).exp())*(2*t)**k
        finite=acb.integral(integrand,left,right,rel_tol=arb(2)**-120,
                            abs_tol=arb(2)**-140,eval_limit=300000,depth_limit=50)
        if not finite.is_finite() or not finite.imag.contains(0):
            raise ArithmeticError('saddle quadrature unresolved')
        tail_left=polynomial_tangent_tail(left,left_rate,phase(left,x)-p0,k)
        tail_right=polynomial_tangent_tail(right,right_rate,phase(right,x)-p0,k)
        model=finite.real.mid()
        error=finite.real.rad()+tail_left+tail_right
        if not model>error:
            raise ArithmeticError('positive moment or relative error unresolved')
        relative=(error/model).upper()
        models.append(scale*model)
        errors.append(relative)
        records.append({'order':k,'normalized_model':endpoints(model),
                        'quadrature_radius_upper':str(finite.real.rad().upper().fmpq()),
                        'left_tail_upper':str(tail_left.upper().fmpq()),
                        'right_tail_upper':str(tail_right.upper().fmpq()),
                        'relative_error_upper':str(relative.fmpq())})
    return models,errors,{'x':endpoints(x),'center':endpoints(center),
                          'left':endpoints(left),'right':endpoints(right),
                          'log_scale':endpoints((4*arb.pi()**2).log()+p0),
                          'left_rate':endpoints(left_rate),'right_rate':endpoints(right_rate),
                          'moments':records}


def certify_point(x,cutoff=1,spread=16):
    x=Fraction(x)
    if x<257:
        raise ValueError('curvature center must be at least 257')
    models,errors,evidence=[],[],[]
    for y in (x-1,x,x+1):
        model,sigma,record=first_summand_models(str(y),spread)
        remainder=uniform_bound(y,cutoff,max_order=2)
        eta=[arb(v['relative_error_upper']) for v in remainder['moments']]
        total=[(s+e*(1+s)).upper() for s,e in zip(sigma,eta)]
        models.append(model)
        errors.append(total)
        record.update(omitted_theta=remainder,combined_errors=[str(v.fmpq()) for v in total])
        evidence.append(record)
    result=propagate_moment_errors(str(x),models,errors)
    return {'x':str(x),'status':'certified_negative_curvature_at_point' if result['status']=='negative_under_supplied_error_hypotheses' else 'unresolved',
            'transfer':result,'moments':evidence}


def run():
    ctx.prec=512
    return {'schema_version':1,'status':'pointwise_effective_localized_saddle_not_unbounded_curvature_proof',
            'working_bits':512,'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
              for name in ('localized_saddle.py','effective_theta_remainder.py','curvature_error.py','laboratory.py','coefficients.py')},
            'points':[certify_point(x,u) for x,u in ((257,1),(4097,2),(65537,3))],
            'trust_boundary':'FLINT quadrature, global phase concavity, tangent tail proof and explicit theta remainder; not a Lean certificate.',
            'remaining':'A uniform-in-parameter saddle approximation or localized-integral estimate strong enough for every x in an unbounded domain.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    for row in result['points']:
        print(row['x'],row['status'],row['transfer']['curvature_enclosure'])


if __name__=='__main__':
    main()
