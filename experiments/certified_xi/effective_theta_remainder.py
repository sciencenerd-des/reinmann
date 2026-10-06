"""Uniform relative remainder for replacing Phi by its first summand.

Bounds logarithmic moment orders 0..4 for every real x>=X. This is not a
saddle approximation error or a certificate of the curvature sign.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from flint import arb,ctx
from laboratory import endpoints


def uniform_bound(threshold, cutoff=1, gap='1/4', width='1/8', max_order=4):
    X,U,g,h=map(Fraction,(threshold,cutoff,gap,width))
    if X<0 or U<1 or g<=0 or h<=0 or type(max_order) is not int or not 0<=max_order<=4:
        raise ValueError('require X>=0, U>=1, positive gap/width and order 0..4')
    ctx.prec=512
    x,u,v,length=map(lambda z:arb(str(z)),(X,U,U+g,h))
    pi=arb.pi()
    e=(2*u).exp()
    series_ratio=16*(-5*pi*e).exp()
    denominator=1-3/(2*pi*e)
    if not series_ratio<1 or not denominator>0:
        raise ArithmeticError('positive kernel denominator unresolved')
    rho=16*(-3*pi*e).exp()/((1-series_ratio)*denominator)
    # Phi on [0,U] is at most this bound: discard each negative summand.
    q0=16*(-3*pi).exp()
    b=4*pi*pi*(arb(9)*u/2-pi).exp()/(1-q0)
    # Positive first-summand mass on [V,V+h], including a logarithmic weight.
    kernel_lower=4*pi*pi*(arb(9)*v/2-pi*(2*(v+length)).exp()).exp()
    kernel_lower*=1-3/(2*pi*(2*v).exp())
    base=length*v**(2*x)*kernel_lower
    if not base>0:
        raise ArithmeticError('positive comparison mass unresolved')
    rows=[]
    a=2*x+1
    for k in range(max_order+1):
        low=2**k*math.factorial(k)/a**(k+1)
        low+=(u**(2*x+1)-1)/a*(2*u.log())**k
        beta=b*low/(base*(2*v.log())**k)
        if not beta<1:
            raise ArithmeticError('threshold insufficient for positive signed moment denominator')
        relative=rho+(1+rho)*beta/(1-beta)
        rows.append({'order':k,'low_region_mass_ratio':endpoints(beta),
                     'relative_error_upper':str(relative.upper().fmpq())})
    return {'threshold':str(X),'cutoff':str(U),'comparison_start':str(U+g),
            'comparison_width':str(h),'pointwise_high_region_ratio':endpoints(rho),
            'moments':rows,'scope':'Every real x>=threshold, moment orders listed; relative to signed first-summand moments, proved positive here.'}


def run():
    return {'schema_version':1,'status':'uniform_first_summand_remainder_not_curvature_or_saddle_certificate',
            'working_bits':512,
            'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                             for name in ('effective_theta_remainder.py','laboratory.py','coefficients.py')},
            'bounds':[uniform_bound(x,u) for x,u in ((256,1),(4096,2),(65536,3))],
            'trust_boundary':'FLINT evaluation of explicit analytic inequalities; not a Lean theorem.',
            'remaining':'An effective saddle remainder for the first summand and error propagation through the cancelling curvature expression.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    for row in result['bounds']:
        bound=max(Fraction(v['relative_error_upper']) for v in row['moments'])
        print('x >=',row['threshold'],'max relative error <=',arb(str(bound)))


if __name__=='__main__':
    main()
