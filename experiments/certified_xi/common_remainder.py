"""Uniform Cauchy derivative bounds for a common, anchor-frozen Xi remainder.

The reference integral is frozen at one anchor, not the moving degree-16
model. It is used at all three neighboring parameters with the same phase.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from flint import arb, acb, ctx
from laboratory import endpoints, interval
from high_order_saddle import growing_bound, stirling_row
from decaying_theta import saddle_theta_bound
from curvature_error import curvature_transfer


def derivative_bound(threshold):
    X=Fraction(threshold)
    if X<10**6:
        raise ValueError('threshold>=1000000 required')
    with ctx.workprec(512):
        x=arb(str(X))
        bound=growing_bound(X)
        R=interval(bound['constants']['phase_remainder_upper']).upper()
        tau=interval(bound['constants']['gaussian_tail_exponent']).lower()
        d=interval(bound['constants']['tail_decay_fraction']).lower()
        C=interval(bound['constants']['standardized_third_derivative_upper']).upper()
        u=(2*x/arb.pi()).lambertw()/2
        L=(32*u).sqrt()
        h=L/(x*(1+2*u)).sqrt()
        tilt=arb(11)/2/(2*arb.pi()).sqrt()*(-u).exp()
        amplitude=3/(2*arb.pi())*(-2*u*(-h).exp()).exp()
        mass=2*(-tilt-arb('0.5')-C/6-R).exp()*(1-amplitude)
        eta=arb('0.25')
        decay=d-eta/L**2
        if not decay>0 or not mass>0:
            raise ArithmeticError('complex-tilted tail or model mass unresolved')
        tail=2*(-tau*32*u+eta).exp()/(mass*decay*L)
        central=eta.exp()*R.expm1()
        saddle=central+tail
        theta=saddle_theta_bound(X)
        high_theta=arb(theta['saddle_region_relative_upper'])
        global_theta=arb(theta['global_relative_upper'])
        # |exp(-2(z-a)c)Q_a(z)| >= exp(-eta) cos(eta) Q_a(a).
        # cos(1/4) >= 1-(1/4)^2/2 = 31/32.
        lower=(-eta).exp()*arb(31)/32
        theta_error=high_theta*(eta.exp()+saddle)+global_theta*tail
        sigma=(saddle+theta_error)/lower
        if not 0<=sigma<1:
            raise ArithmeticError('analytic logarithmic remainder unresolved')
        M=-(-sigma).log1p()
        radius=x.sqrt()/32
        clearance=radius-1
        if not clearance>0:
            raise ArithmeticError('neighboring-parameter Cauchy clearance unresolved')
        derivatives=[(math.factorial(j)*M/clearance**j).upper() for j in range(5)]
        return {'threshold':str(X),'status':'uniform_common_anchored_remainder_derivative_bounds',
                'scope':'For every anchor a>=threshold, bounds on R_a^(j)(y) for every real |y-a|<=1, where R_a=log(I/Q_a) and Q_a is frozen at a.',
                'relative_complex_error_upper':str(sigma.upper().fmpq()),
                'log_remainder_upper':str(M.upper().fmpq()),
                'disk_radius_lower':str(radius.lower().fmpq()),
                'derivatives':[{'order':j,'absolute_upper':str(v.fmpq())} for j,v in enumerate(derivatives)],
                'saddle_bound':bound,'theta_bound':theta}



def scaled_derivative_bound(threshold,anchor):
    """Power-law envelope from one threshold, uniform over larger anchors."""
    X,a=Fraction(threshold),Fraction(anchor)
    if a<X:
        raise ValueError('anchor must be at least threshold')
    with ctx.workprec(512):
        base=derivative_bound(X)
        tau=interval(base['saddle_bound']['constants']['gaussian_tail_exponent'])
        if not tau>=arb(7)/16 or not tau<=arb('0.5'):
            raise ArithmeticError('seventh-power decay condition unresolved')
        x,z=arb(str(X)),arb(str(a))
        u0=(2*x/arb.pi()).lambertw()/2
        u=(2*z/arb.pi()).lambertw()/2
        factor=(u/u0)**16*(x/z)**7
        rows=[]
        for row in base['derivatives']:
            j=row['order']
            value=arb(row['absolute_upper'])*factor*(x/z)**(arb(j)/2)
            rows.append({'order':j,'absolute_upper':str(value.upper().fmpq())})
        return {'threshold':str(X),'anchor':str(a),'derivatives':rows,
                'scope':'All real |y-anchor|<=1; same inequality holds as a function of every anchor>=threshold.',
                'formula':'E_j(X)*(u(a)/u(X))^16*(X/a)^(7+j/2)'}


def anchored_moments(anchor,offset):
    """Centered derivatives of one frozen reference integral at a+offset."""
    a,b=arb(anchor),arb(offset)
    if not a.is_finite() or not a>=10**6 or not b.is_finite() or not abs(b)<=1:
        raise ValueError('finite anchor>=1000000 and |offset|<=1 required')
    u=(2*a/arb.pi()).lambertw()/2
    c=u.log()
    A=2*a*(1+2*u)-arb(9)*u/2
    L=(32*u).sqrt()
    coefficients=[arb(0),(1+arb(9)*u/2)/A.sqrt()]
    for j in range(2,17):
        touchard=sum((arb(v)*(2*u)**k for k,v in enumerate(stirling_row(j))),arb(0))
        coefficients.append((arb(9)*u/2-a/u*touchard)/(math.factorial(j)*A**(arb(j)/2)))
    result=[]
    for k in range(3):
        def integrand(s,_analytic):
            poly=acb(0)
            for coefficient in reversed(coefficients):
                poly=poly*s+coefficient
            centered=2*s/A.sqrt()
            amplitude=1-3/(2*arb.pi())*(-2*(c+s/A.sqrt()).exp()).exp()
            return (poly+b*centered).exp()*amplitude*centered**k
        value=acb.integral(integrand,-L,L,rel_tol=arb(2)**-220,
                           abs_tol=arb(2)**-240,eval_limit=300000,depth_limit=50)
        if not value.is_finite() or not value.imag.contains(0):
            raise ArithmeticError('anchored quadrature unresolved')
        result.append(value.real)
    if not result[0]>0:
        raise ArithmeticError('positive anchored zeroth moment unresolved')
    return result


def certify_anchor(anchor):
    a=Fraction(anchor)
    bound=derivative_bound(a)
    x=arb(str(a))
    models=[anchored_moments(str(a),offset) for offset in (-1,0,1)]
    mean=[m[1]/m[0] for m in models]
    variance=[m[2]/m[0]-(m[1]/m[0])**2 for m in models]
    q=2*x*(2*x-1)/((2*x+2)*(2*x+1))*models[0][0]*models[2][0]/models[1][0]**2
    L=1/x+2/(2*x-1)-2/(2*x+2)-2/(2*x+1)+mean[0]+mean[2]-2*mean[1]
    M=-1/x**2-4/(2*x-1)**2+4/(2*x+2)**2+4/(2*x+1)**2+variance[0]+variance[2]-2*variance[1]
    e2,e3,e4=[arb(row['absolute_upper']) for row in bound['derivatives'][2:]]
    result=curvature_transfer(x,q,L,M,((abs(q)*e2.expm1()).upper(),e3,e4))
    return {'anchor':str(a),'status':'certified_negative_curvature_at_anchor' if
            result['status']=='negative_under_supplied_error_hypotheses' else 'unresolved',
            'transfer':result,'common_remainder':bound,
            'model_moments':[[endpoints(v) for v in row] for row in models]}


def run():
    with ctx.workprec(512):
        return {'schema_version':1,'status':'uniform_common_remainder_derivatives_pointwise_curvature_only',
                'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                    for name in ('common_remainder.py','high_order_saddle.py','decaying_theta.py',
                                 'curvature_error.py','laboratory.py','coefficients.py')},
                'uniform_bounds':[derivative_bound(x) for x in (10**6,10**8,10**12)],
                'anchors':[certify_anchor(x) for x in (10**6+1,10**8+1)],
                'decay_envelopes':[scaled_derivative_bound(10**6,a) for a in (10**8,10**12,10**40)],
                'trust_boundary':'Cauchy integral formula, complex disk domination and FLINT balls; not Lean formalized.',
                'remaining':'Uniform sign of the anchored reference curvature and the interior all-rank budget.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    for row in result['uniform_bounds']:
        print(row['threshold'],[str(arb(v['absolute_upper'])) for v in row['derivatives'][2:]])
    for row in result['anchors']:
        print(row['anchor'],row['status'],row['transfer']['curvature_enclosure'])


if __name__=='__main__':
    main()
