"""Growing-window high-order saddle bounds; curvature signs remain pointwise."""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from flint import arb, acb, ctx
from laboratory import endpoints
from localized_saddle import phase
from effective_theta_remainder import uniform_bound
from curvature_error import propagate_moment_errors


def stirling_row(n):
    if type(n) is not int or not 0 <= n <= 25:
        raise ValueError('integer order 0..25 required')
    row = [1]
    for k in range(1,n+1):
        row = [0]+[(row[j-1] if j-1<len(row) else 0)+
                   (j*row[j] if j<len(row) else 0) for j in range(1,k+1)]
    return row


def growing_bound(threshold, degree=16, window_factor=32):
    X, K = Fraction(threshold), Fraction(window_factor)
    if X < 65536 or K <= 0 or type(degree) is not int or not 2<=degree<=24:
        raise ValueError('X>=65536, positive window factor, degree 2..24 required')
    with ctx.workprec(512):
        x, Kb = arb(str(X)), arb(str(K))
        u = (2*x/arb.pi()).lambertw()/2
        L = (Kb*u).sqrt()
        h = L/(x*(1+2*u)).sqrt()
        z = 1/((x*(1+2*u)).sqrt()*u.log())
        if not u>=arb('1.5') or not L>=2 or not L*z<1:
            raise ArithmeticError('growing-window domain unresolved')
        D = 2*u*h*h.exp()
        tilt = arb(11)/2/(2*arb.pi()).sqrt()*(-u).exp()
        cubic = 3*(3*h+D).exp()*((2+1/u)/arb.pi()).sqrt()*(-u).exp()
        cubic += arb(9)/4*h.exp()/x**arb('1.5')
        ratio = tilt/L
        B = cubic*L
        tau = arb('0.5')-ratio-B/6
        decay_fraction = 1-ratio-B/2
        if not tau>0 or not decay_fraction>0:
            raise ArithmeticError('uniform Gaussian tail decay unresolved')
        n = degree+1
        bell = sum(stirling_row(n))
        R = bell*(n*h+D).exp()*(2+1/u)**(arb(n)/2)/arb.pi()**(arb(n)/2-1)
        R *= (Kb*u)**(arb(n)/2)*(-(n-2)*u).exp()/math.factorial(n)
        R += arb(9)/4*h.exp()*(Kb/arb.pi())**(arb(n)/2)*(-n*u).exp()/math.factorial(n)
        amplitude = 3/(2*arb.pi())*(-2*u*(-h).exp()).exp()
        # On |s|<=1 the Taylor model is >= -tilt-1/2-cubic/6-R.
        common_lower = 2*(-tilt-arb('0.5')-cubic/6-R).exp()*(1-amplitude)
        if not common_lower>0:
            raise ArithmeticError('positive model mass unresolved')
        rows=[]
        for k in range(3):
            polynomial=sum((arb(math.factorial(k)//math.factorial(k-j))*
                            (1+L*z)**(k-j)*z**j/(decay_fraction*L)**(j+1)
                            for j in range(k+1)),arb(0))
            tail=2*(-tau*Kb*u).exp()*polynomial/(common_lower*(1-z)**k)
            error=R.exp()-1+tail
            rows.append({'order':k,'relative_error_upper':str(error.upper().fmpq()),
                         'tail_relative_upper':str(tail.upper().fmpq())})
        return {'threshold':str(X),'degree':degree,'window_factor':str(K),
                'scope':'Every real x>=threshold, with L(x)=sqrt(window_factor*W(2x/pi)/2); model retains exact amplitude.',
                'constants':{name:endpoints(v) for name,v in
                             (('u_lower',u),('radius_at_threshold',L),('phase_remainder_upper',R),
                              ('gaussian_tail_exponent',tau),('tail_decay_fraction',decay_fraction),
                              ('standardized_third_derivative_upper',cubic))},'moments':rows}


def model_moments(x, degree=16, window_factor=32):
    """Integrate the specified model, returning its own quadrature error."""
    x=arb(x)
    if not x.is_finite() or not x>=65536 or type(degree) is not int or not 2<=degree<=24:
        raise ValueError('finite x>=65536 and integer degree 2..24 required')
    K=arb(window_factor)
    if not K.is_finite() or not K>0:
        raise ValueError('positive finite window factor required')
    u=(2*x/arb.pi()).lambertw()/2
    c=u.log()
    A=2*x*(1+2*u)-arb(9)*u/2
    L=(K*u).sqrt()
    if not c-L/A.sqrt()>0:
        raise ArithmeticError('positive model moment weights unresolved')
    coefficients=[arb(0),(1+arb(9)*u/2)/A.sqrt()]
    for j in range(2,degree+1):
        touchard=sum((arb(v)*(2*u)**k for k,v in enumerate(stirling_row(j))),arb(0))
        derivative=arb(9)*u/2-x/u*touchard
        coefficients.append(derivative/(math.factorial(j)*A**(arb(j)/2)))
    scale=4*arb.pi()**2*phase(c,x).exp()/A.sqrt()
    models, errors=[],[]
    for k in range(3):
        def integrand(s,_analytic):
            polynomial=acb(0)
            for a in reversed(coefficients):
                polynomial=polynomial*s+a
            t=c+s/A.sqrt()
            amplitude=1-3/(2*arb.pi())*(-2*t.exp()).exp()
            return polynomial.exp()*amplitude*(2*t)**k
        value=acb.integral(integrand,-L,L,rel_tol=arb(2)**-220,
                           abs_tol=arb(2)**-240,eval_limit=300000,depth_limit=50)
        if not value.is_finite() or not value.imag.contains(0) or not value.real>0:
            raise ArithmeticError('model quadrature unresolved')
        mid=value.real.mid()
        models.append(scale*mid)
        errors.append((value.real.rad()/mid).upper())
    return models,errors


def certify_point(x, degree=16, window_factor=32):
    x=Fraction(x)
    if x<65537:
        raise ValueError('curvature center>=65537 required')
    models, errors, evidence=[],[],[]
    for y in (x-1,x,x+1):
        bound=growing_bound(y,degree,window_factor)
        theta=uniform_bound(y,3,max_order=2)
        model,quad=model_moments(str(y),degree,window_factor)
        total=[]
        for k in range(3):
            sigma=arb(bound['moments'][k]['relative_error_upper'])
            eta=arb(theta['moments'][k]['relative_error_upper'])
            total.append(((1+sigma)*(1+eta)*(1+quad[k])-1).upper())
        models.append(model)
        errors.append(total)
        evidence.append({'x':str(y),'saddle':bound,'theta':theta,
                         'quadrature_errors':[str(v.fmpq()) for v in quad],
                         'combined_errors':[str(v.fmpq()) for v in total]})
    try:
        result=propagate_moment_errors(str(x),models,errors)
    except (ArithmeticError,ValueError) as exc:
        result={'status':'unresolved','reason':str(exc)}
    return {'x':str(x),'status':'certified_negative_curvature_at_point' if
            result['status']=='negative_under_supplied_error_hypotheses' else 'unresolved',
            'transfer':result,'evidence':evidence}


def run():
    with ctx.workprec(512):
        return {'schema_version':1,'status':'uniform_high_order_moment_bounds_pointwise_curvature_only',
                'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                    for name in ('high_order_saddle.py','localized_saddle.py','effective_theta_remainder.py',
                                 'curvature_error.py','laboratory.py','coefficients.py')},
                'bounds':[growing_bound(x) for x in (10**6,10**8,10**12)],
                'points':[certify_point(x) for x in (10**6+1,10**8+1)],
                'remaining':'Uniform sign control for the model curvature and a uniform interior cumulative rank budget.',
                'trust_boundary':'Explicit analytic inequalities and FLINT balls; not Lean formalized.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    for row in result['bounds']:
        print(row['threshold'],arb(row['moments'][2]['relative_error_upper']))
    for row in result['points']:
        print(row['x'],row['status'],row['transfer'])


if __name__=='__main__':
    main()
