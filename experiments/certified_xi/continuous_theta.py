"""Rigorous theta logarithmic moments and continuous scaled-deficit curvature.

Uses u=exp(t), making logarithmic moments entire integrands on a finite t
interval. Explicit left, right and omitted-series tails enclose the remainder.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from flint import acb, arb, ctx
from laboratory import endpoints, sign


def tail_bounds(x, k, terms=12, upper=4, left=64, parameter_bounds=None):
    # Explicit rational-domain endpoints avoid outward ball radii crossing x=0.
    if parameter_bounds is None:
        x_lo,x_hi=x.lower(),x.upper()
    else:
        lo,hi=map(Fraction,parameter_bounds)
        if lo<0 or hi<lo:
            raise ValueError('invalid parameter endpoints')
        x_lo,x_hi=arb(str(lo)),arb(str(hi))
    if not x_lo >= 0 or not 0 <= k <= 3 or terms < 1 or upper < 1 or left < 1:
        raise ValueError('require x>=0, k=0..3 and positive cutoffs')
    pi=arb.pi()
    h=(-arb(left)).exp()
    q0=16*(-3*pi).exp()
    j=terms+1
    qj=16*(-pi*(2*j+1)/2).exp()
    e=(2*arb(upper)).exp()
    qu=16*(-3*pi*e).exp()
    p=2*x_hi+k
    rate=2*pi*e-arb(9)/2-p/upper
    if not all(q<1 for q in (q0,qj,qu)) or not rate>0:
        raise ArithmeticError('tail denominator unresolved; increase cutoffs')
    # Phi(u) <= B for 0<=u<=h.
    b=4*pi**2*(arb(9)*h/2-pi).exp()/(1-q0)
    a=2*x_lo+1
    # Exact integral of exp(-a v) v^k from left to infinity.
    poly=sum((arb(math.factorial(k)//math.factorial(k-j))*left**(k-j)/a**(j+1)
              for j in range(k+1)),arb(0))
    small=b*2**k*(-a*left).exp()*poly
    # Omitted j>J terms on [h,U]; bound |log u| by max(left,log U).
    log_bound=arb(left).max(arb(upper).log())
    sumj=j**4*(-pi*j*j/2).exp()/(1-qj)
    middle=4*pi**2*arb(upper)**(2*x_hi+1)
    middle*=(arb(9)*upper/2-pi/2).exp()*sumj*(2*log_bound)**k
    # |log u|^k <= u^k on u>=U>=1.
    large=4*pi**2*2**k*arb(upper)**p*(arb(9)*upper/2-pi*e).exp()
    large/=(1-qu)*rate
    return small.upper(),middle.upper(),large.upper()


def log_moments(x, bits=256, accuracy=64, terms=12, upper=4, left=64, max_order=2):
    if max_order not in range(4):
        raise ValueError("max_order must be 0..3")
    ctx.prec=bits
    x=arb(x)
    if not x.is_finite() or not x>=0:
        raise ValueError('moment parameter must be finite and nonnegative')
    pi=arb.pi()
    constants=[(4*pi**2*j**4,6*pi*j*j,pi*j*j) for j in range(1,terms+1)]
    values=[]
    evidence=[]
    for k in range(max_order+1):
        def integrand(t,_analytic):
            u=t.exp()
            e2,e9,e5=(2*u).exp(),(arb(9)*u/2).exp(),(arb(5)*u/2).exp()
            phi=sum(((a*e9-b*e5)*(-c*e2).exp() for a,b,c in constants),acb(0))
            return ((2*x+1)*t).exp()*(2*t)**k*phi
        value=acb.integral(integrand,-left,arb(upper).log(),
                           rel_tol=arb(2)**(-accuracy-20),
                           abs_tol=arb(2)**(-accuracy-32),eval_limit=300000,depth_limit=50)
        if not value.is_finite() or not value.imag.contains(0):
            raise ArithmeticError('logarithmic-moment quadrature unresolved')
        tails=tail_bounds(x,k,terms,upper,left)
        result=value.real+arb(0,sum(tails,arb(0)).upper())
        # Absolute error test is also meaningful when the first moment is near zero.
        if not result.rad()<arb(2)**(-accuracy)*max(arb(1),abs(result).upper()):
            raise ArithmeticError('requested moment accuracy unresolved')
        values.append(result)
        evidence.append({'derivative_order':k,'enclosure':endpoints(result),
                         'tails':dict(zip(('small_u','omitted_terms','large_u'),
                                          (str(t.fmpq()) for t in tails)))})
    if not values[0]>0:
        raise ArithmeticError('positive normalizing integral unresolved')
    return values,evidence


def curvature(x, bits=256, accuracy=64, cache=None):
    """Pointwise rational x>=1. This does not certify intervals between points."""
    x=Fraction(x)
    if not 1<=x<=32:
        raise ValueError('curvature point must lie in [1,32]')
    ctx.prec=bits
    cache={} if cache is None else cache
    triples=[]
    for y in (x-1,x,x+1):
        key=(str(y),bits,accuracy)
        if key not in cache:
            cache[key]=log_moments(str(y),bits,accuracy)
        triples.append(cache[key][0])
    i0=[v[0] for v in triples]
    kp=[v[1]/v[0] for v in triples]
    kpp=[v[2]/v[0]-(v[1]/v[0])**2 for v in triples]
    t=arb(str(x))
    c=(2*t)*(2*t-1)/((2*t+2)*(2*t+1))
    q=c*i0[0]*i0[2]/i0[1]**2
    if not q>0 or not q<1:
        raise ArithmeticError('0<q<1 unresolved')
    lp=1/t+2/(2*t-1)-2/(2*t+2)-2/(2*t+1)+kp[0]+kp[2]-2*kp[1]
    lpp=-1/t**2-4/(2*t-1)**2+4/(2*t+2)**2+4/(2*t+1)**2+kpp[0]+kpp[2]-2*kpp[1]
    delta=1-q
    g=q*delta*lpp+q*lp**2+delta**2/(t+1)**2
    return {'x':str(x),'q':endpoints(q),'epsilon':endpoints((t+1)*delta),
            'ell_prime':endpoints(lp),'ell_second':endpoints(lpp),
            'curvature_numerator_G':endpoints(g),'G_status':sign(g),
            'log_epsilon_second':endpoints(-g/delta**2)}


def run(points,bits=256,accuracy=64):
    if not 128<=bits<=4096 or not 32<=accuracy<=min(256,bits-64):
        raise ValueError('invalid precision budget')
    points=[Fraction(p) for p in points]
    if not points or len(points)>128 or len(set(points))!=len(points):
        raise ValueError('provide 1..128 distinct rational points')
    cache={}
    rows=[curvature(x,bits,accuracy,cache) for x in points]
    return {'schema_version':1,'status':'certified_pointwise_curvature_not_continuum_or_tail',
            'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'bits':bits,'accuracy_bits':accuracy,'left_log_cutoff':64,'upper_u_cutoff':4,
            'theta_terms':12,'points':rows,
            'moments':[{'x':key[0],'records':value[1]} for key,value in cache.items()],
            'trust_boundary':'FLINT/Arb, theta identity and explicit tail inequalities; not Lean certificates',
            'remaining':'Uniform enclosures on intervals and an analytic tail for unbounded x. Positive pointwise samples do not prove concavity.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--points',nargs='+',default=['1','3/2','2','5/2','3','4','6'])
    parser.add_argument('--bits',type=int,default=256)
    parser.add_argument('--accuracy',type=int,default=64)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    try:
        result=run(args.points,args.bits,args.accuracy)
    except (ValueError,ArithmeticError) as exc:
        parser.error(str(exc))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print([(v['x'],v['G_status']) for v in result['points']])

if __name__=='__main__':
    main()
