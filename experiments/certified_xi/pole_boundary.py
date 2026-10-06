"""Analytic-numerical all-rank SHIFT-ONE certificate from two isolated poles.

Uses coefficient enclosures, positive-coefficient tail bounds, a winding count,
Rouche, Cauchy, and decreasing geometric majorants. Not a Lean certificate.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
from flint import arb,acb,ctx
from laboratory import load_coefficients,endpoints,interval
from boundary_budget import boundary_ratios,boundary_prefixes
from dual_rank_budget import dual_grid


def evaluate(coefficients,z):
    value=acb(0)
    for c in reversed(coefficients):
        value=value*z+c
    return value


def translate(coefficients,center):
    result=list(coefficients)
    for i in range(len(result)-2,-1,-1):
        for j in range(i,len(result)-1):
            result[j]+=center*result[j+1]
    return result


def certify_circle(coefficients,radius,tail,expected=2,segments=256):
    if radius<=0 or not tail>=0 or type(segments) is not int or segments<4:
        raise ValueError('invalid circle or subdivision budget')
    radius=arb(radius)
    if not 0<=expected<len(coefficients):
        raise ValueError('invalid expected polynomial root count')
    lower=None
    winding=arb(0)
    first=evaluate(coefficients,acb(radius))
    previous=first
    records=[]
    arc_radius=radius*arb.pi()/segments
    for j in range(segments):
        center=radius*(acb(0,1)*2*arb.pi()*(arb(j)+arb('0.5'))/segments).exp()
        shifted=translate(coefficients,center)
        variation=arb(0)
        for c in reversed(shifted[1:]):
            variation=(variation+abs(c))*arc_radius
        bound=abs(shifted[0]).lower()-variation.upper()
        if not bound>tail:
            raise ArithmeticError('arc disk may contain zero or violate Rouche bound')
        lower=bound if lower is None else lower.min(bound)
        endpoint=first if j==segments-1 else evaluate(coefficients,
            radius*(acb(0,1)*2*arb.pi()*(j+1)/segments).exp())
        increment=(endpoint/previous).arg()
        if not increment.is_finite():
            raise ArithmeticError('argument increment unresolved')
        winding+=increment
        previous=endpoint
        records.append({'arc':j,'polynomial_modulus_lower':str(bound.lower().fmpq()),
                        'argument_increment':endpoints(increment)})
    count=winding/(2*arb.pi())
    if not count.contains(expected) or not expected-arb('0.25')<count<expected+arb('0.25'):
        raise ArithmeticError('winding number does not certify requested count')
    return lower,{'radius':str(radius.fmpq()),'segments':segments,'zero_count':expected,
                  'winding_enclosure':endpoints(count),'polynomial_modulus_lower':str(lower.lower().fmpq()),
                  'arcs':records}


def isolate_real_zero(coefficients,tail,lo,hi,width=F(1,10**18)):
    lo,hi=F(lo),F(hi)
    if not lo<hi or width<=0:
        raise ValueError('invalid root bracket')
    def value(x):
        z=evaluate(coefficients,acb(arb(str(x))))
        if not z.imag.contains(0):
            raise ArithmeticError('real polynomial evaluation required')
        return z.real+arb(0,tail.upper())
    left,right=value(lo),value(hi)
    direction=1 if left>0 else -1
    if not direction*left>0 or not direction*right<0:
        raise ArithmeticError('strict real sign change unresolved')
    for _ in range(256):
        if hi-lo<=width:
            return arb(str(lo)).union(arb(str(hi))),{
                'lo':str(lo),'hi':str(hi),'left_value':endpoints(value(lo)),
                'right_value':endpoints(value(hi))}
        mid=(lo+hi)/2
        v=direction*value(mid)
        if v>0:
            lo=mid
        elif v<0:
            hi=mid
        else:
            raise ArithmeticError('root refinement reached coefficient tail uncertainty')
    raise ArithmeticError('root refinement budget exhausted')


def tail_criteria(n,A,B,alpha,beta,M,radius):
    if type(n) is not int or n<1 or not all(v>0 for v in (A,B,alpha,beta,M,radius)):
        raise ValueError('positive pole constants and index required')
    if not alpha>beta or not beta*radius>1:
        raise ArithmeticError('two-pole ordering or contour separation unresolved')
    T=(alpha-beta)**2/(alpha*beta)
    s=beta/alpha
    loss=B/A*s**n+M/A*(1/(radius*alpha))**n
    error=M/(B*T)*(1/(beta*radius))**n*(2+alpha*radius+1/(alpha*radius))
    error+=M/(A*T)*(1/(alpha*radius))**n*(2+beta*radius+1/(beta*radius))
    error+=2*M**2/(A*B*T)*(1/(alpha*beta*radius**2))**n
    upper=8*(n+1)*B/A*T*s**n
    ratio=arb(n+2)/(n+1)*s
    passed=loss<arb('0.5') and error<1 and upper<1 and ratio<1
    return passed,{'tail_start':n,'positivity_loss':endpoints(loss),
                   'determinant_error_over_two_pole_gap':endpoints(error),
                   'normalized_boundary_ratio_upper':str(upper.upper().fmpq()),
                   'linear_geometric_successive_ratio':endpoints(ratio)}


def correction_tail_criteria(k,A,B,alpha,beta,M,radius):
    if type(k) is not int or k<2:
        raise ValueError('correction tail index must be at least two')
    _,record=tail_criteria(k-1,A,B,alpha,beta,M,radius)
    # Reconstruct outward boxes; loss/error formulas are geometric sums.
    loss=interval(record['positivity_loss'])
    error=interval(record['determinant_error_over_two_pole_gap'])
    ratio=(beta/alpha).max(1/(radius*alpha)).max(1/(radius*beta)).max(1/(alpha*beta*radius**2))
    scaled=(8*error+16*loss)*(k+1)**2
    successive=ratio*(arb(k+2)/(k+1))**2
    passed=loss<arb('0.5') and error<arb('0.5') and scaled<1 and successive<1
    return passed,{'correction_tail_start':k,'geometric_ratio':endpoints(ratio),
                   'scaled_curvature_error':endpoints(scaled),
                   'weighted_successive_ratio':endpoints(successive)}


def run(path):
    ctx.prec=768
    mu,_=load_coefficients(path)
    if len(mu)!=121:
        raise ValueError('this certificate requires coefficients 0..120')
    coefficients=[acb((-1)**n*mu[n]/mu[0]) for n in range(len(mu))]
    coefficients[0]=acb(1)
    radius,outer=arb(600),arb(1200)
    s=arb('0.5')+outer.sqrt()
    positive_majorant=s*(s-1)/2*arb.pi()**(-s/2)*(s/2).gamma()*s.zeta()/mu[0]
    q=radius/outer
    omitted_start=len(coefficients)
    if not 0<q<arb(omitted_start)/(omitted_start+1):
        raise ArithmeticError('coefficient derivative tail monotonicity unresolved')
    tail=positive_majorant*q**omitted_start
    derivative_tail=omitted_start*tail/radius
    lower,circle=certify_circle(coefficients,radius,tail)
    roots=[]
    amplitudes=[]
    root_records=[]
    derivative_coefficients=[(j+1)*coefficients[j+1] for j in range(len(coefficients)-1)]
    for lo,hi in ((199,201),(441,443)):
        root,record=isolate_real_zero(coefficients,tail,lo,hi)
        derivative=evaluate(derivative_coefficients,acb(root)).real+arb(0,derivative_tail.upper())
        if derivative.contains(0):
            raise ArithmeticError('simple pole derivative unresolved')
        amplitude=-1/(root*derivative)
        roots.append(root)
        amplitudes.append(amplitude)
        record.update(derivative=endpoints(derivative),amplitude=endpoints(amplitude))
        root_records.append(record)
    if not 0<roots[0]<roots[1]<radius or not amplitudes[0]>0 or not amplitudes[1]<0:
        raise ArithmeticError('pole order or residue signs unresolved')
    A,B=amplitudes[0],-amplitudes[1]
    alpha,beta=1/roots[0],1/roots[1]
    M=1/(lower-tail)+A/(radius/roots[0]-1)+B/(radius/roots[1]-1)
    tail_record=None
    for n in range(2,120):
        passed,record=tail_criteria(n,A,B,alpha,beta,M,radius)
        if passed:
            tail_record=record
            break
    if tail_record is None:
        raise ArithmeticError('no overlap between provable tail and finite coefficient range')
    ctx.prec=2048
    _,finite=boundary_ratios(mu)
    bridge=finite[:tail_record['tail_start']-1]
    if len(bridge)!=tail_record['tail_start']-1 or any(
        row['rank_positive_status']!='positive' or row['boundary_status']!='positive' for row in bridge):
        raise ArithmeticError('finite bridge incomplete or sign unresolved')
    correction_tail=None
    for k in range(3,118):
        passed,record=correction_tail_criteria(k,A,B,alpha,beta,M,radius)
        if passed:
            correction_tail=record
            break
    if correction_tail is None:
        raise ArithmeticError('no overlap for the correction curvature tail')
    grid=dual_grid(mu,max_rank=correction_tail['correction_tail_start']-1,max_shift=2)
    boundary,_=boundary_ratios(mu)
    correction_bridge=boundary_prefixes(boundary,grid)
    if len(correction_bridge)!=correction_tail['correction_tail_start']-1 or any(
        not interval(row['correction'])>0 for row in correction_bridge):
        raise ArithmeticError('finite correction bridge incomplete or not positive')
    return {'schema_version':1,'status':'analytic_numerical_all_ranks_shift_one_not_all_shifts',
            'coefficient_input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                             for name in ('pole_boundary.py','boundary_budget.py','normalized_recurrence.py',
                                          'laboratory.py','coefficients.py','dual_rank_budget.py','tail_and_rank_budget.py')},
            'contour_working_bits':768,'bridge_working_bits':2048,
            'positive_majorant_radius':1200,'positive_majorant':endpoints(positive_majorant),
            'function_tail':endpoints(tail),'derivative_tail':endpoints(derivative_tail),
            'circle':circle,'poles':root_records,'reciprocal_remainder_coefficient_constant':endpoints(M),
            'tail':tail_record,'finite_bridge':bridge,
            'correction_tail':correction_tail,'finite_correction_bridge':correction_bridge,
            'claim':'h_n>0 and 0<(n+1)(1-h_(n-1)h_(n+1)/h_n^2)<1 for every integer n>=1; C_r(1)>0 for every r>=1, so the boundary cumulative negative loss is zero.',
            'trust_boundary':'FLINT, Xi coefficient/theta identity, positive coefficients, winding number, Rouche, Cauchy and dual determinant algebra. Not Lean-checked.',
            'remaining':'No interior all-rank budget or RH theorem; other shifts remain uncontrolled uniformly.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run(args.coefficients)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'tail starts',result['tail']['tail_start'],'finite bridge',len(result['finite_bridge']))


if __name__=='__main__':
    main()
