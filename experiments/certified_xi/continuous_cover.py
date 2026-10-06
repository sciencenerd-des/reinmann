"""Certified finite interval cover for scaled-deficit log-concavity.

Monotone endpoint bounds on each side of u=1 enclose every real parameter
in each cell. A failed or exhausted cover is explicitly incomplete.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from flint import acb, arb, ctx
from continuous_theta import tail_bounds
from laboratory import endpoints, sign


def finite_parts(x, bits=256, max_order=2):
    if max_order not in range(4):
        raise ValueError("max_order must be 0..3")
    ctx.prec=bits
    x=arb(str(x))
    if not x>=0:
        raise ValueError('nonnegative moment parameter required')
    pi=arb.pi()
    constants=[(4*pi**2*j**4,6*pi*j*j,pi*j*j) for j in range(1,13)]
    parts=[]
    for k in range(max_order+1):
        def integrand(t,_analytic):
            u=t.exp()
            e2,e9,e5=(2*u).exp(),(arb(9)*u/2).exp(),(arb(5)*u/2).exp()
            phi=sum(((a*e9-b*e5)*(-c*e2).exp() for a,b,c in constants),acb(0))
            return ((2*x+1)*t).exp()*(2*t)**k*phi
        pair=[]
        for lo,hi in ((-64,0),(0,arb(4).log())):
            val=acb.integral(integrand,lo,hi,rel_tol=arb(2)**-84,
                             abs_tol=arb(2)**-96,eval_limit=300000,depth_limit=50)
            if not val.is_finite() or not val.imag.contains(0):
                raise ArithmeticError('endpoint integration unresolved')
            pair.append(val.real)
        parts.append(pair)
    return parts


def moment_box(lo,hi,cache,max_order=2):
    if max_order not in range(4):
        raise ValueError("max_order must be 0..3")
    if lo<0 or hi<lo:
        raise ValueError('invalid nonnegative moment interval')
    for x in (lo,hi):
        if x not in cache or len(cache[x])<=max_order:
            cache[x]=finite_parts(x,max_order=max_order)
    low,high=cache[lo],cache[hi]
    x=arb(str(lo)).union(arb(str(hi)))
    results=[]
    for k in range(max_order+1):
        # Left piece is decreasing for even k, increasing for odd k.
        left_lo=(low if k%2 else high)[k][0].lower()
        left_hi=(high if k%2 else low)[k][0].upper()
        # Every right piece is nonnegative and increasing in x.
        lower=left_lo+low[k][1].lower()
        upper=left_hi+high[k][1].upper()
        enclosed=lower.union(upper)
        tails=tail_bounds(x,k,parameter_bounds=(lo,hi))
        results.append(enclosed+arb(0,sum(tails,arb(0)).upper()))
    if not results[0]>0:
        raise ArithmeticError('positive moment denominator unresolved')
    return results


def curvature_box(lo,hi,cache):
    if not 1<=lo<=hi<=8:
        raise ValueError('cover domain must lie in [1,8]')
    triples=[moment_box(lo+j,hi+j,cache) for j in (-1,0,1)]
    i=[v[0] for v in triples]
    kp=[v[1]/v[0] for v in triples]
    kpp=[v[2]/v[0]-(v[1]/v[0])**2 for v in triples]
    t=arb(str(lo)).union(arb(str(hi)))
    q=(2*t)*(2*t-1)/((2*t+2)*(2*t+1))*i[0]*i[2]/i[1]**2
    if not q>0 or not q<1:
        return {'lo':str(lo),'hi':str(hi),'status':'unresolved','reason':'q denominator domain'}
    lp=1/t+2/(2*t-1)-2/(2*t+2)-2/(2*t+1)+kp[0]+kp[2]-2*kp[1]
    lpp=-1/t**2-4/(2*t-1)**2+4/(2*t+2)**2+4/(2*t+1)**2+kpp[0]+kpp[2]-2*kpp[1]
    d=1-q
    if not d**2>0:
        return {'lo':str(lo),'hi':str(hi),'status':'unresolved','reason':'squared deficit denominator'}
    g=q*d*lpp+q*lp**2+d**2/(t+1)**2
    return {'lo':str(lo),'hi':str(hi),'status':sign(g),
            'G':endpoints(g),'log_epsilon_second':endpoints(-g/d**2)}


def verify_partition(cells,lo,hi):
    position=lo
    for cell in sorted(cells,key=lambda v:Fraction(v['lo'])):
        if Fraction(cell['lo'])!=position or Fraction(cell['hi'])<=position:
            raise ArithmeticError('gap, overlap or reversed cover cell')
        position=Fraction(cell['hi'])
    if position!=hi:
        raise ArithmeticError('incomplete cover partition')


def run(lo='1',hi='2',max_depth=16,max_cells=10000):
    lo,hi=Fraction(lo),Fraction(hi)
    if not 1<=lo<hi<=8 or not 0<=max_depth<=20 or not 1<=max_cells<=20000:
        raise ValueError('invalid cover domain or budget')
    ctx.prec=256
    pending=[(lo,hi,0)]
    cells=[]
    cache={}
    while pending:
        a,b,depth=pending.pop()
        row=curvature_box(a,b,cache)
        if row['status']=='unresolved' and depth<max_depth and len(cells)+len(pending)+2<=max_cells:
            mid=(a+b)/2
            pending.extend(((mid,b,depth+1),(a,mid,depth+1)))
        else:
            cells.append(row)
    cells.sort(key=lambda v:Fraction(v['lo']))
    verify_partition(cells,lo,hi)
    complete=all(v['status']=='positive' for v in cells)
    return {'schema_version':1,'status':'certified_finite_interval' if complete else 'incomplete_cover',
            'domain':[str(lo),str(hi)],'bits':256,'max_depth':max_depth,'max_cells':max_cells,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'tail_source_sha256':hashlib.sha256(Path(__file__).with_name('continuous_theta.py').read_bytes()).hexdigest(),
            'endpoint_parameters':len(cache),'cells':cells,
            'trust_boundary':'FLINT ball arithmetic, theta identity, tail estimates and monotone split; not a Lean certificate',
            'scope':'Every real x in the declared domain if status is certified_finite_interval; no unbounded tail or higher-rank assertion.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lo',default='1')
    parser.add_argument('--hi',default='2')
    parser.add_argument('--max-depth',type=int,default=16)
    parser.add_argument('--max-cells',type=int,default=10000)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run(args.lo,args.hi,args.max_depth,args.max_cells)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],len(result['cells']),'cells',result['endpoint_parameters'],'endpoint parameters')

if __name__=='__main__':
    main()
