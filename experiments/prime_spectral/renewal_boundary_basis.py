"""Certified normalized renewal profiles and an exact-trace Green basis.

Uses the established Stieltjes representation in Grzywny--Ryznar Prop. 3.2,
with B(xi)=log(1+xi^2)/2. Laplace calibration removes the slowly convergent
renewal tail. Chebyshev interpolation is enclosed by a Cauchy remainder;
no interpolated value is treated as exact. This is not an eigenstate fit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx

from certified_weil import endpoints
from renewal_trace_enclosures import kappa


def newton_coefficients(nodes, values):
    coefficients = list(values)
    for order in range(1,len(nodes)):
        for j in range(len(nodes)-1,order-1,-1):
            coefficients[j] = (coefficients[j]-coefficients[j-1])/(nodes[j]-nodes[j-order])
    return coefficients


def evaluate_newton(z,nodes,coefficients):
    value = acb(coefficients[-1])
    for j in range(len(nodes)-2,-1,-1):
        value = coefficients[j]+(z-nodes[j])*value
    return value


def spectral_panel(left,right,count=12,cutoff=64):
    if not right > left or not 4 <= count <= 24 or right-left > 2:
        raise ValueError('panel width in (0,2] and 4..24 nodes required')
    a,b = arb(left),arb(right)
    nodes = [(a+b)/2+(b-a)/2*(arb.pi()*(2*j+1)/(2*count)).cos()
             for j in range(count)]
    values = [kappa(((1+z.exp()).log())/2,cutoff) for z in nodes]
    coefficients = newton_coefficients(nodes,values)
    # The CBF sector bound gives |kappa(sqrt(1+exp(z)))| <=2*kappa(s(b))
    # on every unit disk centered in the panel. Jensen: kappa(s)<=sqrt(log(1+s)).
    majorant = (1+(1+b.exp()).sqrt()).log().sqrt()
    error = 4*majorant*((b-a)/4)**count
    return nodes,coefficients,error


def panel_integral(panel,left,right,x,a,kind):
    nodes,coefficients,error = panel
    x,a=arb(x),arb(a)
    if not x > 0 or not 0 < a < 1 or kind not in ('renewal','basis'):
        raise ValueError('x>0, 0<a<1 and renewal/basis kind required')
    def weights(z,analytic):
        ez=z.exp()
        s=(1+ez).sqrt(analytic=analytic)
        factor=ez/(s*(z*z+acb.pi()**2))
        if kind=='renewal':
            positive=a/(s*(s+a))
            negative=(-s*x).exp()/s
        else:
            positive=2*a*(-a*x).exp()/(s*s-a*a)
            negative=(-s*x).exp()/(s-a)
        return factor*positive,factor*negative
    def integrand(z,analytic):
        pos,neg=weights(z,analytic)
        return evaluate_newton(z,nodes,coefficients)*(pos-neg)
    def absolute_majorant(z,analytic):
        pos,neg=weights(z,analytic)
        return pos+neg
    options={'abs_tol':arb(2)**-80,'rel_tol':arb(2)**-80,'eval_limit':20000}
    value=acb.integral(integrand,left,right,**options)
    mass=acb.integral(absolute_majorant,left,right,**options)
    if not value.is_finite() or not mass.is_finite() or not value.imag.contains(0) or not mass.imag.contains(0):
        raise ArithmeticError('spectral-panel quadrature unresolved')
    return value.real, error*abs(mass.real).upper()


def tail_allowance(x,a,left,right,kind):
    x,a=arb(x),arb(a)
    if not x > 0 or not 0 < a < 1 or not left <= 0 or not right >= 2:
        raise ValueError('positive x, 0<a<1, left<=0 and right>=2 required')
    if kind=='renewal':
        near=(1+a)*arb(left).exp()/arb.pi()**2
        coefficient=a
        exponential_factor=arb(1)
    elif kind=='basis':
        near=(2*a/(1-a*a)+1/(1-a))*arb(left).exp()/arb.pi()**2
        # 1/(s^2-a^2)<=1/((1-a^2)*s^2), 1/(s-a)<=1/((1-a)*s).
        coefficient=2*a/(1-a*a)
        exponential_factor=1/(1-a)
    else:
        raise ValueError('unknown profile kind')
    R=arb(right)/2
    S=R.exp()
    H=R+arb(2).log()
    inverse_square_tail=2/arb.pi()**2*(-R).exp()*(H.sqrt()+1/(2*H.sqrt()))
    exponential_tail=2/arb.pi()**2*(-S*x).exp()/(x*S.sqrt())
    return near+coefficient*inverse_square_tail+exponential_factor*exponential_tail


def generate(count=12,width=1,left=-32,right=48,cutoff=64):
    if type(width) is not int or width not in (1,2) or (right-left)%width:
        raise ValueError('integer width 1 or 2 must partition the range')
    a=arb(1)/2
    J=1/kappa(a.log(),cutoff)
    points=[('1/8',arb(1)/8),('1/4',arb(1)/4),('1',arb(1)),('exp(-8)',(-arb(8)).exp())]
    totals={(label,kind):[arb(0),arb(0)] for label,_ in points for kind in ('renewal','basis')}
    for start in range(left,right,width):
        panel=spectral_panel(start,start+width,count,cutoff)
        for label,x in points:
            for kind in ('renewal','basis'):
                value,error=panel_integral(panel,start,start+width,x,a,kind)
                totals[label,kind][0]+=value
                totals[label,kind][1]+=error
        if (start-left)%8==0:
            print('spectral panels through',start+width,flush=True)
    rows=[]
    for label,x in points:
        row={'distance_label':label,'distance':endpoints(x)}
        for kind in ('renewal','basis'):
            integral,error=totals[label,kind]
            tail=tail_allowance(x,a,left,right,kind)
            enclosed=integral+arb(0,(error+tail).upper())
            if kind=='renewal':
                value=arb(2).sqrt()*x+J-arb(2).sqrt()/a+enclosed
            else:
                value=J*(arb(2).sqrt()/a*(1-2*(-a*x).exp())+(-a*x).exp()*J+enclosed)
            if not value > 0 or not value.is_finite():
                raise ArithmeticError('positive profile value unresolved')
            row[kind]=endpoints(value)
            row[kind+'_interpolation_allowance']=endpoints(error)
            row[kind+'_whole_tail_allowance']=endpoints(tail)
        V=arb(row['renewal']['lo']).union(arb(row['renewal']['hi']))
        h=arb(row['basis']['lo']).union(arb(row['basis']['hi']))
        if not h < J*V or not h > (-a*x).exp()*J*V:
            raise ArithmeticError('exact Green-convolution ratio check unresolved')
        rows.append(row)
    sources=[Path(__file__),Path(__file__).with_name('renewal_trace_enclosures.py')]
    return {'status':'renewal_profiles_and_exact_trace_basis_enclosed','bits':ctx.prec,
            'nodes_per_panel':count,'panel_width':width,'spectral_z_range':[left,right],
            'wiener_hopf_cutoff':cutoff,'basis_decay':endpoints(a),'exact_basis_trace':endpoints(J),
            'rows':rows,'scope':'Established Stieltjes representation plus written calibration/Cauchy-tail bounds. Profiles of a Green basis, not actual Weil minimizing-state values or residual certificates.',
            'source_hashes':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--nodes',type=int,default=12)
    parser.add_argument('--width',type=int,default=1)
    args=parser.parse_args()
    with ctx.workprec(256):
        data=generate(args.nodes,args.width)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
