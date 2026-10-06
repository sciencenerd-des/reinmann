"""Anchor-dependent theta-tail bound with no fixed absolute error floor."""
from fractions import Fraction
import math
from flint import arb,ctx


def saddle_theta_bound(threshold, order=16):
    X=Fraction(threshold)
    if X<10**6 or type(order) is not int or not 1<=order<=64:
        raise ValueError('threshold>=1000000 and integer order 1..64 required')
    with ctx.workprec(512):
        x=arb(str(X))
        u=(2*x/arb.pi()).lambertw()/2
        L=(32*u).sqrt()
        h=L/(x*(1+2*u)).sqrt()
        D=2*u*h*h.exp()
        denominator=(1-16*(-5*arb.pi()).exp())*(1-3/(2*arb.pi()))
        if not denominator>0:
            raise ArithmeticError('global theta denominator unresolved')
        C=16/denominator
        global_ratio=C*(-3*arb.pi()).exp()
        high_ratio=C*math.factorial(order)*(u/(3*x))**order*(order*D).exp()
        return {'threshold':str(X),'order':order,
                'global_relative_upper':str(global_ratio.upper().fmpq()),
                'saddle_region_relative_upper':str(high_ratio.upper().fmpq()),
                'scope':'For every anchor a>=threshold, Phi(v)-phi1(v)<=high*phi1(v) for v>=u(a)*exp(-L(a)/sqrt(A(a))); global*phi1(v) bounds the omitted sum for every v>=0.',
                'proof':'Geometric theta sum and exp(-z)<=order!/z^order; u(a)/a and u(a)*h(a) decrease.'}
