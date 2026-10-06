"""Conditional, explicit moment-error propagation into log-epsilon curvature.

The caller must establish the supplied moment errors over its whole domain.
This module cannot infer a saddle remainder from sample agreement.
"""
from flint import arb
from laboratory import endpoints


def log_moment_errors(model,relative):
    if len(model)!=3 or len(relative)!=3 or not all(v.is_finite() for v in model) or not model[0]>0:
        raise ValueError('three model moments with positive zeroth moment required')
    if not all(e.is_finite() and e>=0 for e in relative) or not relative[0]<1:
        raise ValueError('nonnegative finite errors and zeroth error below one required')
    e0,e1,e2=relative
    a=abs(model[1]/model[0]).upper()
    b=abs(model[2]/model[0]).upper()
    first=a*(e1+e0)/(1-e0)
    second=b*(e2+e0)/(1-e0)+first*(2*a+first)
    return (-(1-e0).log()).upper(),first.upper(),second.upper()


def curvature_value(x,q,L,M):
    return -1/(x+1)**2-q*M/(1-q)-q*L**2/(1-q)**2


def curvature_transfer(x,q,L,M,errors):
    x,q,L,M=map(arb,(x,q,L,M))
    if len(errors)!=3 or not all(e.is_finite() and e>=0 for e in errors) or not x>=1:
        raise ValueError('x>=1 and three nonnegative finite absolute errors required')
    e0,e1,e2=errors
    qbox=q+arb(0,e0.upper())
    if not 0<qbox<1:
        raise ArithmeticError('positive deficit domain unresolved after error propagation')
    qmax=qbox.upper()
    d=(1-qbox).lower()
    A=abs(L).upper()+e1
    B=abs(M).upper()+e2
    bound=(B/d**2+(1+qmax)*A**2/d**3)*e0
    bound+=2*qmax*A/d**2*e1+qmax/d*e2
    center=curvature_value(x,q,L,M)
    result=center+arb(0,bound.upper())
    return {'status':'negative_under_supplied_error_hypotheses' if result<0 else 'unresolved',
            'reference_curvature':endpoints(center),'curvature_error_upper':str(bound.upper().fmpq()),
            'curvature_enclosure':endpoints(result),
            'obligation':'Supplied reference and error bounds must hold throughout the claimed domain; this function establishes no saddle remainder.'}


def propagate_moment_errors(x,models,relative):
    x=arb(x)
    if not x.is_finite() or not x>=1:
        raise ValueError('finite x>=1 required')
    if len(models)!=3 or len(relative)!=3:
        raise ValueError('neighboring moment triples at x-1,x,x+1 required')
    errors=[log_moment_errors(v,e) for v,e in zip(models,relative)]
    totals=[errors[0][k]+2*errors[1][k]+errors[2][k] for k in range(3)]
    p=[v[1]/v[0] for v in models]
    pp=[v[2]/v[0]-(v[1]/v[0])**2 for v in models]
    q=2*x*(2*x-1)/((2*x+2)*(2*x+1))*models[0][0]*models[2][0]/models[1][0]**2
    L=1/x+2/(2*x-1)-2/(2*x+2)-2/(2*x+1)+p[0]+p[2]-2*p[1]
    M=-1/x**2-4/(2*x-1)**2+4/(2*x+2)**2+4/(2*x+1)**2+pp[0]+pp[2]-2*pp[1]
    eq=abs(q).upper()*(totals[0].exp()-1)
    return curvature_transfer(x,q,L,M,(eq.upper(),totals[1].upper(),totals[2].upper()))
