"""Series derivative probe with FLINT0.8-compatible sinh and analytic cross-check.

The original measurement driver is frozen; this companion binds the exact API
adaptation without changing any source hash of the running spectrum jobs.
"""
from pathlib import Path
import json
from flint import acb,acb_series,arb,ctx
import final_log_mechanism as calibration
from control_zero_attribution import transform
from full_ground_fourier import sha256


def checked_jet(z,length,v,parity):
    old=ctx.cap
    try:
        ctx.cap=3;w=acb_series([z,1])*length/2;sinh=(w.exp()-(-w).exp())/2
        if parity=='even':
            R=v[0]/w
            for n in range(1,len(v)):R+=arb(2).sqrt()*v[n]*w/(w*w+(arb.pi()*n)**2)
            result=length.sqrt()*sinh*R
        else:
            R=sum((v[n-1]*arb.pi()*n/(w*w+(arb.pi()*n)**2) for n in range(1,len(v)+1)),acb_series([0]))
            result=-(2*length).sqrt()*sinh*R
        a=z*length/2
        if parity=='even':
            R=v[0]/a;D=-v[0]/a**2
            for n in range(1,len(v)):
                p=arb.pi()*n;den=a*a+p*p
                R+=arb(2).sqrt()*v[n]*a/den;D+=arb(2).sqrt()*v[n]*(p*p-a*a)/den**2
            derivative=length.sqrt()*length/2*(a.cosh()*R+a.sinh()*D)
        else:
            R=sum((v[n-1]*arb.pi()*n/(a*a+(arb.pi()*n)**2) for n in range(1,len(v)+1)),acb(0))
            D=sum((-2*v[n-1]*arb.pi()*n*a/(a*a+(arb.pi()*n)**2)**2 for n in range(1,len(v)+1)),acb(0))
            derivative=-(2*length).sqrt()*length/2*(a.cosh()*R+a.sinh()*D)
        if not result[0].overlaps(transform(z,length,v,parity)) or not result[1].overlaps(derivative):raise ArithmeticError('independent value/analytic derivative check failed')
        return result
    finally:ctx.cap=old


if __name__=='__main__':
    calibration.transform_jet=checked_jet
    calibration.witness_decay()
    p=calibration.OUT/'saved_witness_derivatives.json';d=json.loads(p.read_text());d['source_sha256'][Path(__file__).name]=sha256(Path(__file__));d['method']='FLINT0.8 series sinh via(exp(w)-exp(-w))/2; all six values checked against stored transform formula and all six derivatives against analytic product-rule formula.';d['independent_formula_checks_passed']=12
    p.write_text(json.dumps(d,indent=2)+'\n')
