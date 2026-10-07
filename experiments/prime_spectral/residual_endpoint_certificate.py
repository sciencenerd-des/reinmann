"""Linear residual-to-trace bounds and improved actual two-state envelopes.

Residuals must be FULL operator L2/Linfinity residuals of a unit trial in
D(A). A finite projected residual is not sufficient. This generator records
constants and required budgets; it does not claim a trial clears a budget.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import arb,ctx

from certified_weil import endpoints
from threshold_ground_gap import box


def bounds_for_interval(length,prime_norm,ground_upper,mass_one):
    L,m,U,V1=map(arb,(length,prime_norm,ground_upper,mass_one))
    if not all(v.is_finite() for v in (L,m,U,V1)) or not L > arb(1)/2 or not m >= 0 or not V1 > 0:
        raise ValueError('L>1/2, m>=0 and V(1)>0 required')
    c=(2*arb.pi()).log()
    kstar=arb(5)/4+2*(L/2).cosh()
    knorm=L*kstar
    E0=c+knorm+m
    candidates=[]
    for time in ('51/100','13/25','21/40','53/100','11/20','3/5','3/4','1'):
        t=arb(time)
        Ct=((t-arb(1)/2).gamma()/(2*arb.pi().sqrt()*t.gamma())).sqrt()
        candidates.append((time,((U+E0)*t).exp()*(Ct+t*L.sqrt()*kstar)))
    time,M=min(candidates,key=lambda row:row[1].upper())
    G=max((knorm+m).upper(),(U+c).upper())+knorm+m+8
    MF=G*M
    trace=V1*(arb(9)/4*MF+M/(8*arb(1).exp()))
    return {'L':L,'m':m,'U':U,'V1':V1,'E0':E0,'M':M,'G':G,'MF':MF,
            'trace':trace,'time':time,'knorm':knorm,'kstar':kstar}


def residual_constants(bounds,clearance):
    h=arb(clearance)
    if not h.is_finite() or not h > 0:
        raise ValueError('positive full complementary clearance required')
    L,M,G,V1=(bounds[k] for k in ('L','M','G','V1'))
    t=arb(bounds['time'])
    Qinf=1+M*L.sqrt()
    alpha=V1*(arb(9)/4*G+1/(8*arb(1).exp()))
    A=alpha*M/h
    B=Qinf*(alpha*t*((bounds['U']+bounds['E0'])*t).exp()+arb(9)/4*V1)
    return A,B


def residual_trace_interval(trial_lo,trial_hi,epsilon2,epsiloninf,clearance,A,B):
    p,q,e2,ei,h,a,b=map(arb,(trial_lo,trial_hi,epsilon2,epsiloninf,clearance,A,B))
    if not all(v.is_finite() for v in (p,q,e2,ei,h,a,b)) or not q >= p or not e2 >= 0 or not ei >= 0 or not h > 0 or not a >= 0 or not b >= 0:
        raise ValueError('ordered trace and nonnegative residual constants required')
    rho=e2/h
    if not rho < 1:
        raise ValueError('full residual-to-clearance ratio must be less than one')
    overlap=(1-rho*rho).sqrt()
    error=a*e2+b*ei
    lo,hi=p-error,q+error
    corners=(lo,hi,lo/overlap,hi/overlap)
    return min(v.lower() for v in corners),max(v.upper() for v in corners)


def generate():
    basis_path=Path('research/prime_spectral/verification_2026_10_07_boundary_basis/renewal_basis.json')
    gap_path=Path('research/prime_spectral/verification_2026_10_07_trace_stability/threshold_ground_gaps.json')
    basis=json.loads(basis_path.read_text())
    gaps=json.loads(gap_path.read_text())
    for path,digest in basis['source_hashes'].items():
        if hashlib.sha256(Path(path).read_bytes()).hexdigest()!=digest:
            raise ArithmeticError('stale boundary-basis source')
    records=[]
    with ctx.workprec(256):
        V1=box(next(r for r in basis['rows'] if r['distance_label']=='1')['renewal'])
        weights={q:2*arb(q).log()/arb(q).sqrt() for q in (2,3)}
        for prime in (2,3):
            row=next(r for r in gaps['results'] if r['threshold_prime']==prime)
            U,L2=(('142/100000','999/100000') if prime==2 else
                  ('103/1000000000','109/1000000000'))
            U,L2=arb(U),arb(L2)
            if not box(row['trial_ground_eigenvalue_upper']) < U or not box(row['second_eigenvalue_lower']) > L2:
                raise ArithmeticError('saved full-operator spectral inputs insufficient')
            threshold=bounds_for_interval(arb(prime).log(),arb(0) if prime==2 else weights[2],U,V1)
            A,B=residual_constants(threshold,L2-U)
            budget=arb('1e-3')/(A+B)
            if not budget/(L2-U) < arb('1e-2'):
                raise ArithmeticError('budget does not isolate the ground component')
            cell=bounds_for_interval(arb('7/10' if prime==2 else '6/5'),
                                     weights[2] if prime==2 else weights[2]+weights[3],U,V1)
            def serial(bound):
                return {**{key:endpoints(bound[key]) for key in
                            ('L','m','U','E0','M','G','MF','trace')},'heat_time':bound['time']}
            records.append({'threshold_prime':prime,'fixed_threshold_bounds':serial(threshold),
                            'one_sided_two_minimizer_bounds':serial(cell),
                            'fixed_threshold_clearance':endpoints(L2-U),
                            'L2_residual_trace_coefficient':endpoints(A),
                            'Linfty_residual_trace_coefficient':endpoints(B),
                            'equal_residual_budget_for_complement_trace_error_1e-3':endpoints(budget),
                            'split_L2_budget_for_complement_trace_error_1e-3':endpoints(arb('5e-4')/A),
                            'split_Linfty_budget_for_complement_trace_error_1e-3':endpoints(arb('5e-4')/B)})
    sources=[Path(__file__),basis_path,gap_path,Path(__file__).with_name('threshold_ground_gap.py')]
    return {'status':'actual_state_envelopes_and_conditional_residual_trace_constants_enclosed',
            'records':records,'bits':256,
            'scope':'One-sided envelopes bound both actual full and prime-omitted minimizing states. Residual constants use only the fixed-threshold gap, assume a unit D(A) trial with Rayleigh mu<=U, and do not certify any actual trial residual or nonzero trace.',
            'source_hashes':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=generate()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
