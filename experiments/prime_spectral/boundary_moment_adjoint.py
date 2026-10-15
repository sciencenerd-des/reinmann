"""Actual Weil adjoints with free endpoint values and coherent tail moments.

Compactly supported piecewise smooth corrections lie in the logarithmic
operator domain by bounded variation Fourier decay. Every boundary and
omitted-mode contribution is retained. Floating selection is untrusted.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from flint import acb, arb, ctx

from adjoint_fourier_certificate import l2_norm_bounds, matrix_inputs, sequence_bound
from canonical_prolate_adjoint import (OUT as PROLATE_DIR, CanonicalProfile,
    complex_box, external_target)
from certified_weil import endpoints
from full_ground_fourier import OUTPUT, energy_distance, sha256
from orthogonal_fourier_transfer import protected_mean, validated_base
from threshold_ground_gap import box
from weil_matrix import prime_powers

OUT=Path('research/prime_spectral/verification_2026_10_11_boundary_moment')


def coefficients(exact):
    if not isinstance(exact,list) or len(exact)<2 or any(len(v)!=2 for v in exact):
        raise ValueError('constant and positive exact complex coefficients required')
    h=[acb(arb(re),arb(im)) for re,im in exact]
    if any(not v.is_finite() for v in h):
        raise ValueError('finite correction coefficients required')
    return h


def asymptotic_sequence_bound(cutoff,prefix):
    """|b_m| <= 1/4 + prime oscillation amplitudes + D/(P+1), m>P."""
    if type(cutoff) is not int or cutoff<2 or type(prefix) is not int or prefix<1:
        raise ValueError('integer cutoff at least two and positive prefix required')
    L=arb(cutoff).log()
    # rho(r)-1/(2r)=(E(r)-r*S(r))/(2*sinhc(r)).
    # E'=int t exp(tr/2)dt/4, S'=int t(1-t)^2 sinh(tr)dt/2.
    derivative=(L/2).sinh()+((L/2).exp()/8+L.cosh()/6+L*L.sinh()/24)/2
    derivative+=((L/2).exp()/2+L*L.cosh()/6)*L.sinh()/4
    D=(arb('1/2')+L*L*derivative)/arb.pi()**2
    primes=sum((arb(p).log()/(arb.pi()*arb(q).sqrt())
                for q,p in prime_powers(cutoff) if q<cutoff),arb(0))
    B=arb('1/4')+primes+D/(prefix+1)
    return B,{'regular_kernel_derivative_bound':endpoints(derivative),
              'archimedean_asymptotic_error_coefficient':endpoints(D),
              'prime_oscillation_amplitudes':endpoints(primes),'sequence_tail_bound':endpoints(B)}


def inverse_power_norm(power,prefix):
    return 1/((2*power-1)*arb(prefix)**(2*power-1)).sqrt()


def coherent_tail(cutoff,exact,b,z,prefix,order=2):
    """Geometric expansions retain boundary and signed moment cancellation."""
    h=coefficients(exact);N=len(h)-1;P=prefix
    if (type(P) is not int or P<=N or len(b)<=N or type(order) is not int or order<1):
        raise ValueError('prefix beyond correction and positive tail expansion order required')
    rho=1-(arb(N)/(P+1))**2
    a=acb(z)*arb(cutoff).log()/2;u=(a/arb.pi())**2
    eta=1-abs(u)/(P+1)**2
    if not eta>0:
        raise ArithmeticError('Fourier target geometric tail unresolved')
    K=arb(2).sqrt()*a*a.sin()/arb.pi()**2
    B,details=asymptotic_sequence_bound(cutoff,P)
    endpoint=h[0]+arb(2).sqrt()*sum(h[1:],acb(0))
    boundary=arb(2).sqrt()*abs(endpoint)*B*inverse_power_norm(1,P)
    total=boundary;moments=[]
    for j in range(order):
        T=sum((n**(2*j+1)*b[n]*h[n] for n in range(1,N+1)),acb(0))
        S=sum((n**(2*j+2)*h[n] for n in range(1,N+1)),acb(0))
        even=-2*T+K*u**j;odd=2*S
        total+=abs(even)*inverse_power_norm(2*j+2,P)
        total+=B*abs(odd)*inverse_power_norm(2*j+3,P)
        moments.append({'even_power':2*j+2,'even_coefficient':complex_box(even),
                        'odd_power':2*j+3,'odd_coefficient_times_b_m':complex_box(odd)})
    # Entire remainder after the finite geometric expansions.
    force=2*sum((n**(2*order+1)*abs(b[n]*h[n]) for n in range(1,N+1)),arb(0))/rho
    bforce=2*B*sum((n**(2*order+2)*abs(h[n]) for n in range(1,N+1)),arb(0))/rho
    target=abs(K)*abs(u)**order/eta
    remainder=(force+target)*inverse_power_norm(2*order+2,P)+bforce*inverse_power_norm(2*order+3,P)
    total+=remainder
    return total,{**details,'endpoint_coefficient':complex_box(endpoint),
        'boundary_tail_upper':endpoints(boundary),'coherent_moments':moments,
        'entire_geometric_remainder_upper':endpoints(remainder),'tail_L2_upper':endpoints(total)}


def select_free(matrix,b,k,z,cutoff,nu,delta,order=2,free_boundary=True):
    """Least squares includes boundary and coherent-tail proxies; no proof uses it."""
    import numpy as np
    P=len(matrix)-1;N=len(matrix[0])-1
    A=np.array([[float(x.mid()) for x in row] for row in matrix])
    for n in range(N+1):A[n,n]-=float(nu.mid())
    rhs=np.array([complex(float(x.real.mid()),float(x.imag.mid())) for x in k])
    B=float(asymptotic_sequence_bound(cutoff,P)[0].upper())
    a=complex(z)*float(arb(cutoff).log())/2
    import cmath
    K=np.sqrt(2)*a*cmath.sin(a)/np.pi**2;u=(a/np.pi)**2
    extra=[float(delta.upper())*np.eye(N+1)];targets=[np.zeros(N+1,dtype=complex)]
    endpoint=np.array([1,*[np.sqrt(2) for _ in range(N)]])
    extra.append((np.sqrt(2)*B*float(inverse_power_norm(1,P)))*endpoint[None,:])
    targets.append(np.zeros(1,dtype=complex))
    for j in range(order):
        w=float(inverse_power_norm(2*j+2,P))
        extra.append(np.array([[0,*[-2*n**(2*j+1)*float(b[n].mid())*w for n in range(1,N+1)]]]))
        targets.append(np.array([-K*u**j*w]))
        w=2*B*float(inverse_power_norm(2*j+3,P))
        extra.append(np.array([[0,*[n**(2*j+2)*w for n in range(1,N+1)]]]))
        targets.append(np.zeros(1,dtype=complex))
    A=np.vstack([A,*extra]);rhs=np.concatenate([rhs,*targets])
    if free_boundary:
        D=np.eye(N+1)
    else:
        D=np.vstack([-np.sqrt(2)*np.ones(N),np.eye(N)])
    selected,_,rank,_=np.linalg.lstsq(A@D,rhs,rcond=None)
    if rank!=D.shape[1]:raise ArithmeticError('floating correction selector rank deficiency')
    h=D@selected
    return [[format(v.real,'.17g'),format(v.imag,'.17g')] for v in h]


def trial_target_pairing(profile,z,trial):
    """Entire finite-trial/target pairing with shared moments cancelled first."""
    c=list(map(arb,trial));norm=sum((v*v for v in c),arb(0)).sqrt()
    if not norm>0:raise ValueError('nonzero trial required')
    g=[v/norm for v in c];L=profile.length;J=profile.order
    moments=[arb(0) for _ in range(J)]
    for j in range(J):
        if j%2==0:moments[j]=g[0]*(L/2)**j/(j+1)
    for n in range(1,len(g)):
        omega=2*arb.pi()*n/L;integral=acb(0)
        for j in range(1,J):
            integral=((L/2)**j-(-L/2)**j-j*integral)/acb(0,omega)
            if j%2==0:moments[j]+=g[n]*arb(2).sqrt()*integral.real/L
    mean=profile.moments[0];value=acb(0)
    for j in range(J-1,0,-1):
        value=value*(-acb(0,1)*z)+(moments[j]-g[0]*profile.moments[j]/mean)/math.factorial(j)
    value*=-acb(0,1)*z
    R=abs(acb(z))*L/2
    remainder=R.exp()*R**J/math.factorial(J)*(1+abs(g[0])*L.sqrt()*profile.trial_norm_upper/arb(mean.lower()))
    e0=L.sqrt()*profile.output_error;ez=e0*(abs(acb(z).imag)*L/2).exp()
    exact_error=abs(g[0])*(ez+abs(profile.raw_taylor(z)/mean)*e0)/(mean-e0)
    from canonical_prolate_adjoint import widen
    return widen(value,remainder+exact_error)


def ground_pairing_upper(vector, norm_upper, trial, mass, known_pairing=None):
    """Use the certified ground angle and an actual finite-trial pairing."""
    c=list(map(arb,trial));mass=arb(mass);norm_upper=arb(norm_upper)
    if (not c or len(c)>len(vector) or any(not v.is_finite() for v in c) or not sum((v*v for v in c),arb(0))>0
            or not mass.is_finite() or not 0<=mass<1 or not norm_upper>=0):
        raise ValueError('nonzero finite trial, orthogonal mass in [0,1), nonnegative norm required')
    norm=sum((v*v for v in c),arb(0)).sqrt();g=[v/norm for v in c]
    q=sum((g[n]*vector[n] for n in range(min(len(g),len(vector)))),acb(0))
    if known_pairing is not None:
        q=acb(known_pairing)
        if not q.is_finite():raise ValueError('finite known pairing required')
    q_lower=arb(max(0,abs(q).lower()));q_upper=arb(abs(q).upper())
    complement_squared=norm_upper**2-q_lower**2
    complement=arb(max(0,complement_squared.upper())).sqrt()
    estimate=q_upper+arb(mass.upper()).sqrt()*complement
    bound=arb(min(norm_upper.upper(),estimate.upper()))
    return bound,{'trial_pairing':complex_box(q),'full_norm_upper':endpoints(norm_upper),
                  'orthogonal_complement_norm_upper':endpoints(complement),'ground_pairing_upper':endpoints(bound)}


def certify(cutoff,exact,matrix,b,z,profile,nu,delta,mean,order=2,trial=None,mass=None):
    h=coefficients(exact);N=len(h)-1;P=len(matrix)-1
    if (cutoff!=profile.cutoff or not matrix or len(matrix[0])!=len(h) or any(len(row)!=len(h) for row in matrix)
        or not all(v.is_finite() for v in (nu,delta,mean)) or not delta>=0 or not mean>0):
        raise ValueError('valid full adjoint inputs required')
    p,k=external_target(z,arb(cutoff).log(),profile,P)
    residual=[sum((row[n]*h[n] for n in range(N+1)),acb(0))-k[m]
              -(nu*h[m] if m<=N else 0) for m,row in enumerate(matrix)]
    prefix=l2_norm_bounds(residual);tail,details=coherent_tail(cutoff,exact,b,z,P,order)
    full=(arb(prefix.upper())**2+arb(tail.upper())**2).sqrt()
    norm=l2_norm_bounds(h);uncertainty=delta*norm
    error=(full+uncertainty)/mean
    correlation={}
    if trial is not None:
        if len(trial)>len(h) or len(trial)>len(matrix):
            raise ValueError('trial coordinates must be included in correction and residual prefixes')
        c=list(map(arb,trial));gnorm=sum((v*v for v in c),arb(0)).sqrt();g=[v/gnorm for v in c]
        pairing=sum((h[n]*(sum((g[i]*matrix[i][n] for i in range(len(g))),arb(0))
                      -(nu*g[n] if n<len(g) else 0)) for n in range(N+1)),acb(0))
        pairing-=trial_target_pairing(profile,z,trial)
        R,R_details=ground_pairing_upper(residual,arb(full.upper()),trial,mass,known_pairing=pairing)
        H,H_details=ground_pairing_upper(h,arb(norm.upper()),trial,mass)
        correlation={'residual':R_details,'correction':H_details}
        refined=(R+delta*H)/mean
        refined=arb(min(error.upper(),refined.upper()))
    else:
        refined=error
    return {'exact_coefficients':exact,'target_profile':complex_box(p),
            'prefix_residual_norm':endpoints(prefix),'tail':details,'full_residual_norm_upper':endpoints(full),
            'correction_norm':endpoints(norm),'eigenvalue_uncertainty_times_norm':endpoints(uncertainty),
            'cauchy_profile_error_upper':endpoints(error),'ground_correlation':correlation,
            'normalized_profile_error_upper':endpoints(refined)}


def generate(directory=OUT,cover_cells=None,modes=16,prefix=128):
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    base_path=OUTPUT/'full_ground_fourier.json';base=validated_base(base_path)
    dependencies={str(base_path):sha256(base_path)};results=[]
    with ctx.workprec(1024):
        for row in base['results']:
            C=row['threshold_prime']
            profile=CanonicalProfile(PROLATE_DIR/f'jacobi_C{C}_T40.json',PROLATE_DIR/f'vectors_C{C}_T40.json')
            dependencies.update(profile.provenance)
            ell=arb(box(row['full_ground_lower']).lower());upper=arb(box(row['trial_rayleigh_enclosure']).upper())
            nu=(ell+upper)/2;delta=(upper-ell)/2
            r,_=energy_distance(box(row['trial_rayleigh_enclosure']),ell,box(row['full_second_lower']))
            c=list(map(arb,row['exact_cosine_coefficients']));m=c[0]/sum((v*v for v in c),arb(0)).sqrt()
            mean=arb(protected_mean(r,m).lower())
            with ctx.workprec(384):
                matrix,b,path=matrix_inputs(C,modes,prefix,PROLATE_DIR if (modes,prefix)==(16,128) else directory)
            dependencies[str(path)]=sha256(path)
            probes=[]
            for re,im in [('0','2/5'),('1','0'),('1','2/5'),('1','-2/5')]:
                z=acb(re,im);_,k=external_target(z,profile.length,profile,prefix)
                exact=select_free(matrix,b,k,z,C,nu,delta)
                checked=certify(C,exact,matrix,b,z,profile,nu,delta,mean,trial=row['exact_cosine_coefficients'],mass=arb(r.upper()))
                checked['z']={'real':re,'imag':im};probes.append(checked)
            result={'cutoff':C,'spectral_shift':endpoints(nu),'eigenvalue_uncertainty':endpoints(delta),
                    'ground_mean_lower':endpoints(mean),'ground_trial_coefficients':row['exact_cosine_coefficients'],
                    'ground_orthogonal_mass_upper':endpoints(arb(r.upper())),'probes':probes}
            if cover_cells:
                nx,ny=cover_cells
                if min(nx,ny)<1:raise ValueError('positive cell counts required')
                records=[];maximum=arb(0)
                for i in range(nx):
                    for j in range(2*ny):
                        x0,x1=arb(i)/nx,arb(i+1)/nx
                        y0,y1=arb(2)*(j-ny)/(5*ny),arb(2)*(j+1-ny)/(5*ny)
                        center=acb((x0+x1)/2,(y0+y1)/2);z=acb(x0.union(x1),y0.union(y1))
                        _,k=external_target(center,profile.length,profile,prefix)
                        exact=select_free(matrix,b,k,center,C,nu,delta)
                        checked=certify(C,exact,matrix,b,z,profile,nu,delta,mean,trial=row['exact_cosine_coefficients'],mass=arb(r.upper()))
                        checked['cell']=[i,j];records.append(checked)
                        maximum=arb(max(maximum.upper(),arb(checked['normalized_profile_error_upper']['hi']).upper()))
                result['rectangle_cover']={'region':'|Re z|<=1, |Im z|<=2/5','real_half_subdivisions':nx,
                    'imag_half_subdivisions':ny,'symmetry':'Real candidate reflects Re z; both signs of Im z explicitly covered',
                    'normalized_profile_error_upper':endpoints(maximum),'cells':records}
            results.append(result)
            print('free boundary coherent-tail adjoints checked:',C,flush=True)
    names=('boundary_moment_adjoint.py','canonical_prolate_adjoint.py','adjoint_fourier_certificate.py',
        'full_ground_fourier.py','orthogonal_fourier_transfer.py','threshold_ground_gap.py','certified_weil.py','weil_matrix.py',
        'certified_prolate_jacobi.py','certified_prolate_vectors.py','certified_prolate_projection.py')
    return {'status':'free_boundary_coherent_tail_full_weil_adjoint','bits':1024,'matrix_bits':384,
            'modes':modes,'prefix':prefix,'tail_order':2,'results':results,'dependency_sha256':dependencies,
            'source_sha256':{str(Path(__file__).with_name(n)):sha256(Path(__file__).with_name(n)) for n in names},
            'scope':'Written bounded-variation operator-domain proof, asymptotic sequence and coherent full-tail analysis plus Arb arithmetic. Fixed cutoffs only; no growing-support rate or RH proof.'}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',type=Path,default=OUT)
    parser.add_argument('--cover-cells',nargs=2,type=int)
    parser.add_argument('--modes',type=int,default=16)
    parser.add_argument('--prefix',type=int,default=128)
    args=parser.parse_args()
    result=generate(args.directory,args.cover_cells,args.modes,args.prefix)
    suffix='' if not args.cover_cells else f'_cover{args.cover_cells[0]}x{args.cover_cells[1]}'
    (args.directory/f'boundary_moment_N{args.modes}_M{args.prefix}{suffix}.json').write_text(json.dumps(result,indent=2)+'\n')
