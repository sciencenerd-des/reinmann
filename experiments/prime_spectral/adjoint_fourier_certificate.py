"""Full Weil adjoint residuals for endpoint-zero cosine corrections.

Floating least squares selects exact decimal coefficients only. Arb checks
their actual residual prefix, the entire analytic cosine tail, correction
norm, eigenvalue uncertainty and protected Fourier mean.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx

from certified_weil import entry, endpoints
from full_ground_fourier import OUTPUT, energy_distance, sha256
from orthogonal_fourier_transfer import protected_mean, validated_base
from threshold_ground_gap import box
from weil_matrix import prime_powers

OUT=Path('research/prime_spectral/verification_2026_10_11_adjoint_fourier')


def payload_hash(data):
    return hashlib.sha256(json.dumps({key:data[key] for key in ('b_sequence','even_diagonal')},sort_keys=True).encode()).hexdigest()


def sequence_bound(cutoff):
    """Uniform |b_m| bound, including the singular sine integral and all primes."""
    if cutoff not in (2,3):
        raise ValueError('threshold cutoff 2 or 3 required')
    L=arb(cutoff).log()
    regular=2*(L/2).cosh()+(L/2).exp()/4+L*L.cosh()/12
    primes=sum((arb(p).log()/arb(q).sqrt() for q,p in prime_powers(cutoff) if q<cutoff),arb(0))
    return (arb(3)/2+L*regular+primes)/arb.pi()


def matrix_inputs(cutoff,modes,prefix,directory):
    if cutoff not in (2,3) or not 1<=modes<prefix:
        raise ValueError('threshold and 1 <= modes < prefix required')
    path=Path(directory)/f'matrix_C{cutoff}_N{modes}_M{prefix}.json'
    hashes={name:sha256(Path(__file__).with_name(name)) for name in ('certified_weil.py','weil_matrix.py')}
    if path.exists():
        data=json.loads(path.read_text())
        if (data.get('source_sha256')!=hashes or data.get('cutoff')!=cutoff
                or data.get('modes')!=modes or data.get('prefix')!=prefix or data.get('bits')!=384):
            raise ValueError('matrix input provenance mismatch')
        if data.get('payload_sha256')!=payload_hash(data):
            raise ValueError('matrix payload hash mismatch')
    else:
        L=arb(cutoff).log(); powers=prime_powers(cutoff)
        seq=[arb(0)]
        for n in range(1,prefix+1):
            seq.append(n*entry(n,0,L,powers,cutoff))
        diag=[entry(0,0,L,powers,cutoff)]
        diag += [entry(n,n,L,powers,cutoff)+entry(n,-n,L,powers,cutoff) for n in range(1,modes+1)]
        data={'cutoff':cutoff,'modes':modes,'prefix':prefix,'bits':384,
              'b_sequence':[endpoints(x) for x in seq], 'even_diagonal':[endpoints(x) for x in diag],
              'source_sha256':hashes}
        data['payload_sha256']=payload_hash(data)
        path.parent.mkdir(parents=True,exist_ok=True); path.write_text(json.dumps(data,indent=2)+'\n')
    if len(data['b_sequence'])!=prefix+1 or len(data['even_diagonal'])!=modes+1:
        raise ValueError('matrix input dimensions mismatch')
    b=list(map(box,data['b_sequence'])); diag=list(map(box,data['even_diagonal']))
    B=sequence_bound(cutoff)
    if any(not abs(x)<B for x in b):
        raise ArithmeticError('uniform sequence bound failed a known coefficient')
    matrix=[]
    for m in range(prefix+1):
        row=[]
        for n in range(modes+1):
            if m==n: value=diag[m]
            elif m==0: value=arb(2).sqrt()*b[n]/n
            elif n==0: value=arb(2).sqrt()*b[m]/m
            else: value=2*(m*b[m]-n*b[n])/(m*m-n*n)
            row.append(value)
        matrix.append(row)
    return matrix,b,path


def fourier_coordinate(z,length,n):
    a=acb(z)*length/2
    if n==0: return a.sinc()
    denominator=a*a-(n*arb.pi())**2
    if not denominator.contains(0):
        # Cancel the opposite sinc terms analytically before interval
        # evaluation. Important on cells, where separate terms lose this.
        return arb(2).sqrt()*a*a.sin()/denominator
    return (-1)**n*((a-n*arb.pi()).sinc()+(a+n*arb.pi()).sinc())/arb(2).sqrt()


def target_coordinates(z,length,trial,prefix):
    if acb(z).is_zero():
        return acb(1),[acb(0) for _ in range(prefix+1)]
    c=list(map(arb,trial))
    if not c or any(not x.is_finite() for x in c) or not c[0]>0:
        raise ValueError('finite trial with positive mean required')
    positive=[fourier_coordinate(z,length,n) for n in range(1,max(prefix+1,len(c)))]
    k0=-sum((c[n]*positive[n-1]/c[0] for n in range(1,len(c))),acb(0))
    profile=fourier_coordinate(z,length,0)-k0
    k=[k0,*positive[:prefix]]
    return profile,k


def endpoint_zero_coefficients(positive):
    h=[acb(arb(x[0]),arb(x[1])) for x in positive]
    if not h or any(not x.is_finite() for x in h):
        raise ValueError('finite nonempty exact-decimal coefficient list required')
    return [-arb(2).sqrt()*sum(h,acb(0)),*h]


def l2_norm_bounds(values):
    """Keep nonnegative norm endpoints even when balls straddle zero.

    Squaring a midpoint-radius enclosure can have a slightly negative
    outward lower endpoint. Clamp only known-nonnegative squared norms.
    """
    if any(not x.is_finite() for x in values):
        raise ValueError('finite complex coordinate enclosures required')
    lower=sum((arb(max(0,abs(x).lower()))**2 for x in values),arb(0))
    upper=sum((arb(abs(x).upper())**2 for x in values),arb(0))
    lo=arb(max(0,lower.lower())).sqrt()
    hi=arb(upper.upper()).sqrt()
    return arb(lo.lower()).union(arb(hi.upper()))


def full_tail(cutoff,positive,b,z,prefix):
    """All omitted residual modes, using the exact endpoint-zero cancellation."""
    h=endpoint_zero_coefficients(positive); N=len(positive); M=prefix
    if not type(M) is int or not M>N or len(b)<=N:
        raise ValueError('prefix strictly beyond all correction modes required')
    rho=1-(arb(N)/(M+1))**2
    C3=2*sequence_bound(cutoff)*sum((n*n*abs(h[n]) for n in range(1,N+1)),arb(0))/rho
    C2=2*sum((n*abs(b[n]*h[n]) for n in range(1,N+1)),arb(0))/rho
    a=acb(z)*arb(cutoff).log()/2
    eta=1-abs(a)**2/(arb.pi()*(M+1))**2
    if not eta>0: raise ArithmeticError('Fourier target tail denominator unresolved')
    K2=arb(2).sqrt()*abs(a*a.sin())/(arb.pi()**2*eta)
    tail=C3/(5*arb(M)**5).sqrt()+(C2+K2)/(3*arb(M)**3).sqrt()
    return tail,{'endpoint_cancellation':'h0=-sqrt(2)*sum(h1,...,hN), exact algebraic identity',
                 'C3':endpoints(C3),'C2':endpoints(C2),'target_K2':endpoints(K2),
                 'tail_L2_upper':endpoints(tail)}


def select_correction(matrix,k,nu,delta):
    """Uncertified selector. Its rounded output is verified independently below."""
    import numpy as np
    M=len(matrix)-1; N=len(matrix[0])-1
    A=np.array([[float(x.mid()) for x in row] for row in matrix])
    for n in range(N+1): A[n,n]-=float(nu.mid())
    D=np.vstack([-np.sqrt(2)*np.ones(N),np.eye(N)])
    B=A@D
    rhs=np.array([complex(float(x.real.mid()),float(x.imag.mid())) for x in k])
    # Penalize the actual physical correction norm, including its constant mode.
    augmented=np.vstack([B,float(delta.upper())*D])
    target=np.concatenate([rhs,np.zeros(N+1,dtype=complex)])
    coeff,_,rank,_=np.linalg.lstsq(augmented,target,rcond=None)
    if rank!=N: raise ArithmeticError('floating selector rank deficiency')
    return [[format(x.real,'.17g'),format(x.imag,'.17g')] for x in coeff]


def certify_correction(cutoff,positive,matrix,b,z,trial,nu,delta,mean_lower):
    h=endpoint_zero_coefficients(positive); M=len(matrix)-1; N=len(h)-1
    if len(matrix[0])!=N+1 or any(len(row)!=N+1 for row in matrix):
        raise ValueError('correction and rectangular matrix dimensions mismatch')
    nu,delta,mean=map(arb,(nu,delta,mean_lower))
    if not all(x.is_finite() for x in (nu,delta,mean)) or not delta>=0 or not mean>0:
        raise ValueError('finite shift, nonnegative uncertainty, positive ground mean required')
    profile,k=target_coordinates(z,arb(cutoff).log(),trial,M)
    residual=[]
    for m,row in enumerate(matrix):
        value=sum((row[n]*h[n] for n in range(N+1)),acb(0))-k[m]
        if m<=N: value-=nu*h[m]
        residual.append(value)
    prefix_norm=l2_norm_bounds(residual)
    tail,details=full_tail(cutoff,positive,b,z,M)
    norm=l2_norm_bounds(h)
    full=(arb(prefix_norm.upper())**2+arb(tail.upper())**2).sqrt()
    uncertainty=delta*norm
    error=(full+uncertainty)/mean
    return {'exact_positive_coefficients':positive,'modes':N,'residual_prefix':M,
            'target_profile':{'real':endpoints(profile.real),'imag':endpoints(profile.imag)},
            'full_L2_residual_enclosure':{'lo':str(arb(max(0,prefix_norm.lower())).fmpq()),'hi':str(full.upper().fmpq())},
            'correction_norm':endpoints(norm),'eigenvalue_uncertainty_times_norm':endpoints(uncertainty),
            'normalized_profile_error_upper':endpoints(error),'tail_details':details}


def rectangle_cover(cutoff,matrix,b,trial,nu,delta,mean,real_cells,imag_cells):
    """The whole |Re z|<=1, |Im z|<=2/5 rectangle, using symmetry.

    Each cell has a fixed exact-decimal correction. Interval target and
    tail evaluations bound every complex frequency in that cell.
    """
    if (type(real_cells) is not int or type(imag_cells) is not int
            or real_cells<1 or imag_cells<1):
        raise ValueError('positive integer rectangle cell counts required')
    records=[]; maximum=arb(0)
    L=arb(cutoff).log(); M=len(matrix)-1
    for i in range(real_cells):
        for j in range(imag_cells):
            x0,x1=arb(i)/real_cells,arb(i+1)/real_cells
            y0,y1=arb(2)*j/(5*imag_cells),arb(2)*(j+1)/(5*imag_cells)
            center=acb((x0+x1)/2,(y0+y1)/2)
            z=acb(x0.union(x1),y0.union(y1))
            _,k=target_coordinates(center,L,trial,M)
            positive=select_correction(matrix,k,nu,delta)
            checked=certify_correction(cutoff,positive,matrix,b,z,trial,nu,delta,mean)
            upper=arb(checked['normalized_profile_error_upper']['hi'])
            maximum=arb(max(maximum.upper(),upper.upper()))
            checked['cell']=[i,j]
            records.append(checked)
    return {'region':'|Re z|<=1, |Im z|<=2/5',
            'positive_quadrant_real_cells':real_cells,'positive_quadrant_imag_cells':imag_cells,
            'symmetry':'real even ground and trial: reflection in both axes preserves error modulus',
            'normalized_profile_error_upper':endpoints(maximum),'cells':records}


def generate(directory=OUT,modes=8,prefix=64,cover_cells=None):
    directory=Path(directory); directory.mkdir(parents=True,exist_ok=True)
    base_path=OUTPUT/'full_ground_fourier.json'; base=validated_base(base_path)
    rows=[]; inputs=[]
    with ctx.workprec(384):
        for row in base['results']:
            C=row['threshold_prime']; L=arb(C).log()
            ell=arb(box(row['full_ground_lower']).lower()); upper=arb(box(row['trial_rayleigh_enclosure']).upper())
            nu=(ell+upper)/2; delta=(upper-ell)/2
            r,_=energy_distance(box(row['trial_rayleigh_enclosure']),ell,box(row['full_second_lower']))
            c=list(map(arb,row['exact_cosine_coefficients'])); m=c[0]/sum((x*x for x in c),arb(0)).sqrt()
            mean=arb(protected_mean(r,m).lower())
            matrix,b,path=matrix_inputs(C,modes,prefix,directory); inputs.append(path)
            probes=[]
            for re,im in [('0','2/5'),('1','0'),('1','2/5')]:
                z=acb(arb(re),arb(im)); _,k=target_coordinates(z,L,row['exact_cosine_coefficients'],prefix)
                positive=select_correction(matrix,k,nu,delta)
                checked=certify_correction(C,positive,matrix,b,z,row['exact_cosine_coefficients'],nu,delta,mean)
                checked['z']={'real':re,'imag':im}; probes.append(checked)
            record={'cutoff':C,'spectral_shift':endpoints(nu),'eigenvalue_uncertainty':endpoints(delta),
                    'ground_mean_lower':endpoints(mean),'probes':probes}
            if cover_cells is not None:
                record['rectangle_cover']=rectangle_cover(C,matrix,b,row['exact_cosine_coefficients'],nu,delta,mean,*cover_cells)
            rows.append(record)
            print('full adjoint residuals checked at cutoff',C,flush=True)
    sources=[Path(__file__),*[Path(__file__).with_name(n) for n in ('certified_weil.py','weil_matrix.py','full_ground_fourier.py','orthogonal_fourier_transfer.py','threshold_ground_gap.py')]]
    return {'status':'full_operator_adjoint_point_and_rectangle_certificates' if cover_cells else 'full_operator_adjoint_point_certificates','bits':384,'results':rows,
            'base_sha256':sha256(base_path),'matrix_input_sha256':{str(p):sha256(p) for p in inputs},
            'source_sha256':{str(p):sha256(p) for p in sources},
            'scope':'Written domain/form identity/self-adjointness and full-tail argument plus Arb arithmetic. Points and any explicitly recorded compact rectangle only; no whole-strip adjoint bound, Xi candidate identification, support limit or RH proof.'}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',type=Path,default=OUT)
    parser.add_argument('--modes',type=int,default=8)
    parser.add_argument('--prefix',type=int,default=64)
    parser.add_argument('--cover-cells',type=int,nargs=2)
    args=parser.parse_args()
    result=generate(args.directory,args.modes,args.prefix,args.cover_cells)
    suffix='' if args.cover_cells is None else f'_cover{args.cover_cells[0]}x{args.cover_cells[1]}'
    (args.directory/f'adjoint_N{args.modes}_M{args.prefix}{suffix}.json').write_text(json.dumps(result,indent=2)+'\n')
