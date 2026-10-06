"""Prime-defined finite quotient operator and entire Fourier profile.

Real-zero conclusion uses the written exact displacement-identity proof;
interval residuals are consistency checks, not proofs of exact identities.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, acb, arb_mat, ctx
from certified_weil import endpoints, inertia
from certified_mode_comparison import normalized_vector, box


def fourier_profile(coefficients, length, z):
    if len(coefficients)%2!=1 or coefficients[len(coefficients)//2].contains(0):
        raise ValueError('odd coefficient list and nonzero central coefficient required')
    N=len(coefficients)//2
    return sum((c*(-1)**n*(arb.pi()*n-acb(z)*length/2).sinc()
                for n,c in zip(range(-N,N+1),coefficients)),acb(0))/coefficients[N]


def build(certificate):
    vector,_,_=normalized_vector(certificate)
    N=certificate['modes']
    indices=list(range(-N,N+1))
    c=[vector[abs(n)]/arb(2).sqrt() if n else vector[0] for n in indices]
    length=arb(certificate['cutoff']).log()
    omega=2*arb.pi()/length
    A=[[box(x) for x in row] for row in certificate['matrix']]
    lam=box(certificate['smallest_even_eigenvalue'])
    G=[[A[i][j]-(lam if i==j else 0) for j in range(2*N+1)] for i in range(2*N+1)]
    keep=[i for i in range(2*N+1) if i!=N]
    metric=[[G[i][j]-G[i][N]-G[N][j]+G[N][N] for j in keep] for i in keep]
    if inertia(metric)[0]!=0:
        raise ArithmeticError('positive quotient metric unresolved')
    quotient=[[omega*indices[j]*((1 if i==j else 0)-c[i]) for j in keep] for i in keep]
    b=[indices[i]*A[i][N] for i in range(2*N+1)]
    for i in range(2*N+1):
        for j in range(2*N+1):
            if i!=j and not ((indices[i]-indices[j])*A[i][j]-b[i]+b[j]).contains(0):
                raise ArithmeticError('displacement consistency failure')
    K,B=arb_mat(metric),arb_mat(quotient)
    residual=K*B-B.transpose()*K
    if not all(residual[i,j].contains(0) for i in range(2*N) for j in range(2*N)):
        raise ArithmeticError('metric adjoint consistency failure')
    return c,length,quotient,metric


def run(certificate):
    c,length,B,K=build(certificate)
    return {'schema_version':1,'status':'finite_prime_quotient_with_written_real_zero_proof',
            'cutoff':certificate['cutoff'],'modes':certificate['modes'],'dimension':len(B),
            'boundary_normalized_fourier_coefficients':[endpoints(x) for x in c],
            'quotient_operator':[[endpoints(x) for x in row] for row in B],
            'quotient_metric':[[endpoints(x) for x in row] for row in K],
            'origin_profile':endpoints(fourier_profile(c,length,0).real),
            'consistency_checks':'Displacement and metric-adjoint residuals enclose zero; exact identities are proved analytically, not inferred from these checks.',
            'claim':'This certified finite arithmetic profile has only real zeros, under the written displacement/quotient proof.',
            'remaining':'No growing-mode or support convergence to Xi; the quotient spectrum is not identified with zeta ordinates.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    with ctx.workprec(512):
        data=json.loads(args.certificate.read_text())
        for name,digest in data['source_hashes'].items():
            if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()!=digest:
                raise ValueError('stale finite-gate certificate')
        result=run(data)
        result['input_sha256']=hashlib.sha256(args.certificate.read_bytes()).hexdigest()
        result['source_hashes']={name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                 for name in ('quotient_operator.py','certified_mode_comparison.py','certified_weil.py')}
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print(result['status'],result['dimension'])


if __name__=='__main__':
    main()
