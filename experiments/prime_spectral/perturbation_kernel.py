"""Transfer a certified midpoint eigensystem to an interval Weil matrix.

The midpoint is only a preconditioner. Weyl and the elementary eigenspace
projection bound cover every symmetric matrix in the original entry balls.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
from flint import arb, arb_poly, ctx
from certified_weil import certified_matrix, endpoints
from isolated_kernel import isolated_spectrum


def transfer_spectrum(matrix):
    midpoint = [[arb(x.mid()) for x in row] for row in matrix]
    if any(midpoint[i][j] != midpoint[j][i] for i in range(len(matrix)) for j in range(len(matrix))):
        raise ArithmeticError('symmetric midpoint required')
    delta = max((sum((arb(x.rad()) for x in row), arb(0)).upper() for row in matrix))
    try:
        eigenvalues, vector = isolated_spectrum(midpoint)
    except ValueError as exc:
        raise ArithmeticError('midpoint eigenpair isolation unresolved') from exc
    gap = eigenvalues[1]-eigenvalues[0] if len(eigenvalues)>1 else arb(1)
    if not gap > 2*delta or not eigenvalues[0] > delta:
        raise ArithmeticError('separated positive midpoint transfer unresolved')
    norm = sum((x*x for x in vector),arb(0)).sqrt()
    if not norm > 0:
        raise ArithmeticError('nonzero midpoint eigenvector unresolved')
    unit = [x/norm for x in vector]
    eta = arb(2).sqrt()*delta/(gap-delta)
    enclosed = [(x-eta).lower() for x in unit], [(x+eta).upper() for x in unit]
    actual = [arb(lo).union(arb(hi)) for lo, hi in zip(*enclosed)]
    first = arb((eigenvalues[0]-delta).lower()).union(arb((eigenvalues[0]+delta).upper()))
    return {'first': first, 'second_lower': eigenvalues[1]-delta if len(eigenvalues)>1 else None,
            'matrix_error_upper': arb(delta), 'midpoint_gap': gap,
            'vector_error_upper': eta.upper(), 'vector': actual}


def bernstein_from_raw(vector):
    N=len(vector)-1
    if N<1:
        raise ValueError('noncentral modes required')
    root2=arb(2).sqrt()
    boundary=vector[0]+root2*sum(vector[1:],arb(0))
    if boundary.contains(0):
        raise ArithmeticError('nonzero boundary normalization unresolved')
    # Delay the division by the tiny boundary value until all large terms
    # that cancel in each Bernstein numerator have been combined.
    p=arb_poly([boundary])
    x=arb_poly([1,-2])
    prev,curr=arb_poly([1]),x
    for value in vector[1:]:
        p+=root2*value*(curr-1)
        prev,curr=curr,2*x*curr-prev
    b=[sum((p[j]*math.comb(k,j)/math.comb(N,j) for j in range(k+1)),arb(0))/boundary
       for k in range(N+1)]
    if not all(x>0 for x in b):
        raise ArithmeticError('whole-support Bernstein positivity unresolved')
    return boundary,b


def run(cutoff=31,modes=16):
    with ctx.workprec(512):
        _,even,odd=certified_matrix(cutoff,modes)
        e,o=transfer_spectrum(even),transfer_spectrum(odd)
        gap=min(e['second_lower'],o['first'])-e['first']
        if not gap>0:
            raise ArithmeticError('lowest even spectral gap unresolved')
        boundary,b=bernstein_from_raw(e['vector'])
        v=e['vector']
        if not v[0]/boundary>0:
            raise ArithmeticError('positive kernel mass unresolved')
        length=arb(cutoff).log()
        variance=length**2*(v[0]/12+sum((v[n]/(arb(2).sqrt()*arb.pi()**2*n**2)
                                         for n in range(1,modes+1)),arb(0)))/v[0]
        if not variance>0:
            raise ArithmeticError('positive variance unresolved')
        return {'schema_version':1,'status':'certified_finite_perturbation_prime_kernel_not_uniform',
                'cutoff':cutoff,'modes':modes,'working_bits':512,
                'even_first':endpoints(e['first']),'odd_first':endpoints(o['first']),
                'lowest_even_gap':endpoints(gap),
                'even_matrix_error_upper':str(e['matrix_error_upper'].upper().fmpq()),
                'odd_matrix_error_upper':str(o['matrix_error_upper'].upper().fmpq()),
                'even_vector_error_upper':str(arb(e['vector_error_upper']).upper().fmpq()),
                'raw_boundary_evaluation':endpoints(boundary),
                'bernstein_coefficients':[endpoints(x) for x in b],
                'variance':endpoints(variance),
                'claim':'This finite interval matrix has a positive simple even lowest eigenvalue, nonzero boundary, whole-support positive spatial kernel, and the existing quotient real-zero conclusion.',
                'remaining':'No uniform gate, variance estimate, or Xi theta-measure convergence.',
                'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() for name in
                                 ('perturbation_kernel.py','certified_weil.py','weil_matrix.py','isolated_kernel.py')},
                'trust_boundary':'FLINT certified midpoint eigenpairs, interval matrix entries, symmetric perturbation bounds and exact quotient/Bernstein identities; not Lean formalized.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff',type=int,default=31)
    parser.add_argument('--modes',type=int,default=16)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=run(args.cutoff,args.modes)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],result['variance'])


if __name__=='__main__':
    main()
