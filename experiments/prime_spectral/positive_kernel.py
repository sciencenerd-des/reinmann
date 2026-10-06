"""Finite Bernstein positivity gate for prime-defined spatial kernels."""
import argparse
import hashlib
import json
import math
from pathlib import Path
from flint import arb, arb_poly, ctx
from certified_weil import endpoints
from quotient_operator import build


def bernstein_coefficients(noncentral):
    """g(t)=1+2 sum c_n*(T_n(1-2u)-1), u=(1+cos(2*pi*t/L))/2.

The expression uses the exact boundary normalization c0+2 sum c_n=1.
"""
    if not noncentral:
        raise ValueError('at least one noncentral mode required')
    c = [arb(x) for x in noncentral]
    if not all(x.is_finite() for x in c):
        raise ValueError('finite coefficients required')
    x = arb_poly([1, -2])
    previous, current = arb_poly([1]), x
    polynomial = arb_poly([1])
    for value in c:
        polynomial += 2*value*(current-1)
        previous, current = current, 2*x*current-previous
    N = len(c)
    return [sum((polynomial[j]*math.comb(k,j)/math.comb(N,j)
                 for j in range(k+1)), arb(0)) for k in range(N+1)]


def run(certificate):
    c, L, _, _ = build(certificate)
    N = certificate['modes']
    positive_half = c[N:]
    # Here u=(1+cos(2*pi*t/L))/2, so T_n(1-2u)=(-1)^n*cos(2*pi*n*t/L).
    coefficients = bernstein_coefficients(positive_half[1:])
    if not positive_half[0] > 0 or not all(x > 0 for x in coefficients):
        raise ArithmeticError('positive spatial kernel unresolved')
    moment = L**2*(positive_half[0]/12
                  +sum((positive_half[n]/n**2 for n in range(1,N+1)),arb(0))/arb.pi()**2)/positive_half[0]
    if not moment > 0:
        raise ArithmeticError('positive normalized variance unresolved')
    return {'schema_version': 1, 'status': 'certified_finite_positive_prime_spatial_kernel',
            'cutoff': certificate['cutoff'], 'modes': N,
            'bernstein_coefficients': [endpoints(x) for x in coefficients],
            'boundary_value': '1 exactly from boundary normalization',
            'normalizing_mass': endpoints(L*positive_half[0]),
            'variance': endpoints(moment),
            'claim': 'g(t)>0 for all |t|<=L/2; g(t)/(L*c0) is an even probability density whose characteristic function is the existing Fourier profile.',
            'remaining': 'Positivity and bounded variance along an infinite support/mode path and weak convergence to the Xi theta measure are not proved.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    with ctx.workprec(512):
        certificate=json.loads(args.certificate.read_text())
        sources=dict(certificate['source_hashes'])
        for name,digest in sources.items():
            if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()!=digest:
                raise ValueError('stale source: '+name)
        result=run(certificate)
        for name in ('positive_kernel.py','quotient_operator.py','certified_mode_comparison.py'):
            sources[name]=hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        result['source_hashes']=sources
        result['input_sha256']=hashlib.sha256(args.certificate.read_bytes()).hexdigest()
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print(result['status'],result['modes'])
        print('variance:', arb(result['variance']['lo']).union(arb(result['variance']['hi'])))


if __name__=='__main__':
    main()
