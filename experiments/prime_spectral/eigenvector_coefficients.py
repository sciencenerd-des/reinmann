"""Direct quotient coefficients preserving the common eigenvector denominator."""
import argparse
import hashlib
import json
import math
from pathlib import Path
from flint import arb, ctx
from certified_weil import endpoints
from quotient_operator import build
from quotient_coefficient_budget import coefficient_budget


def direct_coefficients(positive_half, length, order):
    """Even c_0,...,c_N and L give coefficients of det(zI-B)/det(-B).

The identity assumes the even quotient construction; finite real-zero
and metric gates are supplied separately by build(), not inferred here.
"""
    N = len(positive_half)-1
    if N < 1 or type(order) is not int or not 1 <= order <= N:
        raise ValueError('N>=1 and integer order in 1..N required')
    c = [arb(x) for x in positive_half]
    L = arb(length)
    if not L.is_finite() or not L > 0 or not all(x.is_finite() for x in c) or c[0].contains(0):
        raise ValueError('finite positive length and finite vector with nonzero c0 required')
    nodes = [(L/(2*arb.pi()*n))**2 for n in range(1, N+1)]
    def product(omit=None):
        p = [arb(1)]+[arb(0)]*order
        for j, node in enumerate(nodes):
            if j != omit:
                for k in range(order, 0, -1):
                    p[k] -= node*p[k-1]
        return p
    base = product()
    numerator = [c[0]*x for x in base]
    for j, node in enumerate(nodes):
        omitted = product(j)
        for k in range(1, order+1):
            numerator[k] -= 2*c[j+1]*node*omitted[k-1]
    return [arb(1)]+[x/c[0] for x in numerator[1:]]


def compare(first, second, order=3):
    rows = []
    coefficients = []
    tails = []
    for certificate in (first, second):
        c, L, B, _ = build(certificate)
        N = certificate['modes']
        direct = direct_coefficients(c[N:], L, order)
        old = coefficient_budget(B, order, 1)
        if not all(x.overlaps(y) for x, y in zip(direct, old['even_coefficients'])):
            raise ArithmeticError('direct and inverse-trace coefficient disagreement')
        S = -direct[1]
        if not S > 0:
            raise ArithmeticError('positive spectral sum unresolved')
        upper = arb(S.upper())
        tail = arb(0) if order == N else upper.exp()*upper**(order+1)/math.factorial(order+1)
        coefficients.append(direct)
        tails.append(tail)
        rows.append({'cutoff': certificate['cutoff'], 'modes': N,
                     'even_coefficients': [endpoints(x) for x in direct],
                     'spectral_sum': endpoints(S),
                     'inverse_trace_spectral_sum': endpoints(old['spectral_sum']),
                     'unit_disk_tail_upper': str(tail.upper().fmpq()),
                     'weighted_cancellation': endpoints(S*(2*arb.pi()/L)**2)})
    difference = sum((abs(x-y) for x, y in zip(*coefficients)), arb(0))+sum(tails, arb(0))
    return {'schema_version': 1, 'status': 'finite_prime_eigenvector_coefficients_not_convergence',
            'order': order, 'rows': rows, 'unit_disk_difference_upper': str(difference.upper().fmpq()),
            'remaining': 'Uniform weighted eigenvector cancellation and coefficient convergence to Xi remain unproved.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first', type=Path, required=True)
    parser.add_argument('--second', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    with ctx.workprec(512):
        certificates, sources = [], {}
        for path in (args.first, args.second):
            certificate = json.loads(path.read_text())
            for name, digest in certificate['source_hashes'].items():
                if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() != digest:
                    raise ValueError('stale certificate source: '+name)
                sources[name] = digest
            certificates.append(certificate)
        result = compare(*certificates)
        for name in ('eigenvector_coefficients.py', 'quotient_operator.py', 'quotient_coefficient_budget.py', 'certified_mode_comparison.py'):
            sources[name] = hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        result['source_hashes'] = sources
        result['input_hashes'] = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in (args.first, args.second)}
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2)+'\n')
        print(result['status'])
        print('unit disk difference upper:', arb(result['unit_disk_difference_upper']))


if __name__ == '__main__':
    main()
