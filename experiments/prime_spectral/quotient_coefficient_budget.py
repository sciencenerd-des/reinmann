"""Prime-only Taylor budgets for gated even real-zero quotient polynomials.

Uniformity in a sequence and identification with Xi are separate open tasks.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

from flint import arb, arb_mat, ctx
from certified_weil import endpoints
from quotient_operator import build


def coefficient_budget(quotient, order, radius):
    size = len(quotient)
    if not size or size % 2 or any(len(row) != size for row in quotient):
        raise ValueError('nonempty even-dimensional square quotient required')
    if type(order) is not int or not 1 <= order <= size//2:
        raise ValueError('integer Taylor order in 1..half dimension required')
    radius = arb(radius)
    if not radius.is_finite() or not radius >= 0:
        raise ValueError('finite nonnegative radius required')
    inverse = arb_mat(quotient).inv()
    square = inverse*inverse
    power = square
    sums = []
    elementary = [arb(1)]
    for k in range(1, order+1):
        sums.append(sum((power[i, i] for i in range(size)), arb(0))/2)
        elementary.append(sum(((-1)**(j-1)*elementary[k-j]*sums[j-1]
                               for j in range(1, k+1)), arb(0))/k)
        if k < order:
            power = power*square
    if not all(e.is_finite() for e in elementary) or not sums[0] > 0:
        raise ArithmeticError('finite coefficient or positive spectral sum unresolved')
    upper = arb(sums[0].upper())
    x = upper*radius**2
    tail = arb(0) if order == size//2 else x.exp()*x**(order+1)/math.factorial(order+1)
    return {'spectral_sum': sums[0], 'even_coefficients': [(-1)**k*e for k, e in enumerate(elementary)],
            'disk_tail_upper': arb(tail.upper()), 'disk_modulus_upper': arb(x.exp().upper())}


def compare(first, second, order=3, radius=1):
    data = []
    for certificate in (first, second):
        _, _, quotient, _ = build(certificate)
        data.append(coefficient_budget(quotient, order, radius))
    radius = arb(radius)
    gap = sum((abs(a-b)*radius**(2*k) for k, (a, b) in
               enumerate(zip(data[0]['even_coefficients'], data[1]['even_coefficients']))), arb(0))
    total = gap+sum((row['disk_tail_upper'] for row in data), arb(0))
    return {'schema_version': 1, 'status': 'finite_quotient_coefficient_comparison_not_convergence',
            'configurations': [{'cutoff': c['cutoff'], 'modes': c['modes']} for c in (first, second)],
            'order': order, 'radius': endpoints(radius),
            'budgets': [{'spectral_sum': endpoints(row['spectral_sum']),
                         'even_coefficients': [endpoints(x) for x in row['even_coefficients']],
                         'disk_tail_upper': str(row['disk_tail_upper'].upper().fmpq()),
                         'disk_modulus_upper': str(row['disk_modulus_upper'].upper().fmpq())} for row in data],
            'profile_difference_upper': str(total.upper().fmpq()),
            'remaining': 'No uniform spectral-sum bound or all-order coefficient convergence to Xi has been established.',
            'trust_boundary': 'Existing finite quotient gates and written real-zero proof, Newton identities and FLINT balls.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first', type=Path, required=True)
    parser.add_argument('--second', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    with ctx.workprec(512):
        certificates = []
        sources = {}
        for path in (args.first, args.second):
            certificate = json.loads(path.read_text())
            for name, digest in certificate['source_hashes'].items():
                if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() != digest:
                    raise ValueError('stale input source: '+name)
                sources[name] = digest
            certificates.append(certificate)
        result = compare(*certificates)
        for name in ('quotient_coefficient_budget.py', 'quotient_operator.py', 'certified_mode_comparison.py'):
            sources[name] = hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        result['source_hashes'] = sources
        result['input_hashes'] = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in (args.first, args.second)}
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2)+'\n')
        print(result['status'])
        print('disk difference upper:', arb(result['profile_difference_upper']))
        for row in result['budgets']:
            print('tail upper:', arb(row['disk_tail_upper']))


if __name__ == '__main__':
    main()
