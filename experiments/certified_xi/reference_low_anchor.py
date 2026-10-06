"""Point certificates for the frozen degree-16 reference outside its tail theorem.

These are direct integrals of Q_a, with the anchor held fixed. A positive
curvature at one anchor refutes an all-anchor negative-sign claim for Q_a;
it says nothing adverse about the true theta moment integral.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

from flint import acb, arb, ctx

from high_order_saddle import stirling_row
from laboratory import endpoints, sign


def frozen_moments(anchor: int, offset: int) -> list[arb]:
    """Q_a(a+offset) and its first two centered tilt derivatives.

    The common positive prefactor and exp(2*offset*log(u)) are omitted:
    both disappear from the centered second differences used below.
    """
    if not isinstance(anchor, int) or anchor < 1 or offset not in (-1, 0, 1):
        raise ValueError('integer anchor>=1 and offset in {-1,0,1} required')
    a = arb(anchor)
    u = (2*a/arb.pi()).lambertw()/2
    c = u.log()
    A = 2*a*(1+2*u)-arb(9)*u/2
    if not A > 0:
        raise ArithmeticError('nonpositive saddle scale')
    L = (32*u).sqrt()
    coefficients = [arb(0), (1+arb(9)*u/2)/A.sqrt()]
    for j in range(2, 17):
        touchard = sum((arb(v)*(2*u)**k for k, v in enumerate(stirling_row(j))), arb(0))
        coefficients.append((arb(9)*u/2-a/u*touchard)/(math.factorial(j)*A**(arb(j)/2)))

    moments = []
    for order in range(3):
        def integrand(s, _analytic):
            phase = acb(0)
            for coefficient in reversed(coefficients):
                phase = phase*s+coefficient
            centered = 2*s/A.sqrt()
            amplitude = 1-3/(2*arb.pi())*(-2*(c+s/A.sqrt()).exp()).exp()
            return (phase+offset*centered).exp()*amplitude*centered**order

        value = acb.integral(integrand, -L, L, rel_tol=arb(2)**-180,
                             abs_tol=arb(2)**-200, eval_limit=300000,
                             depth_limit=50)
        if not value.is_finite() or not value.imag.contains(0):
            raise ArithmeticError('frozen-reference quadrature unresolved')
        moments.append(value.real)
    if not moments[0] > 0:
        raise ArithmeticError('nonpositive reference mass')
    return moments


def certify_anchor(anchor: int) -> dict:
    with ctx.workprec(384):
        triple = [frozen_moments(anchor, offset) for offset in (-1, 0, 1)]
        masses = [row[0] for row in triple]
        means = [row[1]/row[0] for row in triple]
        variances = [row[2]/row[0]-(row[1]/row[0])**2 for row in triple]
        a = arb(anchor)
        q = 2*a*(2*a-1)/((2*a+2)*(2*a+1))*masses[0]*masses[2]/masses[1]**2
        if not 0 < q < 1:
            raise ArithmeticError('reference deficit unresolved')
        ell_prime = (1/a+2/(2*a-1)-2/(2*a+2)-2/(2*a+1)
                     +means[0]+means[2]-2*means[1])
        ell_second = (-1/a**2-4/(2*a-1)**2+4/(2*a+2)**2+4/(2*a+1)**2
                      +variances[0]+variances[2]-2*variances[1])
        curvature = (-1/(a+1)**2-q*ell_second/(1-q)
                     -q*ell_prime**2/(1-q)**2)
        return {
            'anchor': anchor,
            'status': f'{sign(curvature)}_reference_curvature',
            'q': endpoints(q),
            'ell_prime': endpoints(ell_prime),
            'ell_second': endpoints(ell_second),
            'log_deficit_second': endpoints(curvature),
            'centered_moments': [[endpoints(v) for v in row] for row in triple],
        }


def run() -> dict:
    return {
        'schema_version': 1,
        'status': 'low_anchor_reference_counterexample',
        'source_hashes': {
            name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
            for name in ('reference_low_anchor.py', 'high_order_saddle.py', 'laboratory.py')
        },
        'anchors': [certify_anchor(a) for a in (1, 6, 8)],
        'scope': 'Direct finite-integral point enclosures for the unchanged frozen degree-16 Q_a.',
        'trust_boundary': 'Written integral identity and python-flint 0.8.0 Arb quadrature; not Lean formalized.',
        'remaining': 'A compact true-theta sign bridge and the interior all-rank budget are still unproved.',
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print([(row['anchor'], row['status']) for row in result['anchors']])


if __name__ == '__main__':
    main()
