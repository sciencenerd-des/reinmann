"""Full-window lower certificate, including the infinite polynomial complement.

See research/prime_spectral/WINDOW_POSITIVITY_PROOF_2026_10_07.md.
The defaults certify support [-3/5,3/5], C=exp(6/5), with primes 2 and 3.
No zero data, numerical eigensolver, or finite-minor scan is used.
This generator is separate from the independently developed window_positivity_certificate.py.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import time
from pathlib import Path

from flint import acb, arb, arb_mat, ctx

from certified_weil import endpoints, inertia
from weil_matrix import prime_powers


def fourier_legendre(t, half_width, count):
    """Real amplitudes F_n(t)/i^n, with normalized Legendre functions."""
    z = half_width * t
    factor = arb(1)
    values = []
    for n in range(count):
        values.append((2 * half_width * (2*n+1)).sqrt() * factor
                      * (-z*z/4).hypgeom_0f1(arb(n) + arb(3)/2))
        factor *= z / (2*n+3)
    return values


def pole_legendre(half_width, count):
    """Cosh coefficients for even n and sinh coefficients for odd n."""
    z = half_width / 2
    factor = arb(1)
    values = []
    for n in range(count):
        values.append((2 * half_width * (2*n+1)).sqrt() * factor
                      * (z*z/4).hypgeom_0f1(arb(n) + arb(3)/2))
        factor *= z / (2*n+3)
    return values


def symbol(t, powers):
    z = acb(arb(1)/4, t/2)
    return z.digamma().real - arb.pi().log() - sum(
        (2*arb(p).log()/arb(q).sqrt() * (t*arb(q).log()).cos()
         for q, p in powers), arb(0))


def bounds(a, cutoff, count, order, powers):
    """All constants enclose analytic operator bounds, not sampled errors."""
    mass = sum((2*arb(p).log()/arb(q).sqrt() for q, p in powers), arb(0))
    beta = (cutoff/(2*arb.pi())).log() - 1/arb(cutoff) - mass
    if not beta > 0 or cutoff < 4:
        raise ValueError('positive high-frequency envelope required')
    # Unit-panel Bernstein ellipse rho=2: |Im t| <= 3/8.
    zmax = arb(1) + (cutoff+2)/arb(2)
    psi_bound = 17 + 2*zmax
    h = psi_bound + arb.pi().log() + mass*(arb(3)/8 * (2*a)).cosh() + abs(beta)
    kernel_bound = 2*a * (3*a/4).exp() * h
    quadrature = 4*cutoff*kernel_bound*arb(2)**(1-2*order)/arb.pi()
    r = (2*a).sqrt() * (a*cutoff)**count / math.factorial(count)
    p = (2*a).sqrt() * (a/2).exp()
    rp = p * (a/2)**count / math.factorial(count)
    coupling = cutoff*h/arb.pi() * (2*a).sqrt()*r + 4*p*rp
    tail_deviation = cutoff*h/arb.pi()*r*r + 4*rp*rp
    return beta, quadrature, coupling, tail_deviation, h


def certify(half_width='3/5', cutoff=64, count=160, order=80,
            bits=384, finite_lower='1e-12', block_method='linear'):
    if (type(cutoff) is not int or cutoff < 4 or type(count) is not int
            or count < 2 or count % 2 or type(order) is not int or order < 2
            or type(bits) is not int or bits < 128):
        raise ValueError('integer cutoff >=4, even count >=2, order >=2, bits >=128 required')
    with ctx.workprec(bits):
        if block_method not in ('linear', 'schur'):
            raise ValueError('unknown block method')
        started = time.monotonic()
        a = arb(half_width)
        if not 0 < a <= 1:
            raise ValueError('half width must be a positive rational <= 1')
        c = (2*a).exp()
        top = int(c.ceil().fmpq())
        powers = []
        for q, p in prime_powers(top):
            if arb(q).log() < 2*a:
                powers.append((q, p))
            elif not arb(q).log() >= 2*a:
                raise ArithmeticError('prime threshold unresolved')
        beta, quadrature, coupling, tail_dev, h = bounds(a, cutoff, count, order, powers)
        size = count//2
        matrices = [arb_mat(size, size), arb_mat(size, size)]
        nodes = [arb.legendre_p_root(order, k, weight=True) for k in range(order)]
        for panel in range(cutoff):
            amplitudes, weights = [], []
            for x, w in nodes:
                t = arb(panel) + (x+1)/2
                amplitudes.append(fourier_legendre(t, a, count))
                weights.append(w/2 * (symbol(t, powers)-beta)/arb.pi())
            for parity in (0, 1):
                v = arb_mat([[row[2*j+parity] * (-1)**j for row in amplitudes]
                             for j in range(size)])
                weighted = arb_mat([[v[j,k]*weights[k] for k in range(order)]
                                    for j in range(size)])
                matrices[parity] += weighted*v.transpose()
            if panel % 8 == 7:
                print(f'assembled {panel+1}/{cutoff} panels', flush=True)
        poles = pole_legendre(a, count)
        lower = arb(finite_lower)
        if not lower > 0:
            raise ValueError('positive proposed finite lower bound required')
        sectors = []
        for parity in (0, 1):
            for i in range(size):
                for j in range(size):
                    matrices[parity][i,j] += 2*(-1)**parity*poles[2*i+parity]*poles[2*j+parity]
                    if i == j:
                        matrices[parity][i,j] += beta
            negative, pivots = inertia(matrices[parity].tolist(), lower+quadrature)
            if negative or not all(p > 0 for p in pivots):
                raise ArithmeticError(f'finite shifted {parity=} block failed positivity: {negative=}')
            sectors.append({'parity': 'odd' if parity else 'even',
                            'dimension': size,
                            'shifted_ldl_pivots': [endpoints(x) for x in pivots],
                            'quadrature_matrix': [[endpoints(x) for x in row]
                                                  for row in matrices[parity].tolist()]})
        schur_target = arb('9.5e-13')
        determinant = (lower-schur_target)*(beta-tail_dev-schur_target)-coupling**2
        if block_method == 'schur':
            if not lower > schur_target or not determinant > 0:
                raise ArithmeticError('Schur determinant allowance did not close')
            full_lower = schur_target
        else:
            full_lower = lower.min(beta-tail_dev)-coupling
        if not full_lower > 0:
            raise ArithmeticError('infinite complement/coupling allowance did not close')
        return {'status': 'certified_full_window_lower_bound',
                'half_width': half_width, 'C': endpoints(c),
                'active_prime_powers': powers, 'cutoff': cutoff, 'polynomial_count': count,
                'gauss_order': order, 'bits': bits, 'finite_lower': finite_lower,
                'block_method': block_method,
                'schur_target': '9.5e-13', 'schur_determinant': endpoints(determinant),
                'beta': endpoints(beta), 'symbol_ellipse_absolute_bound': endpoints(h),
                'quadrature_operator_error': endpoints(quadrature),
                'infinite_coupling_bound': endpoints(coupling),
                'infinite_tail_deviation': endpoints(tail_dev),
                'full_lower_bound': endpoints(full_lower), 'sectors': sectors,
                'seconds': round(time.monotonic()-started, 3),
                'trust_boundary': 'Written analytic reduction plus FLINT/Arb; not Lean or independent review.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--half-width', default='3/5')
    parser.add_argument('--cutoff', type=int, default=64)
    parser.add_argument('--count', type=int, default=160)
    parser.add_argument('--order', type=int, default=80)
    parser.add_argument('--bits', type=int, default=384)
    parser.add_argument('--finite-lower', default='1e-12')
    parser.add_argument('--block-method', choices=['linear', 'schur'], default='linear')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = certify(args.half_width, args.cutoff, args.count, args.order,
                     args.bits, args.finite_lower, args.block_method)
    source = Path(__file__).resolve()
    result['source_hashes'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in (source, source.with_name('certified_weil.py'),
                                         source.with_name('weil_matrix.py'))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], arb(result['full_lower_bound']['lo']).str(12))


if __name__ == '__main__':
    main()
