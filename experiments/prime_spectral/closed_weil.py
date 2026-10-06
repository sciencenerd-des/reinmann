"""Closed finite Weil entries with a rank-independent exponential tail bound.

The archimedean regularization is evaluated as digamma/trigamma terms
plus a rapidly convergent series. The original certified integral remains
an independent reference implementation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx

from certified_weil import correlation_ball, endpoints, entry
from weil_matrix import prime_powers


def tail_bound(length: arb, terms: int) -> arb:
    """Absolute omitted archimedean tail, uniformly for all integer indices."""
    if not length > 0 or type(terms) is not int or terms < 1:
        raise ValueError('positive length and positive integer tail length required')
    first = arb(2 * terms) + arb(1) / 2
    return 2 * (-first * length).exp() / (
        length * first**2 * (1 - (-2 * length).exp()))


def _psi(index: int, length: arb) -> acb:
    return acb(arb(1) / 4, -arb.pi() * index / length).digamma()


def entry_closed(index: int, other: int, length: arb,
                 powers: list[tuple[int, int]], terms: int = 40) -> arb:
    """Entry for a fixed set of active prime powers; no threshold inference."""
    error = tail_bound(length, terms)
    omega = 2 * arb.pi() * index / length
    eta = 2 * arb.pi() * other / length
    if index == other:
        rational = (arb(1) / 4 - omega**2) / (arb(1) / 4 + omega**2)**2
        pole = 4 / length * ((length / 2).cosh() - 1) * rational
        argument = acb(arb(1) / 4, -omega / 2)
        arch = (arb.pi().log() - argument.digamma().real
                - argument.polygamma(1).real / (2 * length))
        for k in range(terms):
            decay = arb(2 * k) + arb(1) / 2
            arch += (2 / length * (-decay * length).exp()
                     * (decay**2 - omega**2) / (decay**2 + omega**2)**2)
    else:
        difference = arb.pi() * (index - other)
        pole = (2 * (length / 2).cosh() - 2) / difference * (
            omega / (arb(1) / 4 + omega**2)
            - eta / (arb(1) / 4 + eta**2))
        arch = (_psi(index, length).imag - _psi(other, length).imag) / (2 * difference)
        for k in range(terms):
            decay = arb(2 * k) + arb(1) / 2
            arch += (-decay * length).exp() / difference * (
                omega / (decay**2 + omega**2) - eta / (decay**2 + eta**2))
    primes = arb(0)
    for power, prime in powers:
        logarithm = arb(power).log()
        if logarithm > length:
            raise ValueError('inactive prime power supplied to closed Weil entry')
        value = correlation_ball(index, other, acb(logarithm), length)
        if not value.imag.contains(0):
            raise ArithmeticError('real prime correlation unresolved')
        primes += arb(prime).log() / arb(power).sqrt() * value.real
    result = pole - arch - primes + arb(0, error.upper())
    if not result.is_finite():
        raise ArithmeticError('closed Weil entry unresolved')
    return result


def certify(cutoff: int, modes: int, terms: int = 40) -> dict:
    if type(cutoff) is not int or cutoff < 2 or type(modes) is not int or modes < 1:
        raise ValueError('integer cutoff >=2 and positive rank required')
    with ctx.workprec(512):
        length = arb(cutoff).log()
        powers = [(power, prime) for power, prime in prime_powers(cutoff)
                  if power < cutoff]
        error = tail_bound(length, terms)
        comparisons = []
        for index, other in ((0, 0), (0, modes), (modes, modes),
                             (modes, -modes), (modes, modes - 1)):
            closed = entry_closed(index, other, length, powers, terms)
            integral = entry(index, other, length, powers, cutoff)
            if not closed.overlaps(integral):
                raise ArithmeticError('closed formula and original integral disagree')
            comparisons.append({'indices': [index, other],
                                'closed': endpoints(closed),
                                'original_integral': endpoints(integral)})
        return {
            'status': 'certified_closed_weil_entry_comparison_with_uniform_arch_tail',
            'cutoff': cutoff, 'modes': modes, 'tail_terms': terms,
            'working_bits': 512,
            'rank_independent_entry_tail_upper': str(error.upper().fmpq()),
            'full_fourier_operator_tail_upper': str(((2 * modes + 1) * error).upper().fmpq()),
            'comparisons': comparisons,
            'scope': ('Closed entry identity and archimedean tail bound uniform '
                      'in integer Fourier indices; comparison at the listed finite entries.'),
            'remaining': ('No uniform ground-profile derivative budget, infinite-rank '
                          'spectral convergence, theta estimate, or RH proof.'),
        }


def run(cutoff: int, modes: int, terms: int = 40) -> dict:
    result = certify(cutoff, modes, terms)
    result['source_hashes'] = {
        name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        for name in ('closed_weil.py', 'certified_weil.py', 'weil_matrix.py')}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff', type=int, required=True)
    parser.add_argument('--modes', type=int, required=True)
    parser.add_argument('--terms', type=int, default=40)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.cutoff, args.modes, args.terms)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
