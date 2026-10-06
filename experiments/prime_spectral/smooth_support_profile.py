"""Finite one-sided derivative of the origin-normalized Weil ground profile.

This differentiates the coupled eigenvalue equation in the moving even
Fourier coordinates. It certifies only one support and one Fourier rank.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, arb_mat, ctx

from certified_weil import certified_matrix, endpoints, inertia
from eigenvalue_response import _fourier_functional
from isolated_kernel import isolated_spectrum
from smooth_support_derivative import even_derivative_matrix
from support_schur_recurrence import _spectral_solve
from weil_matrix import prime_powers


def _dot(left: list[arb], right: list[arb]) -> arb:
    return sum((a * b for a, b in zip(left, right)), arb(0))


def _sinc_prime(argument: acb) -> acb:
    if argument.contains(0):
        raise ArithmeticError('sinc derivative needs removable-value evaluation')
    return (argument.cos() - argument.sinc()) / argument


def _fourier_length_derivative(modes: int, length: arb, z: acb) -> list[arb]:
    frequency = -z / 2
    terms = [frequency * _sinc_prime(frequency * length)]
    for index in range(1, modes + 1):
        term = ((-1)**index * frequency / arb(2).sqrt()
                * (_sinc_prime(arb.pi() * index + frequency * length)
                   + _sinc_prime(-arb.pi() * index + frequency * length)))
        terms.append(term)
    if any(not value.imag.contains(0) for value in terms):
        raise ArithmeticError('real Fourier length derivative unresolved')
    return [value.real for value in terms]


def certify(cutoff: int, modes: int) -> dict:
    with ctx.workprec(512):
        _, matrix, _ = certified_matrix(cutoff, modes)
        values, raw = isolated_spectrum(matrix)
        if raw[0].contains(0):
            raise ArithmeticError('ground origin unresolved')
        ground = [arb(1)] + [value / raw[0] for value in raw[1:]]
        norm_squared = _dot(ground, ground)
        eigenvalue = values[0]
        constrained = [[matrix[i][j] - (eigenvalue if i == j else 0)
                        for j in range(1, modes + 1)] for i in range(1, modes + 1)]
        if inertia(constrained)[0] != 0:
            raise ArithmeticError('positive origin-constrained block unresolved')
        operator = arb_mat(constrained)
        length = arb(cutoff).log()
        arguments = {'real_4': acb(4), 'real_8': acb(8), 'imag_1': acb(0, 1)}
        functionals = {name: _fourier_functional(modes, length, z)
                       for name, z in arguments.items()}
        drifts = {name: _fourier_length_derivative(modes, length, z)
                  for name, z in arguments.items()}
        sides = {}
        derivatives = {}
        for name, include_endpoint in (('left', False), ('right', True)):
            matrix_prime = even_derivative_matrix(
                cutoff, modes, include_endpoint=include_endpoint)
            eigenvalue_prime = sum(
                (ground[i] * matrix_prime[i][j] * ground[j]
                 for i in range(modes + 1) for j in range(modes + 1)), arb(0)) / norm_squared
            source = [sum((matrix_prime[i][j] * ground[j]
                           for j in range(modes + 1)), arb(0))
                      - eigenvalue_prime * ground[i]
                      for i in range(1, modes + 1)]
            solved, constrained_lowest = _spectral_solve(operator, source)
            ground_prime = [-value for value in solved]
            profile = {}
            for label, functional in functionals.items():
                basis_drift = _dot(drifts[label], ground)
                ground_response = _dot(functional[1:], ground_prime)
                profile[label] = {
                    'basis_length_drift': endpoints(basis_drift),
                    'ground_response': endpoints(ground_response),
                    'total': endpoints(basis_drift + ground_response),
                }
            sides[name] = {
                'lowest_eigenvalue_derivative': endpoints(eigenvalue_prime),
                'ground_coefficient_derivative': [endpoints(x) for x in ground_prime],
                'profile_derivative': profile,
            }
            derivatives[name] = (eigenvalue_prime, ground_prime, profile)
        left, right = derivatives['left'], derivatives['right']
        boundary = ground[0] + arb(2).sqrt() * sum(ground[1:], arb(0))
        prime = next((p for power, p in prime_powers(cutoff)
                      if power == cutoff), None)
        if prime is None:
            raise ValueError('prime-power threshold required')
        exponent, value = 0, 1
        while value < cutoff:
            exponent += 1
            value *= prime
        if value != cutoff:
            raise ArithmeticError('prime-power exponent unresolved')
        jump = -2 / (arb(exponent) * arb(cutoff).sqrt()) * boundary**2 / norm_squared
        if not (right[0] - left[0] - jump).contains(0):
            raise ArithmeticError('ground eigenvalue derivative jump disagrees')
        return {
            'status': 'certified_finite_one_sided_ground_profile_derivative_not_uniform',
            'cutoff': cutoff, 'modes': modes, 'working_bits': 512,
            'origin_normalized_ground': [endpoints(x) for x in ground],
            'origin_constrained_lowest_eigenvalue': endpoints(constrained_lowest),
            'sides': sides,
            'lowest_eigenvalue_derivative_jump': endpoints(right[0] - left[0]),
            'rank_one_jump_prediction': endpoints(jump),
            'ground_coefficient_derivative_jump': [
                endpoints(a - b) for a, b in zip(right[1], left[1])],
            'profile_derivative_jump': {
                label: endpoints(
                    _dot(functionals[label][1:],
                         [a - b for a, b in zip(right[1], left[1])]))
                for label in arguments},
            'scope': 'One prime-power threshold and one finite even Fourier rank.',
            'remaining': ('No interior support integral, uniform spectral-gap budget, '
                          'joint support/rank limit, or RH proof.'),
        }


def run(cutoff: int, modes: int) -> dict:
    result = certify(cutoff, modes)
    source_dir = Path(__file__).parent
    result['source_hashes'] = {
        name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
        for name in ('smooth_support_profile.py', 'smooth_support_derivative.py',
                     'certified_weil.py', 'isolated_kernel.py', 'weil_matrix.py',
                     'eigenvalue_response.py', 'rank_schur_recurrence.py',
                     'support_schur_recurrence.py')}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff', type=int, required=True)
    parser.add_argument('--modes', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.cutoff, args.modes)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['cutoff'], result['modes'])


if __name__ == '__main__':
    main()
