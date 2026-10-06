"""Certified smooth log-support derivative of the finite Weil matrix.

The archimedean moving-endpoint term cancels the derivative of its
analytic tail before interval evaluation. Prime-power endpoint choices
give the left or right derivative at a threshold.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx

from certified_weil import endpoints
from weil_matrix import prime_powers


def scaled_correlation(index: int, other: int, t: acb) -> acb:
    if index == other:
        return 2 * (1 - t) * (2 * arb.pi() * index * t).cos()
    first = arb.pi() * (index + other)
    second = arb.pi() * (index - other)
    return -2 * t * (first * t).cos() * (second * t).sinc()


def scaled_correlation_derivative(index: int, other: int, t: acb) -> acb:
    """Derivative in t, regular even when t contains zero."""
    if index == other:
        frequency = 2 * arb.pi() * index
        return (-2 * (frequency * t).cos()
                - 2 * (1 - t) * frequency * (frequency * t).sin())
    first = arb.pi() * (index + other)
    second = arb.pi() * (index - other)
    return (-2 * (first * t).cos() * (second * t).cos()
            + 2 * first * t * (first * t).sin() * (second * t).sinc())


def entry_derivative(index: int, other: int, length: arb,
                     powers: list[tuple[int, int]],
                     *, include_endpoint: bool) -> arb:
    if not length > 0:
        raise ValueError('positive support length required')
    tolerance = arb(2)**-240

    def pole_integrand(t: acb, _):
        argument = length * t / 2
        return ((2 * argument.cosh() + length * t * argument.sinh())
                * scaled_correlation(index, other, t))

    def arch_integrand(t: acb, _):
        argument = length * t
        sinhc = (acb(0, 1) * argument).sinc()
        return ((argument / 2).exp()
                * scaled_correlation_derivative(index, other, t)
                / (2 * length * sinhc))

    pole = acb.integral(pole_integrand, 0, 1, rel_tol=tolerance,
                        abs_tol=tolerance, eval_limit=200000)
    arch_combined = acb.integral(arch_integrand, 0, 1, rel_tol=tolerance,
                                 abs_tol=tolerance, eval_limit=200000)
    primes = acb(0)
    for power, prime in powers:
        logarithm = arb(power).log()
        if logarithm > length or (not include_endpoint and logarithm.overlaps(length)):
            continue
        if logarithm.overlaps(length) and not logarithm.contains(length):
            raise ArithmeticError('prime threshold comparison unresolved')
        weight = arb(prime).log() / arb(power).sqrt()
        primes += (weight * logarithm / length**2
                   * scaled_correlation_derivative(index, other,
                                                   acb(logarithm / length)))
    result = pole + arch_combined + primes
    if not result.is_finite() or not result.imag.contains(0):
        raise ArithmeticError('real certified Weil support derivative unresolved')
    return result.real


def even_derivative_matrix(cutoff: int, modes: int,
                           *, include_endpoint: bool) -> list[list[arb]]:
    if type(cutoff) is not int or cutoff < 2 or type(modes) is not int or not 1 <= modes <= 16:
        raise ValueError('integer cutoff at least 2 and modes 1..16 required')
    length = arb(cutoff).log()
    powers = prime_powers(cutoff)
    cache = {}

    def cell(index: int, other: int) -> arb:
        key = min((index, other), (other, index), (-index, -other), (-other, -index))
        if key not in cache:
            cache[key] = entry_derivative(*key, length, powers,
                                          include_endpoint=include_endpoint)
        return cache[key]

    result = [[arb(0) for _ in range(modes + 1)] for _ in range(modes + 1)]
    result[0][0] = cell(0, 0)
    root_two = arb(2).sqrt()
    for i in range(1, modes + 1):
        result[0][i] = result[i][0] = root_two * cell(0, i)
        for j in range(1, modes + 1):
            result[i][j] = cell(i, j) + cell(i, -j)
    return result


def certify_threshold_jump(cutoff: int, modes: int) -> dict:
    with ctx.workprec(512):
        left = even_derivative_matrix(cutoff, modes, include_endpoint=False)
        right = even_derivative_matrix(cutoff, modes, include_endpoint=True)
        powers = [(power, prime) for power, prime in prime_powers(cutoff)
                  if power == cutoff]
        if len(powers) != 1:
            raise ValueError('cutoff must be a prime-power threshold')
        power, prime = powers[0]
        exponent, value = 0, 1
        while value < power:
            exponent += 1
            value *= prime
        if value != power:
            raise ArithmeticError('prime-power exponent unresolved')
        coefficient = -2 / (arb(exponent) * arb(cutoff).sqrt())
        boundary = [arb(1)] + [arb(2).sqrt() for _ in range(modes)]
        differences = []
        for i in range(modes + 1):
            row = []
            for j in range(modes + 1):
                difference = right[i][j] - left[i][j]
                if not (difference - coefficient * boundary[i] * boundary[j]).contains(0):
                    raise ArithmeticError('prime-power derivative jump disagrees')
                row.append(endpoints(difference))
            differences.append(row)
        return {
            'status': 'certified_finite_smooth_weil_derivative_and_prime_jump',
            'cutoff': cutoff, 'modes': modes, 'prime': prime, 'exponent': exponent,
            'working_bits': 512,
            'left_even_derivative': [[endpoints(x) for x in row] for row in left],
            'right_even_derivative': [[endpoints(x) for x in row] for row in right],
            'right_minus_left': differences,
            'rank_one_coefficient': endpoints(coefficient),
            'scope': ('Differentiated finite Weil matrix at one prime-power '
                      'support; smooth pole and archimedean derivatives plus '
                      'an explicit prime contribution.'),
            'remaining': ('No support-uniform matrix derivative or ground-profile '
                          'variation bound, all-rank limit, or RH proof.'),
        }


def run(cutoff: int, modes: int) -> dict:
    result = certify_threshold_jump(cutoff, modes)
    result['source_hashes'] = {
        name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        for name in ('smooth_support_derivative.py', 'certified_weil.py', 'weil_matrix.py')
    }
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
