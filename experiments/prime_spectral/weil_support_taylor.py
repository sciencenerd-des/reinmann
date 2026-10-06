"""Certified Taylor coefficients of a fixed prime branch of the Weil form.

A holomorphic digamma formula gives coefficients in log-support. Cauchy
bounds enclose both the omitted exponential series and the Taylor remainder.
The output retains coefficients for later cancellation-preserving products.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from math import factorial
from pathlib import Path

from flint import acb, acb_series, arb, ctx

from certified_weil import endpoints, entry
from smooth_support_derivative import entry_derivative
from weil_matrix import prime_powers


def _ball(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def _psi_series(argument: acb_series, order: int) -> acb_series:
    degree = argument.prec - 1
    increment = acb_series([0] + [argument[j] for j in range(1, degree + 1)],
                           prec=degree + 1)
    result = acb_series([], prec=degree + 1)
    for j in range(degree, -1, -1):
        coefficient = (argument[0].digamma() if j + order == 0 else
                       argument[0].polygamma(j + order)) / factorial(j)
        result = result * increment + coefficient
    return result


def _inverse(value):
    return value.inv() if isinstance(value, acb_series) else 1 / value


def _sin(value):
    if isinstance(value, acb_series):
        imaginary = acb(0, 1)
        return ((imaginary * value).exp() - (-imaginary * value).exp()) * (1 / (2 * imaginary))
    return value.sin()


def _cos(value):
    if isinstance(value, acb_series):
        imaginary = acb(0, 1)
        return ((imaginary * value).exp() + (-imaginary * value).exp()) * (arb(1) / 2)
    return value.cos()


def _psi_enclosed(argument: acb, order: int) -> acb:
    """Mean-value enclosure avoids digamma's wide-ball dependency loss."""
    midpoint = acb(argument.real.mid(), argument.imag.mid())
    value = midpoint.digamma() if order == 0 else midpoint.polygamma(order)
    derivative = argument.polygamma(order + 1)
    radius = abs(acb(arb(0, argument.real.rad()), arb(0, argument.imag.rad())))
    error = (abs(derivative) * radius).upper()
    if not value.is_finite() or not error.is_finite():
        return acb('nan')
    return value + acb(arb(0, error), arb(0, error))


def _analytic_core(index: int, other: int, length, powers, terms: int, psi):
    inverse_length = _inverse(length)
    omega = 2 * arb.pi() * index * inverse_length
    eta = 2 * arb.pi() * other * inverse_length
    cosh = ((length / 2).exp() + (-length / 2).exp()) / 2
    quarter = arb(1) / 4
    imaginary = acb(0, 1)
    if index == other:
        pole = 4 / length * (cosh - 1) * (quarter - omega**2) / (quarter + omega**2)**2
        minus, plus = quarter - imaginary * omega * (arb(1) / 2), quarter + imaginary * omega * (arb(1) / 2)
        arch = (arb.pi().log() - (psi(minus, 0) + psi(plus, 0)) / 2
                - (psi(minus, 1) + psi(plus, 1)) / (4 * length))
        for k in range(terms):
            decay = arb(2 * k) + arb(1) / 2
            arch += (2 / length * (-decay * length).exp()
                     * (decay**2 - omega**2) / (decay**2 + omega**2)**2)
    else:
        difference = arb.pi() * (index - other)
        pole = 2 * (cosh - 1) / difference * (
            omega * _inverse(quarter + omega**2) - eta * _inverse(quarter + eta**2))
        odd_first = (psi(quarter - imaginary * omega * (arb(1) / 2), 0)
                     - psi(quarter + imaginary * omega * (arb(1) / 2), 0)) * (1 / (2 * imaginary))
        odd_second = (psi(quarter - imaginary * eta * (arb(1) / 2), 0)
                      - psi(quarter + imaginary * eta * (arb(1) / 2), 0)) * (1 / (2 * imaginary))
        arch = (odd_first - odd_second) / (2 * difference)
        for k in range(terms):
            decay = arb(2 * k) + arb(1) / 2
            arch += (-decay * length).exp() / difference * (
                omega * _inverse(decay**2 + omega**2) - eta * _inverse(decay**2 + eta**2))
    primes = 0 * length
    for power, prime in powers:
        ratio = arb(power).log() / length
        if index == other:
            correlation = 2 * (1 - ratio) * _cos(2 * arb.pi() * index * ratio)
        else:
            correlation = -(_sin(2 * arb.pi() * index * ratio)
                            - _sin(2 * arb.pi() * other * ratio)) / (arb.pi() * (index - other))
        primes += arb(prime).log() / arb(power).sqrt() * correlation
    return pole - arch - primes


def analytic_tail_bound(center: arb, radius: Fraction, terms: int) -> arb:
    """Uniform in every integer index pair on |L-center|<=radius."""
    if not center > _ball(radius) or radius <= 0 or type(terms) is not int or terms < 1:
        raise ValueError('disk in the right half-plane and positive tail length required')
    minimum_real = (center - _ball(radius)).lower()
    maximum_modulus = (abs(center) + _ball(radius)).upper()
    first = arb(2 * terms) + arb(1) / 2
    return (2 * maximum_modulus * (-first * minimum_real).exp()
            / (minimum_real**2 * first**2 * (1 - (-2 * minimum_real).exp())))


def entry_taylor(index: int, other: int, center: arb,
                 powers: list[tuple[int, int]], degree: int,
                 radius: Fraction, terms: int = 80) -> tuple[list[arb], arb]:
    if type(degree) is not int or degree < 1:
        raise ValueError('positive Taylor degree required')
    tail = analytic_tail_bound(center, radius, terms)
    # Cover the entire Cauchy circle by arc rectangles. A single large
    # rectangle loses the separation of the digamma arguments from poles.
    analytic_bound = None
    for segments in (32, 64, 128):
        arc_bounds = []
        for k in range(segments):
            angle = (2 * arb.pi() * k / segments).union(2 * arb.pi() * (k + 1) / segments)
            length_box = acb(center + _ball(radius) * angle.cos(), _ball(radius) * angle.sin())
            value = abs(_analytic_core(index, other, length_box, powers, terms, _psi_enclosed))
            if not value.is_finite():
                break
            arc_bounds.append(value.upper())
        if len(arc_bounds) == segments:
            analytic_bound = max(arc_bounds) + tail
            break
    if analytic_bound is None or not analytic_bound.is_finite():
        raise ArithmeticError('finite holomorphic Cauchy bound unresolved')
    saved_cap = ctx.cap
    try:
        ctx.cap = degree + 1
        length = acb_series([acb(center), 1], prec=degree + 1)
        polynomial = _analytic_core(index, other, length, powers, terms, _psi_series)
        coefficients = []
        for j in range(degree + 1):
            coefficient = polynomial[j]
            if not coefficient.is_finite() or not coefficient.imag.contains(0):
                raise ArithmeticError('real finite Taylor coefficient unresolved')
            coefficients.append(coefficient.real + arb(0, (tail / _ball(radius)**j).upper()))
    finally:
        ctx.cap = saved_cap
    return coefficients, analytic_bound.upper()


def remainder_bound(bound: arb, radius: Fraction, half_width: Fraction,
                    degree: int, derivative: bool = False) -> arb:
    if radius <= 0 or not 0 <= half_width < radius or type(degree) is not int or degree < 1:
        raise ValueError('Taylor cell must lie strictly within its analytic disk')
    ratio = _ball(half_width / radius)
    if derivative:
        return (bound / _ball(radius) * ratio**degree
                * ((degree + 1) - degree * ratio) / (1 - ratio)**2)
    return bound * ratio**(degree + 1) / (1 - ratio)


def evaluate(coefficients: list[arb], displacement: arb) -> arb:
    result = arb(0)
    for coefficient in reversed(coefficients):
        result = result * displacement + coefficient
    return result


def certify(cutoff: int = 18, modes: int = 8, degree: int = 48) -> dict:
    if type(cutoff) is not int or cutoff < 3 or type(modes) is not int or modes < 1:
        raise ValueError('integer anchor >=3 and positive Fourier rank required')
    radius, terms = Fraction(1, 4), 80
    with ctx.workprec(1024):
        all_powers = prime_powers(2 * cutoff)
        lower_cutoff = max(power for power, _ in all_powers if power < cutoff)
        upper_cutoff = min(power for power, _ in all_powers if power >= cutoff)
        lower, upper = arb(lower_cutoff).log(), arb(upper_cutoff).log()
        center = (lower + upper) / 2
        half_width = Fraction(str(((upper - lower) / 2).upper().fmpq()))
        if not half_width < radius:
            raise ValueError('whole prime-power cell exceeds the analytic disk')
        powers = [(power, prime) for power, prime in all_powers if power <= lower_cutoff]
        cache = {}

        def scalar(index, other):
            key = min((index, other), (other, index), (-index, -other), (-other, -index))
            if key not in cache:
                cache[key] = entry_taylor(*key, center, powers, degree, radius, terms)
            return cache[key]

        comparisons = []
        for index, other in ((0, 0), (0, modes), (modes, modes),
                             (modes, -modes), (modes, modes - 1)):
            coefficients, bound = scalar(index, other)
            derivative = entry_derivative(index, other, center, powers, include_endpoint=True)
            if not coefficients[1].overlaps(derivative):
                raise ArithmeticError('Taylor derivative and differentiated integral disagree')
            remainder = remainder_bound(bound, radius, half_width, degree)
            derivative_remainder = remainder_bound(bound, radius, half_width, degree, True)
            values = []
            for label, displacement in (('lower_endpoint', lower - center),
                                        ('center', arb(0)), ('upper_endpoint', upper - center)):
                value = evaluate(coefficients, displacement) + arb(0, remainder.upper())
                original = entry(index, other, center + displacement, powers, 0)
                if not value.overlaps(original):
                    raise ArithmeticError('Taylor cell enclosure disagrees with original integral')
                values.append({'location': label, 'taylor': endpoints(value),
                               'original_integral': endpoints(original)})
            comparisons.append({'indices': [index, other],
                                'coefficients': [endpoints(x) for x in coefficients],
                                'cauchy_entry_bound': str(bound.fmpq()),
                                'whole_cell_value_remainder_upper': str(remainder.upper().fmpq()),
                                'whole_cell_derivative_remainder_upper': str(derivative_remainder.upper().fmpq()),
                                'integral_derivative': endpoints(derivative),
                                'point_comparisons': values})
        matrices = [[[arb(0) for _ in range(modes + 1)] for _ in range(modes + 1)]
                    for _ in range(degree + 1)]
        bounds = [[arb(0) for _ in range(modes + 1)] for _ in range(modes + 1)]
        for i in range(modes + 1):
            for j in range(i, modes + 1):
                if i == 0:
                    cells, bound = scalar(0, j)
                    scale = arb(1) if j == 0 else arb(2).sqrt()
                    cells, bound = [scale * x for x in cells], scale * bound
                else:
                    first, first_bound = scalar(i, j)
                    second, second_bound = scalar(i, -j)
                    cells = [a + b for a, b in zip(first, second)]
                    bound = first_bound + second_bound
                for k, coefficient in enumerate(cells):
                    matrices[k][i][j] = matrices[k][j][i] = coefficient
                bounds[i][j] = bounds[j][i] = bound
        value_errors = [[remainder_bound(x, radius, half_width, degree) for x in row]
                        for row in bounds]
        derivative_errors = [[remainder_bound(x, radius, half_width, degree, True) for x in row]
                             for row in bounds]
        value_norm = max(sum(row, arb(0)).upper() for row in value_errors)
        derivative_norm = max(sum(row, arb(0)).upper() for row in derivative_errors)
        return {
            'status': 'certified_weil_entry_taylor_cell_not_ground_profile_budget',
            'cutoff_anchor': cutoff, 'modes': modes, 'degree': degree,
            'lower_prime_power': lower_cutoff, 'upper_prime_power': upper_cutoff,
            'working_bits': 1024, 'analytic_radius': str(radius),
            'cell_half_width': str(half_width), 'log_support_center': endpoints(center),
            'tail_terms': terms, 'active_prime_powers': [list(pair) for pair in powers],
            'uniform_complex_arch_tail_upper': str(analytic_tail_bound(center, radius, terms).upper().fmpq()),
            'even_matrix_coefficients': [
                [[endpoints(x) for x in row] for row in matrix] for matrix in matrices],
            'even_value_remainder_upper': [[str(x.upper().fmpq()) for x in row] for row in value_errors],
            'even_derivative_remainder_upper': [[str(x.upper().fmpq()) for x in row] for row in derivative_errors],
            'even_value_operator_remainder_upper': str(value_norm.fmpq()),
            'even_derivative_operator_remainder_upper': str(derivative_norm.fmpq()),
            'entries': comparisons,
            'scope': ('Certified full even-block Taylor coefficients and analytic '
                      'operator remainders over one whole prime-power support cell.'),
            'remaining': ('A validated ground-eigenpair family, integrated profile '
                          'budget across all cells and ranks, Xi convergence, and RH.'),
        }


def run(cutoff: int = 18, modes: int = 8, degree: int = 48) -> dict:
    result = certify(cutoff, modes, degree)
    result['source_hashes'] = {
        name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        for name in ('weil_support_taylor.py', 'certified_weil.py',
                     'smooth_support_derivative.py', 'weil_matrix.py')}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff', type=int, default=18)
    parser.add_argument('--modes', type=int, default=8)
    parser.add_argument('--degree', type=int, default=48)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.cutoff, args.modes, args.degree)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
