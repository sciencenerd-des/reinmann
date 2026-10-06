"""Coupled infinite Fourier-tail forcing and high-mode Weil coercivity.

The full 17--19 support-cell ground enclosure supplies common signed
moments. A geometric expansion bounds all omitted modes, not a sampled
rank range. Coercivity concerns only the high-mode compression.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from flint import arb, arb_poly, ctx
from certified_weil import endpoints
from weil_eigenfamily import ball, box, polynomial_bound
from weil_odd_cell import validate_partition
from weil_profile_cell_budget import physical_candidate, polynomial_range


def global_constants(lower, upper, powers):
    lo, hi = lower.lower(), upper.upper()
    if not lo > 0 or not hi >= lo:
        raise ValueError('ordered positive support lengths required')
    exponential_sum = ((-lo / 2).exp() / (1 - (-2 * lo).exp())).upper()
    prime_sum = sum((arb(prime).log() / arb(power).sqrt() for power, prime in powers), arb(0)).upper()
    digamma_imag = (arb.pi() / 2 + arb(2).min(hi / arb.pi())).upper()
    pole_b = (2 * ((hi / 2).cosh() - 1) / arb.pi()).upper()
    arch_b = (digamma_imag / (2 * arb.pi()) + exponential_sum / arb.pi()).upper()
    prime_b = (prime_sum / arb.pi()).upper()
    b = (pole_b + arch_b + prime_b).upper()
    # For n>=1, |b_n| <= b0+b1/n by the same exact closed formula.
    b0 = (arb(1) / 4 + prime_b).upper()
    b1 = (hi * ((hi / 2).cosh() - 1 + (1 + exponential_sum) / 2) / arb.pi()**2).upper()
    return {'length_upper': hi, 'exponential_sum': exponential_sum, 'prime_sum': prime_sum,
            'arch_off_diagonal_norm': (2 * arb.pi() * arch_b).upper(),
            'full_off_diagonal_norm': (2 * arb.pi() * b).upper(),
            'negative_pole_norm': (2 * (hi / 2).sinh() - hi).upper(),
            'b': b, 'b0': b0, 'b1': b1}


def high_mode_lower(constants, first_index, even=False):
    if type(first_index) is not int or first_index < 1:
        raise ValueError('positive first Fourier index required')
    n = arb(first_index)
    length = constants['length_upper']
    exponential = constants['exponential_sum']
    diagonal = ((n / length).log() - length / (arb.pi() * n) - 1 / (4 * n)
                - length * (1 + exponential) / (2 * arb.pi()**2 * n * n))
    return (diagonal - constants['arch_off_diagonal_norm'] - 2 * constants['prime_sum']
            - (arb(0) if even else constants['negative_pole_norm'])).lower()


def coercive_start(constants, even=False):
    high = 1
    while not high_mode_lower(constants, high, even) > 1:
        high *= 2
    low = high // 2
    while high - low > 1:
        middle = (low + high) // 2
        if high_mode_lower(constants, middle, even) > 1:
            high = middle
        else:
            low = middle
    return high


def power_tail_l2(cutoff, power):
    # Integral test: sum_(j>J) j^(-2p) <= J^(1-2p)/(2p-1).
    return (1 / (arb(2 * power - 1) * arb(cutoff)**(2 * power - 1)).sqrt()).upper()


def tail_bound(modes, cutoff, order, boundary, moments, arithmetic_moments,
               absolute_even_remainder, absolute_arithmetic_remainder, b_tail):
    if (type(cutoff) is not int or cutoff <= modes or type(order) is not int or order < 0
            or len(moments) != order or len(arithmetic_moments) != order):
        raise ValueError('tail cutoff beyond retained rank and matching nonnegative expansion order required')
    terms = [(arb(2).sqrt() * b_tail * abs(boundary).upper() * power_tail_l2(cutoff, 1)).upper()]
    terms += [(2 * b_tail * abs(moment).upper() * power_tail_l2(cutoff, 2 * r + 1)).upper()
              for r, moment in enumerate(moments, 1)]
    terms += [(2 * abs(moment).upper() * power_tail_l2(cutoff, 2 * r + 2)).upper()
              for r, moment in enumerate(arithmetic_moments)]
    geometric = 1 / (1 - arb(modes)**2 / arb(cutoff)**2)
    remainder = (2 * geometric * (b_tail * absolute_even_remainder * power_tail_l2(cutoff, 2 * order + 3)
                                  + absolute_arithmetic_remainder * power_tail_l2(cutoff, 2 * order + 2))).upper()
    return (sum(terms, arb(0)) + remainder).upper(), terms, remainder


def cell_moments(taylor, even_cell, spatial_cell, order):
    modes = taylor['modes']
    radius = ball(even_cell['half_width'])
    offset = ball(even_cell['center_offset'])
    from weil_eigenfamily import _translate
    physical = physical_candidate(even_cell)
    coordinates = [arb_poly([ball(x) for x in row]) for row in even_cell['ground_candidate_coefficients']]
    coordinate_bounds = [polynomial_bound(poly, radius) for poly in coordinates]
    norm_upper = sum((x * x for x in coordinate_bounds), arb(0)).sqrt().upper()
    norm_range = arb(1).union(norm_upper)
    distance = ball(even_cell['uniform_unit_ground_distance_upper'])
    units = [polynomial_range(poly, radius) / norm_range + arb(0, distance) for poly in physical]
    b_polynomials, b_errors, b_ranges = [], [], []
    for i in range(1, modes + 1):
        poly = arb_poly([box(matrix[i][0]) * i / arb(2).sqrt()
                         for matrix in taylor['even_matrix_coefficients']])
        bpoly = _translate(poly, offset)
        error = (ball(taylor['even_value_remainder_upper'][i][0]) * i / arb(2).sqrt()).upper()
        b_polynomials.append(bpoly)
        b_errors.append(error)
        b_ranges.append(polynomial_range(bpoly, radius) + arb(0, error))
    moments, arithmetic = [], []
    for r in range(order):
        weights = [arb(i)**(2 * r + 2) for i in range(1, modes + 1)]
        poly = sum((weight * p for weight, p in zip(weights, physical[1:])), arb_poly())
        norm = sum((x * x for x in weights), arb(0)).sqrt().upper()
        moments.append(polynomial_range(poly, radius) / norm_range + arb(0, (norm * distance).upper()))
        weights = [arb(i)**(2 * r + 1) for i in range(1, modes + 1)]
        poly = sum((weight * p * b for weight, p, b in zip(weights, physical[1:], b_polynomials)), arb_poly())
        bnorm = sum(((weight * abs(b).upper())**2 for weight, b in zip(weights, b_ranges)), arb(0)).sqrt().upper()
        berror = sum((weight * polynomial_bound(p, radius) * error
                      for weight, p, error in zip(weights, physical[1:], b_errors)), arb(0)).upper()
        arithmetic.append(polynomial_range(poly, radius) / norm_range + arb(0, (distance * bnorm + berror).upper()))
    absolute_even = sum((arb(i)**(2 * order + 2) * abs(units[i]).upper() for i in range(1, modes + 1)), arb(0)).upper()
    absolute_arithmetic = sum((arb(i)**(2 * order + 1) * abs(b_ranges[i - 1]).upper() * abs(units[i]).upper()
                               for i in range(1, modes + 1)), arb(0)).upper()
    return (box(spatial_cell['exact_unit_ground_spatial_boundary_interval']), moments, arithmetic,
            absolute_even, absolute_arithmetic, units)


def certify(taylor, even, spatial, cutoff=64, order=8):
    if (taylor.get('status') != 'certified_weil_entry_taylor_cell_not_ground_profile_budget'
            or even.get('status') != 'certified_finite_whole_cell_even_eigenfamily'
            or spatial.get('status') != 'certified_finite_uniform_positive_spatial_kernel_and_real_zero_profiles'):
        raise ValueError('complete ground and spatial cell certificates required')
    validate_partition(even)
    if (type(order) is not int or not 0 <= order <= 32
            or type(cutoff) is not int or cutoff <= even['modes']):
        raise ValueError('expansion order 0..32 and cutoff beyond retained rank required')
    for field in ('lower_prime_power', 'upper_prime_power', 'modes', 'degree'):
        if taylor[field] != even[field] or even[field] != spatial[field]:
            raise ValueError('different support/rank cells')
    if (len(spatial['cells']) != even['subdivisions']
            or not all(c.get('positive_kernel_certified') for c in spatial['cells'])):
        raise ValueError('complete spatial cover required')
    with ctx.workprec(1024):
        constants = global_constants(arb(even['lower_prime_power']).log(), arb(even['upper_prime_power']).log(),
                                     [tuple(x) for x in taylor['active_prime_powers']])
        b_tail = (constants['b0'] + constants['b1'] / cutoff).upper()
        rows = []
        for e, s in zip(even['cells'], spatial['cells']):
            if any(e[field] != s[field] for field in ('index', 'center_offset', 'half_width')):
                raise ValueError('different support subcell partitions')
            boundary, moments, arithmetic, ae, aa, units = cell_moments(taylor, e, s, order)
            bound, terms, remainder = tail_bound(even['modes'], cutoff, order, boundary, moments, arithmetic, ae, aa, b_tail)
            uncoupled = (2 * arb(2).sqrt() * constants['b']
                         * (abs(units[0]).upper() + arb(2).sqrt() * sum((abs(x).upper() for x in units[1:]), arb(0)))
                         / arb(cutoff - even['modes']).sqrt()).upper()
            rows.append({'index': e['index'], 'center_offset': e['center_offset'], 'half_width': e['half_width'],
                         'signed_boundary_interval': endpoints(boundary),
                         'signed_even_moment_intervals': [endpoints(x) for x in moments],
                         'signed_arithmetic_moment_intervals': [endpoints(x) for x in arithmetic],
                         'infinite_even_tail_forcing_l2_upper': str(bound.fmpq()),
                         'uncoupled_displacement_tail_l2_upper': str(uncoupled.fmpq()),
                         'individual_power_tail_l2_upper': [str(x.fmpq()) for x in terms],
                         'geometric_expansion_remainder_l2_upper': str(remainder.fmpq())})
        full_start, even_start = coercive_start(constants), coercive_start(constants, True)
        return {'status': 'certified_cell_uniform_infinite_mode_forcing_and_high_mode_coercivity_not_profile_budget',
                'lower_prime_power': even['lower_prime_power'], 'upper_prime_power': even['upper_prime_power'],
                'modes': even['modes'], 'degree': even['degree'], 'subdivisions': even['subdivisions'],
                'tail_cutoff': cutoff, 'expansion_order': order, 'working_bits': 1024,
                'uniform_infinite_even_tail_forcing_l2_upper': str(max(ball(c['infinite_even_tail_forcing_l2_upper']) for c in rows).fmpq()),
                'uniform_uncoupled_displacement_tail_l2_upper': str(max(ball(c['uncoupled_displacement_tail_l2_upper']) for c in rows).fmpq()),
                'uniform_displacement_sequence_abs_upper': str(constants['b'].fmpq()),
                'uniform_displacement_sequence_tail_abs_upper': str(b_tail.fmpq()),
                'uniform_full_off_diagonal_operator_norm_upper': str(constants['full_off_diagonal_norm'].fmpq()),
                'full_high_mode_first_index_with_lower_bound_above_one': full_start,
                'even_high_mode_first_index_with_lower_bound_above_one': even_start,
                'full_high_mode_lower_at_certified_start': str(high_mode_lower(constants, full_start).fmpq()),
                'even_high_mode_lower_at_certified_start': str(high_mode_lower(constants, even_start, True).fmpq()),
                'cells': rows,
                'claim': 'For every support in this cell, the omitted even components j>tail_cutoff of A times the exact retained-rank unit ground have the saved l2 bound; high-mode compressions beyond the saved starts exceed the identity uniformly in all higher ranks.',
                'scope': 'Infinite Fourier forcing tail and high-mode block only. Intermediate modes and inverse-response transfer to ground profiles are not bounded by this certificate.',
                'remaining': 'Low-spectrum isolation for the infinite operator, uniform coupled profile pairing, summable support/rank path, Xi identification, theta curvature and RH.'}


def run(taylor_path, even_path, spatial_path, cutoff=64, order=8):
    paths = {'taylor': taylor_path, 'even': even_path, 'spatial': spatial_path}
    raw = {key: path.read_bytes() for key, path in paths.items()}
    inputs = {key: json.loads(value) for key, value in raw.items()}
    source = Path(__file__).parent
    for key in ('taylor', 'spatial'):
        for name, digest in inputs[key]['source_hashes'].items():
            if hashlib.sha256((source / name).read_bytes()).hexdigest() != digest:
                raise ValueError('stale source: ' + name)
    if inputs['even']['source_sha256'] != hashlib.sha256((source / 'weil_eigenfamily.py').read_bytes()).hexdigest():
        raise ValueError('stale even eigenfamily source')
    if (inputs['even']['input_sha256'] != hashlib.sha256(raw['taylor']).hexdigest()
            or inputs['spatial']['input_sha256']['even'] != hashlib.sha256(raw['even']).hexdigest()):
        raise ValueError('matrix, ground and spatial inputs do not match')
    result = certify(inputs['taylor'], inputs['even'], inputs['spatial'], cutoff, order)
    result['input_sha256'] = {key: hashlib.sha256(value).hexdigest() for key, value in raw.items()}
    result['source_hashes'] = {name: hashlib.sha256((source / name).read_bytes()).hexdigest() for name in
                               ('weil_rank_tail_cell.py', 'weil_profile_cell_budget.py', 'weil_eigenfamily.py', 'weil_odd_cell.py', 'certified_weil.py')}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--taylor', type=Path, required=True)
    parser.add_argument('--even', type=Path, required=True)
    parser.add_argument('--spatial', type=Path, required=True)
    parser.add_argument('--cutoff', type=int, default=64)
    parser.add_argument('--order', type=int, default=8)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.taylor, args.even, args.spatial, args.cutoff, args.order)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])
    print(float(Fraction(result['uniform_infinite_even_tail_forcing_l2_upper'])))
    print(result['even_high_mode_first_index_with_lower_bound_above_one'], result['full_high_mode_first_index_with_lower_bound_above_one'])


if __name__ == '__main__':
    main()
