"""Finite strip-profile increment budget from coupled polynomial densities.

The density derivative and endpoint flux are enclosed over a complete
support cell. Exact ground-profile increments use the saved uniform C0
transfer errors; no derivative enclosure of the exact ground is asserted.
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


def polynomial_range(poly, radius):
    return poly[0] + arb(0, polynomial_bound(poly - poly[0], radius))


def physical_candidate(cell):
    size = len(cell['ground_candidate_coefficients'])
    coordinates = [arb_poly([ball(x) for x in row]) for row in cell['ground_candidate_coefficients']]
    basis = [[box(x) for x in row] for row in cell['center_basis']]
    return [sum((basis[i][j] * coordinates[j] for j in range(size)), arb_poly())
            for i in range(size)]


def density_derivative_polynomials(physical, length):
    """Numerator of L^2*g^2*partial_L[raw(t/L)/(L*g)] at fixed t.

    Output C0,Cj,Sj represents C0+sum Cj*cos_j+s*sum Sj*sin_j.
    All products and quotient-rule cancellations precede enclosure.
    """
    origin = physical[0]
    prime = origin.derivative()
    cosines, sines = [], []
    for j, coefficient in enumerate(physical[1:], 1):
        product = coefficient * origin
        coupled = coefficient.derivative() * origin - coefficient * prime
        cosines.append(arb(2).sqrt() * (length * coupled - product))
        sines.append(arb(2).sqrt() * (2 * arb.pi() * j) * product)
    return -origin * origin, cosines, sines


def candidate_derivative_bound(physical, length_center, radius, sigma, spatial_subdivisions):
    if (type(spatial_subdivisions) is not int or spatial_subdivisions < 1
            or not radius > 0 or not sigma >= 0):
        raise ValueError('positive spatial subdivision count/radius and nonnegative strip height required')
    length_poly = arb_poly([length_center, 1])
    length_range = length_center + arb(0, radius)
    origin_range = polynomial_range(physical[0], radius)
    if not length_range > 0 or not origin_range > 0:
        raise ArithmeticError('positive candidate origin and support required')
    constant, cosines, sines = density_derivative_polynomials(physical, length_poly)
    constant_range = polynomial_range(constant, radius)
    cosine_ranges = [polynomial_range(poly, radius) for poly in cosines]
    sine_ranges = [polynomial_range(poly, radius) for poly in sines]
    # Numerator is even in s. Equal tiles cover [0,1/2], including both
    # endpoints. Interval trig enclosures, not samples, bound every tile.
    integral = arb(0)
    for k in range(spatial_subdivisions):
        spatial = ball(Fraction(2 * k + 1, 4 * spatial_subdivisions)) + arb(0, ball(Fraction(1, 4 * spatial_subdivisions)))
        numerator = constant_range
        for j, (cosine, sine) in enumerate(zip(cosine_ranges, sine_ranges), 1):
            angle = 2 * arb.pi() * j * (spatial + arb(1) / 2)
            numerator += cosine * angle.cos() + spatial * sine * angle.sin()
        integral += abs(numerator).upper() / spatial_subdivisions
    termwise = (abs(constant_range).upper()
                + sum((abs(x).upper() for x in cosine_ranges), arb(0))
                + sum((abs(x).upper() / 2 for x in sine_ranges), arb(0)))
    denominator = length_range.lower() * origin_range.lower() * origin_range.lower()
    interior = (integral / denominator).upper()
    naive_interior = (termwise / denominator).upper()
    boundary_poly = physical[0] + arb(2).sqrt() * sum(physical[1:], arb_poly())
    boundary_range = polynomial_range(boundary_poly, radius)
    endpoint_flux = (abs(boundary_range).upper() / (length_range.lower() * origin_range.lower())).upper()
    weight = (sigma * length_range.upper() / 2).exp().upper()
    bound = (weight * (interior + endpoint_flux)).upper()
    naive_bound = (weight * (naive_interior + endpoint_flux)).upper()
    return {
        'candidate_origin_range': endpoints(origin_range),
        'candidate_raw_boundary_range': endpoints(boundary_range),
        'spatial_density_derivative_L1_upper': str(interior.fmpq()),
        'spatial_endpoint_flux_upper': str(endpoint_flux.fmpq()),
        'uniform_candidate_strip_derivative_upper': str(bound.fmpq()),
        'termwise_candidate_strip_derivative_upper': str(naive_bound.fmpq()),
    }


def profile_transfer_bound(cell, sigma, length_upper):
    """Recompute the proven residual/origin transfer on any finite strip."""
    origin = ball(cell['uniform_unit_candidate_origin_lower'])
    distance = ball(cell['uniform_unit_ground_distance_upper'])
    if not distance >= 0 or not origin > distance:
        raise ArithmeticError('protected unit candidate origin required')
    argument = sigma * length_upper
    weight = arb(1) if sigma == 0 else (argument.sinh() / argument).sqrt()
    return (weight * distance / (origin - distance) * (1 + 1 / origin)).upper()


def certify(even, spatial_subdivisions=128, sigma=Fraction(2, 5)):
    if (even.get('status') != 'certified_finite_whole_cell_even_eigenfamily'
            or not even.get('all_origin_strip_transfers_certified')):
        raise ValueError('complete even family with protected profile transfers required')
    validate_partition(even)
    sigma_fraction = Fraction(sigma)
    if sigma_fraction < 0:
        raise ValueError('nonnegative rational strip height required')
    with ctx.workprec(1024):
        sigma = ball(sigma_fraction)
        center = box(even['log_support_center'])
        length_upper = arb(even['upper_prime_power']).log().upper()
        rows = []
        integrated = arb(0)
        naive_integrated = arb(0)
        error_budget = arb(0)
        for cell in even['cells']:
            if cell['strip_height'] != '2/5':
                raise ValueError('strip-height mismatch')
            radius = ball(cell['half_width'])
            result = candidate_derivative_bound(physical_candidate(cell), center + ball(cell['center_offset']),
                                                radius, sigma, spatial_subdivisions)
            local = 2 * radius * ball(result['uniform_candidate_strip_derivative_upper'])
            naive_local = 2 * radius * ball(result['termwise_candidate_strip_derivative_upper'])
            transfer = profile_transfer_bound(cell, sigma, length_upper)
            integrated += local
            naive_integrated += naive_local
            error_budget += 2 * transfer
            result.update({'index': cell['index'], 'center_offset': cell['center_offset'], 'half_width': cell['half_width'],
                           'integrated_candidate_strip_budget_upper': str(local.upper().fmpq()),
                           'exact_ground_endpoint_transfer_allowance_upper': str((2 * transfer).upper().fmpq())})
            rows.append(result)
        return {
            'status': 'certified_finite_whole_cell_strip_increment_budget_not_all_rank',
            'lower_prime_power': even['lower_prime_power'], 'upper_prime_power': even['upper_prime_power'],
            'modes': even['modes'], 'degree': even['degree'], 'subdivisions': even['subdivisions'],
            'spatial_subdivisions_on_half_interval': spatial_subdivisions, 'working_bits': 1024, 'strip_height': str(sigma_fraction),
            'integrated_candidate_strip_budget_upper': str(integrated.upper().fmpq()),
            'termwise_integrated_candidate_strip_budget_upper': str(naive_integrated.upper().fmpq()),
            'total_exact_ground_transfer_allowance_upper': str(error_budget.upper().fmpq()),
            'any_two_supports_exact_ground_strip_increment_upper': str((integrated + error_budget).upper().fmpq()),
            'cells': rows,
            'claim': 'For every two ordered supports in this closed cell and every complex z in the saved strip, the exact even ground-profile increment is bounded by the saved budget.',
            'boundary_control': 'Moving spatial-endpoint flux is explicitly enclosed; subcell endpoint transfers telescope, including the closed prime-support endpoints.',
            'scope': 'Finite full-cell C0 increment bound via candidate density derivatives. No exact-ground derivative or arbitrary-partition total variation claim.',
            'remaining': 'Uniform support/rank summability, full parity gates beyond this cell, Xi identification, theta curvature, and RH.',
        }


def run(even_path, spatial_subdivisions=128, sigma=Fraction(2, 5)):
    raw = even_path.read_bytes()
    even = json.loads(raw)
    source = Path(__file__).parent
    if even['source_sha256'] != hashlib.sha256((source / 'weil_eigenfamily.py').read_bytes()).hexdigest():
        raise ValueError('stale even-family source')
    result = certify(even, spatial_subdivisions, sigma)
    result['input_sha256'] = hashlib.sha256(raw).hexdigest()
    result['source_hashes'] = {name: hashlib.sha256((source / name).read_bytes()).hexdigest()
                               for name in ('weil_profile_cell_budget.py', 'weil_eigenfamily.py', 'weil_odd_cell.py', 'certified_weil.py')}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--even', type=Path, required=True)
    parser.add_argument('--spatial-subdivisions', type=int, default=128)
    parser.add_argument('--sigma', type=Fraction, default=Fraction(2, 5))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.even, args.spatial_subdivisions, args.sigma)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])
    print(float(Fraction(result['any_two_supports_exact_ground_strip_increment_upper'])))


if __name__ == '__main__':
    main()
