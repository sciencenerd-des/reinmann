"""Uniform spatial-boundary and kernel gates for a finite Weil support cell.

Parity separation rules out a zero spatial boundary by the exact Weil
displacement identity. Bernstein functionals certify spatial positivity.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path

from flint import arb, arb_poly, fmpq_poly, ctx

from certified_weil import endpoints
from weil_eigenfamily import ball, box, polynomial_bound
from weil_odd_cell import validate_partition


def bernstein_functionals(modes: int):
    if type(modes) is not int or modes < 1:
        raise ValueError('positive Fourier rank required')
    variable = fmpq_poly([1, -2])
    polynomials = [fmpq_poly([1]), variable]
    for _ in range(1, modes):
        polynomials.append(2 * variable * polynomials[-1] - polynomials[-2])
    result = []
    for k in range(modes + 1):
        row = [arb(1)]
        for j in range(1, modes + 1):
            coefficient = sum((Fraction(str(polynomials[j][r])) * Fraction(comb(k, r), comb(modes, r))
                               for r in range(min(k, j) + 1)), Fraction(0))
            row.append(arb(2).sqrt() * ball(coefficient))
        result.append(row)
    return result


def certify(even: dict, parity: dict):
    if (even.get('status') != 'certified_finite_whole_cell_even_eigenfamily'
            or parity.get('status') != 'certified_finite_uniform_positive_weil_simple_even_ground'):
        raise ValueError('uniform even eigenfamily and full parity gate required')
    for field in ('lower_prime_power', 'upper_prime_power', 'modes', 'degree', 'subdivisions', 'log_support_center', 'cell_half_width'):
        if even[field] != parity[field]:
            raise ValueError('parity and even certificates cover different cells')
    validate_partition(even)
    if (not even.get('all_origin_strip_transfers_certified')
            or len(parity['cells']) != even['subdivisions']
            or not all(c.get('simple_even_full_ground_certified') for c in parity['cells'])):
        raise ValueError('protected Fourier origin and complete full parity cover required')
    with ctx.workprec(1024):
        modes = even['modes']
        functionals = bernstein_functionals(modes)
        functional_norms = [sum((x * x for x in row), arb(0)).sqrt().upper() for row in functionals]
        cells = []
        for e, p in zip(even['cells'], parity['cells']):
            if e['index'] != p['index'] or e['center_offset'] != p['center_offset'] or e['half_width'] != p['half_width']:
                raise ValueError('subcell partitions differ')
            radius = ball(e['half_width'])
            coordinates = [arb_poly([ball(x) for x in row]) for row in e['ground_candidate_coefficients']]
            basis = [[box(x) for x in row] for row in e['center_basis']]
            physical = [sum((basis[i][j] * coordinates[j] for j in range(modes + 1)), arb_poly())
                        for i in range(modes + 1)]
            coordinate_bounds = [polynomial_bound(x, radius) for x in coordinates]
            norm_upper = sum((x * x for x in coordinate_bounds), arb(0)).sqrt().upper()
            norm_range = arb(1).union(norm_upper)
            distance = ball(e['uniform_unit_ground_distance_upper'])
            unit_bernstein = []
            for functional, functional_norm in zip(functionals, functional_norms):
                polynomial = sum((a * b for a, b in zip(functional, physical)), arb_poly())
                candidate_range = polynomial[0] + arb(0, polynomial_bound(polynomial - polynomial[0], radius))
                exact_range = candidate_range / norm_range + arb(0, (functional_norm * distance).upper())
                unit_bernstein.append(exact_range)
            ground_origin = box(e['ground_candidate_origin_range'])
            origin_upper = (ground_origin.upper() + distance).upper()
            even_error = ball(e['uniform_eigenvalue_disk_radius_upper'])
            odd_error = ball(p['eigenvalue_disk_radius_upper'])
            even_ranges = [box(x) for x in e['uniform_candidate_eigenvalue_ranges']]
            odd_ranges = [box(x) for x in p['candidate_ranges']]
            odd_clearance = (odd_ranges[0].lower() - odd_error - even_ranges[0].upper() - even_error).lower()
            operator_upper = max((even_ranges[-1].upper() + even_error).upper(),
                                 (odd_ranges[-1].upper() + odd_error).upper())
            # |S| >= odd_gap * ||diag(j) v|| / ||b||,
            # ||diag(j) v|| >= sqrt(1-v0^2), ||b|| <= N ||A||.
            algebraic_lower = None
            if origin_upper < 1 and odd_clearance > 0 and operator_upper > 0:
                algebraic_lower = (odd_clearance * (1 - origin_upper * origin_upper).sqrt()
                                   / (modes * operator_upper)).lower()
            positive = all(x > 0 for x in unit_bernstein)
            cells.append({
                'index': e['index'], 'center_offset': e['center_offset'], 'half_width': e['half_width'],
                'exact_unit_ground_bernstein_intervals': [endpoints(x) for x in unit_bernstein],
                'exact_unit_ground_spatial_boundary_interval': endpoints(unit_bernstein[0]),
                'positive_kernel_certified': positive,
                'odd_minus_even_ground_clearance_lower': str(odd_clearance.fmpq()),
                'full_weil_operator_norm_upper': str(operator_upper.fmpq()),
                'unit_ground_origin_upper': str(origin_upper.fmpq()),
                'absolute_spatial_boundary_lower_from_displacement': str(algebraic_lower.fmpq()) if algebraic_lower is not None else None,
                'boundary_nonzero_from_parity_rigidity': bool(odd_clearance > 0),
            })
        passed = all(c['positive_kernel_certified'] for c in cells)
        boundary = min(Fraction(c['exact_unit_ground_spatial_boundary_interval']['lo']) for c in cells)
        algebraic_values = [Fraction(c['absolute_spatial_boundary_lower_from_displacement']) for c in cells
                            if c['absolute_spatial_boundary_lower_from_displacement'] is not None]
        algebraic = min(algebraic_values) if len(algebraic_values) == len(cells) else None
        return {
            'status': ('certified_finite_uniform_positive_spatial_kernel_and_real_zero_profiles' if passed
                       else 'finite_spatial_positivity_unresolved_with_boundary_rigidity'),
            'lower_prime_power': even['lower_prime_power'], 'upper_prime_power': even['upper_prime_power'],
            'modes': modes, 'degree': even['degree'], 'subdivisions': even['subdivisions'], 'working_bits': 1024,
            'positive_subcells': sum(c['positive_kernel_certified'] for c in cells),
            'uniform_signed_unit_spatial_boundary_lower': str(boundary),
            'uniform_absolute_boundary_lower_from_displacement': str(algebraic) if algebraic is not None else None,
            'all_spatial_boundaries_nonzero_from_parity': all(c['boundary_nonzero_from_parity_rigidity'] for c in cells),
            'real_zero_profile_consequence': ('Written exact displacement/quotient theorem applies at every support in this finite cell: '
                                             'simple even full ground, nonzero spatial boundary and nonzero Fourier origin.'),
            'cells': cells,
            'scope': 'Complete finite support cell; spatial positivity additionally requires every Bernstein interval to be positive.',
            'remaining': 'All-support/all-rank gates, cumulative convergence budget, identification with Xi, and RH.',
        }


def run(even_path: Path, parity_path: Path):
    raw_even, raw_parity = even_path.read_bytes(), parity_path.read_bytes()
    even, parity = json.loads(raw_even), json.loads(raw_parity)
    source = Path(__file__).parent
    if even['source_sha256'] != hashlib.sha256((source / 'weil_eigenfamily.py').read_bytes()).hexdigest():
        raise ValueError('stale even eigenfamily source')
    for name, digest in parity['source_hashes'].items():
        if hashlib.sha256((source / name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale parity source: ' + name)
    if parity['input_sha256']['even'] != hashlib.sha256(raw_even).hexdigest():
        raise ValueError('parity gate uses a different even eigenfamily')
    if even['input_sha256'] != parity['input_sha256']['taylor']:
        raise ValueError('parity and even inputs use different Taylor matrices')
    result = certify(even, parity)
    result['input_sha256'] = {'even': hashlib.sha256(raw_even).hexdigest(), 'parity': hashlib.sha256(raw_parity).hexdigest()}
    result['source_hashes'] = {name: hashlib.sha256((source / name).read_bytes()).hexdigest()
                              for name in ('weil_spatial_cell.py', 'weil_odd_cell.py', 'weil_eigenfamily.py')}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--even', type=Path, required=True)
    parser.add_argument('--parity', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.even, args.parity)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['positive_subcells'], '/', result['subdivisions'])


if __name__ == '__main__':
    main()
