"""Certify odd/even separation over a complete finite prime-power cell."""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, arb_mat, arb_poly, ctx

from certified_weil import endpoints
from weil_eigenfamily import ball, box, center_basis, polynomial_bound, predictors, _translate
from weil_support_taylor import entry_taylor, remainder_bound


def validate_partition(even):
    """Reject incomplete or relabeled covers before making a uniform claim."""
    count = even['subdivisions']
    if type(count) is not int or count < 1 or len(even['cells']) != count:
        raise ValueError('complete positive subdivision count required')
    half_width = Fraction(even['cell_half_width'])
    if half_width <= 0:
        raise ValueError('positive support half width required')
    for i, cell in enumerate(even['cells']):
        offset = -half_width + Fraction(2 * i + 1, count) * half_width
        if (cell['index'] != i or Fraction(cell['center_offset']) != offset
                or Fraction(cell['half_width']) != half_width / count
                or cell.get('status') != 'certified_finite_uniform_even_eigenfamily'
                or not cell.get('positive_even_ground_certified')):
            raise ValueError('complete certified even support cover required')


def validate_spectrum(matrices, radius, error, degree):
    size = matrices[0].nrows()
    eigenvalues, basis = center_basis(matrices[0])
    transformed = [arb_mat([[eigenvalues[i] if i == j else arb(0)
                             for j in range(size)] for i in range(size)])]
    transformed += [basis.transpose() * matrix * basis for matrix in matrices[1:]]
    families, lambdas = predictors(transformed, eigenvalues, degree)
    polynomials = [[arb_poly([matrix[i, j] for matrix in transformed])
                    for j in range(size)] for i in range(size)]
    beta = max(sum((polynomial_bound(families[j][i] - (1 if i == j else 0), radius)
                    for j in range(size)), arb(0)).upper() for i in range(size))
    residuals = []
    for branch in range(size):
        coordinates = [polynomial_bound(x, radius) for x in families[branch]]
        norm = sum((x * x for x in coordinates), arb(0)).sqrt().upper()
        column = []
        for row in range(size):
            residual = sum((polynomials[row][j] * families[branch][j]
                            for j in range(size)), arb_poly()) - lambdas[branch] * families[branch][row]
            column.append(polynomial_bound(residual, radius) + error * norm)
        residuals.append(column)
    residual_norm = max(sum((residuals[j][i] for j in range(size)), arb(0)).upper()
                        for i in range(size))
    ranges = [poly[0] + arb(0, polynomial_bound(poly - poly[0], radius)) for poly in lambdas]
    disk = (residual_norm / (1 - beta)).upper() if beta < 1 else None
    passed = disk is not None and all(b - a > 2 * disk for a, b in zip(ranges, ranges[1:]))
    return {
        'isolated': passed,
        'center_spectrum': [endpoints(x) for x in eigenvalues],
        'candidate_ranges': [endpoints(x) for x in ranges],
        'basis_drift_infinity_upper': str(beta.fmpq()),
        'residual_infinity_upper': str(residual_norm.fmpq()),
        'eigenvalue_disk_radius_upper': str(disk.fmpq()) if disk is not None else None,
    }


def full_gap(even_cell, odd_cell):
    if not odd_cell['isolated']:
        return None
    even_error = ball(even_cell['uniform_eigenvalue_disk_radius_upper'])
    odd_error = ball(odd_cell['eigenvalue_disk_radius_upper'])
    even_ranges = [box(x) for x in even_cell['uniform_candidate_eigenvalue_ranges']]
    odd_lowest = box(odd_cell['candidate_ranges'][0]) + arb(0, odd_error)
    even_lowest = even_ranges[0] + arb(0, even_error)
    even_second = even_ranges[1] + arb(0, even_error)
    return even_second.min(odd_lowest) - even_lowest


def certify(taylor: dict, even: dict) -> dict:
    if (taylor.get('status') != 'certified_weil_entry_taylor_cell_not_ground_profile_budget'
            or even.get('status') != 'certified_finite_whole_cell_even_eigenfamily'):
        raise ValueError('certified matrix Taylor cell and complete even eigenfamily required')
    for field in ('lower_prime_power', 'upper_prime_power', 'modes', 'degree', 'cell_half_width', 'log_support_center'):
        if taylor[field] != even[field]:
            raise ValueError('even eigenfamily belongs to a different matrix cell')
    validate_partition(even)
    with ctx.workprec(1024):
        size, degree = taylor['modes'], taylor['degree']
        center, half_width = box(taylor['log_support_center']), Fraction(taylor['cell_half_width'])
        radius = Fraction(taylor['analytic_radius'])
        powers = [tuple(x) for x in taylor['active_prime_powers']]
        terms = taylor['tail_terms']
        cache = {}

        def scalar(i, j):
            key = min((i, j), (j, i), (-i, -j), (-j, -i))
            if key not in cache:
                cache[key] = entry_taylor(*key, center, powers, degree, radius, terms)
            return cache[key]

        matrices = [arb_mat(size, size) for _ in range(degree + 1)]
        bounds = [[arb(0) for _ in range(size)] for _ in range(size)]
        for i in range(1, size + 1):
            for j in range(i, size + 1):
                first, a = scalar(i, j)
                second, b = scalar(i, -j)
                for k in range(degree + 1):
                    matrices[k][i - 1, j - 1] = matrices[k][j - 1, i - 1] = first[k] - second[k]
                bounds[i - 1][j - 1] = bounds[j - 1][i - 1] = a + b
        value_errors = [[remainder_bound(x, radius, half_width, degree).upper() for x in row] for row in bounds]
        derivative_errors = [[remainder_bound(x, radius, half_width, degree, True).upper() for x in row] for row in bounds]
        value_error = max(sum(row, arb(0)).upper() for row in value_errors)
        coefficient_error = max(sum((sum((matrix[i, j].rad() * ball(half_width)**k
                                          for k, matrix in enumerate(matrices)), arb(0))
                                     for j in range(size)), arb(0)).upper() for i in range(size))
        approximation_error = value_error + coefficient_error
        polynomials = [[arb_poly([matrix[i, j].mid() for matrix in matrices])
                        for j in range(size)] for i in range(size)]
        cells = []
        for even_cell in even['cells']:
            offset, local_radius = ball(even_cell['center_offset']), ball(even_cell['half_width'])
            shifted = [[_translate(poly, offset) for poly in row] for row in polynomials]
            local = [arb_mat([[shifted[i][j][k] for j in range(size)] for i in range(size)])
                     for k in range(degree + 1)]
            result = validate_spectrum(local, local_radius, approximation_error, degree)
            gap = full_gap(even_cell, result)
            result.update({'index': even_cell['index'], 'center_offset': even_cell['center_offset'],
                           'half_width': even_cell['half_width'],
                           'full_weil_ground_gap': endpoints(gap) if gap is not None else None,
                           'simple_even_full_ground_certified': bool(gap is not None and gap > 0)})
            cells.append(result)
        passed = (even['all_even_ground_eigenvalues_positive']
                  and all(c['simple_even_full_ground_certified'] for c in cells))
        minimum_gap = min(Fraction(c['full_weil_ground_gap']['lo']) for c in cells) if passed else None
        return {
            'status': ('certified_finite_uniform_positive_weil_simple_even_ground' if passed else
                       'whole_cell_parity_comparison_unresolved'),
            'lower_prime_power': taylor['lower_prime_power'], 'upper_prime_power': taylor['upper_prime_power'],
            'modes': size, 'degree': degree, 'working_bits': 1024,
            'log_support_center': taylor['log_support_center'], 'cell_half_width': taylor['cell_half_width'],
            'odd_matrix_coefficients': [[[endpoints(matrix[i, j]) for j in range(size)] for i in range(size)]
                                        for matrix in matrices],
            'odd_value_remainder_upper': [[str(x.fmpq()) for x in row] for row in value_errors],
            'odd_derivative_remainder_upper': [[str(x.fmpq()) for x in row] for row in derivative_errors],
            'odd_value_operator_remainder_upper': str(value_error.fmpq()),
            'odd_matrix_approximation_operator_error_upper': str(approximation_error.upper().fmpq()),
            'subdivisions': even['subdivisions'],
            'certified_parity_subcells': sum(c['simple_even_full_ground_certified'] for c in cells),
            'uniform_full_weil_gap_lower': str(minimum_gap) if minimum_gap is not None else None,
            'cells': cells,
            'scope': 'Entire finite support cell: positive full Weil form and a simple even least eigenvalue, conditional on every saved gate passing.',
            'remaining': 'Spatial-boundary and positivity gates, all-support/all-rank control, Xi convergence, and RH.',
        }


def run(taylor_path: Path, even_path: Path) -> dict:
    raw_taylor, raw_even = taylor_path.read_bytes(), even_path.read_bytes()
    taylor, even = json.loads(raw_taylor), json.loads(raw_even)
    src = Path(__file__).parent
    for name, digest in taylor['source_hashes'].items():
        if hashlib.sha256((src / name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale matrix Taylor source: ' + name)
    if even['source_sha256'] != hashlib.sha256((src / 'weil_eigenfamily.py').read_bytes()).hexdigest():
        raise ValueError('stale even eigenfamily source')
    if even['input_sha256'] != hashlib.sha256(raw_taylor).hexdigest():
        raise ValueError('even eigenfamily input differs from matrix Taylor cell')
    result = certify(taylor, even)
    result['input_sha256'] = {'taylor': hashlib.sha256(raw_taylor).hexdigest(), 'even': hashlib.sha256(raw_even).hexdigest()}
    result['source_hashes'] = {name: hashlib.sha256((src / name).read_bytes()).hexdigest()
                               for name in ('weil_odd_cell.py', 'weil_eigenfamily.py', 'weil_support_taylor.py', 'certified_weil.py')}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--taylor', type=Path, required=True)
    parser.add_argument('--even', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.taylor, args.even)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['certified_parity_subcells'], '/', result['subdivisions'])


if __name__ == '__main__':
    main()
