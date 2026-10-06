"""Validate polynomial eigenpair candidates throughout a finite Weil cell.

The center eigenbasis is exactly orthonormal. Polynomial residuals are
formed before interval evaluation, retaining support-parameter cancellation.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb_mat, arb, arb_mat, arb_poly, ctx

from certified_weil import endpoints


def ball(value) -> arb:
    value = Fraction(value)
    return arb(value.numerator) / value.denominator


def box(value) -> arb:
    return ball(value['lo']).union(ball(value['hi']))


def polynomial_bound(polynomial: arb_poly, radius: arb) -> arb:
    return sum((abs(polynomial[k]).upper() * radius**k
                for k in range(len(polynomial))), arb(0)).upper()


def center_basis(matrix: arb_mat):
    values, vectors = acb_mat(matrix).eig(right=True, algorithm='rump')
    ordered = sorted(range(len(values)), key=lambda i: values[i].real.mid())
    if not all(values[i].is_finite() and values[i].imag.contains(0) for i in ordered):
        raise ArithmeticError('real center eigenvalues unresolved')
    eigenvalues = [values[i].real for i in ordered]
    if not all(a < b for a, b in zip(eigenvalues, eigenvalues[1:])):
        raise ArithmeticError('simple ordered center spectrum unresolved')
    columns = []
    for index in ordered:
        raw = [vectors[j, index] for j in range(len(values))]
        if not all(x.is_finite() and x.imag.contains(0) for x in raw):
            raise ArithmeticError('real center eigenvectors unresolved')
        real = [x.real for x in raw]
        norm = sum((x * x for x in real), arb(0)).sqrt()
        if not norm > 0:
            raise ArithmeticError('nonzero center eigenvector unresolved')
        unit = [x / norm for x in real]
        if len(columns) == 0 and unit[0] < 0:
            unit = [-x for x in unit]
        for previous in columns:
            if not sum((a * b for a, b in zip(unit, previous)), arb(0)).contains(0):
                raise ArithmeticError('center orthogonality unresolved')
        columns.append(unit)
    basis = arb_mat([[columns[j][i] for j in range(len(values))] for i in range(len(values))])
    return eigenvalues, basis


def predictors(coefficients: list[arb_mat], eigenvalues: list[arb], degree: int):
    """Numerical candidates only; the subsequent residual supplies validation."""
    size = len(eigenvalues)
    midpoints = [[[matrix[i, j].mid() for j in range(size)] for i in range(size)]
                 for matrix in coefficients]
    center = [value.mid() for value in eigenvalues]
    families = []
    lambdas = []
    for anchor in range(size):
        vector = [[arb(1 if row == anchor else 0)] + [arb(0)] * degree
                  for row in range(size)]
        values = [center[anchor]] + [arb(0)] * degree
        for k in range(1, degree + 1):
            source = [sum((midpoints[j][row][col] * vector[col][k - j]
                           for j in range(1, k + 1) for col in range(size)), arb(0))
                      for row in range(size)]
            values[k] = source[anchor].mid()
            for row in range(size):
                if row != anchor:
                    correction = sum((values[j] * vector[row][k - j]
                                      for j in range(1, k)), arb(0))
                    vector[row][k] = ((correction - source[row])
                                      / (center[row] - center[anchor])).mid()
        families.append([arb_poly(row) for row in vector])
        lambdas.append(arb_poly(values))
    return families, lambdas


def _validate(matrices, radius, truncation, degree, length_upper) -> dict:
    with ctx.workprec(1024):
        size = matrices[0].nrows()
        eigenvalues, basis = center_basis(matrices[0])
        # True center eigenvectors are orthonormal by symmetric spectral
        # theory. Set their constant transform to its exact diagonal form.
        transformed = [arb_mat([[eigenvalues[i] if i == j else arb(0)
                                 for j in range(size)] for i in range(size)])]
        transformed += [basis.transpose() * matrix * basis for matrix in matrices[1:]]
        families, lambdas = predictors(transformed, eigenvalues, degree)
        polynomials = [[arb_poly([matrix[i, j] for matrix in transformed])
                        for j in range(size)] for i in range(size)]
        drift = [[polynomial_bound(families[j][i] - (1 if i == j else 0), radius)
                  for j in range(size)] for i in range(size)]
        beta = max(sum(row, arb(0)).upper() for row in drift)
        residuals = []
        residual_bounds = []
        candidate_norm = None
        for anchor in range(size):
            residual = [sum((polynomials[row][col] * families[anchor][col]
                             for col in range(size)), arb_poly())
                        - lambdas[anchor] * families[anchor][row] for row in range(size)]
            coordinate_bounds = [polynomial_bound(x, radius) for x in families[anchor]]
            vector_bound = sum((x * x for x in coordinate_bounds), arb(0)).sqrt()
            if anchor == 0:
                candidate_norm = vector_bound.upper()
            bounds = [polynomial_bound(x, radius) + truncation * vector_bound for x in residual]
            residuals.append(residual)
            residual_bounds.append(bounds)
        residual_norm = max(sum((residual_bounds[j][i] for j in range(size)), arb(0)).upper()
                            for i in range(size))
        ranges = []
        for polynomial in lambdas:
            error = polynomial_bound(polynomial - polynomial[0], radius)
            ranges.append(polynomial[0] + arb(0, error))
        inverse_bound = (1 / (1 - beta)).upper() if beta < 1 else None
        disk_error = (inverse_bound * residual_norm).upper() if inverse_bound is not None else None
        gaps = [b - a for a, b in zip(ranges, ranges[1:])]
        separated = disk_error is not None and all(gap > 2 * disk_error for gap in gaps)
        ground_residual = sum((x * x for x in residual_bounds[0]), arb(0)).sqrt().upper()
        origin_poly = sum((basis[0, j] * families[0][j] for j in range(size)), arb_poly())
        origin_range = origin_poly[0] + arb(0, polynomial_bound(origin_poly - origin_poly[0], radius))
        distance = None
        origin_lower = None
        exact_origin_lower = None
        profile_error = None
        positive_ground = False
        if separated:
            clearance = ranges[1] - disk_error - ranges[0]
            if not clearance > 0:
                raise ArithmeticError('uniform ground clearance unresolved')
            # Candidate norm >=1: its anchor coordinate is identically one.
            distance = (arb(2).sqrt() * ground_residual / clearance.lower()).upper()
            positive_ground = ranges[0] - disk_error > 0
            origin_lower = (origin_range.lower() / candidate_norm).lower()
            if origin_lower > distance:
                exact_origin_lower = (origin_lower - distance).lower()
                strip_height = arb(2) / 5
                argument = strip_height * length_upper
                weight = (argument.sinh() / argument).sqrt()
                profile_error = (weight * distance / (origin_lower - distance)
                                 * (1 + 1 / origin_lower)).upper()
        return {
            'status': ('certified_finite_uniform_even_eigenfamily' if separated else
                       'finite_eigenfamily_candidate_validation_unresolved'),
            'modes': size - 1, 'degree': degree, 'working_bits': 1024,
            'center_spectrum': [endpoints(x) for x in eigenvalues],
            'center_basis': [[endpoints(basis[i, j]) for j in range(size)] for i in range(size)],
            'ground_candidate_coefficients': [
                [str(row[k].mid().fmpq()) for k in range(degree + 1)] for row in families[0]],
            'ground_eigenvalue_candidate_coefficients': [str(lambdas[0][k].mid().fmpq())
                                                        for k in range(degree + 1)],
            'uniform_basis_drift_infinity_upper': str(beta.fmpq()),
            'uniform_candidate_residual_infinity_upper': str(residual_norm.fmpq()),
            'uniform_candidate_eigenvalue_ranges': [endpoints(x) for x in ranges],
            'uniform_inverse_basis_infinity_upper': str(inverse_bound.fmpq()) if inverse_bound is not None else None,
            'uniform_eigenvalue_disk_radius_upper': str(disk_error.fmpq()) if disk_error is not None else None,
            'uniform_adjacent_candidate_gap_intervals': [endpoints(x) for x in gaps],
            'uniform_ground_residual_euclidean_upper': str(ground_residual.fmpq()),
            'ground_candidate_origin_range': endpoints(origin_range),
            'uniform_unit_ground_distance_upper': str(distance.fmpq()) if distance is not None else None,
            'positive_even_ground_certified': bool(positive_ground),
            'uniform_unit_candidate_origin_lower': str(origin_lower.fmpq()) if origin_lower is not None else None,
            'uniform_exact_unit_even_ground_origin_lower': str(exact_origin_lower.fmpq()) if exact_origin_lower is not None else None,
            'strip_height': '2/5',
            'uniform_origin_normalized_strip_profile_error_upper': str(profile_error.fmpq()) if profile_error is not None else None,
            'scope': 'Finite even eigenfamily; profile transfer additionally requires a protected origin. No odd-parity comparison is asserted.',
            'remaining': 'Odd-parity gate, ground-profile derivative integration, all-support/all-rank budget, Xi identification, and RH.',
        }


def _translate(polynomial: arb_poly, offset: arb) -> arb_poly:
    result = arb_poly()
    linear = arb_poly([offset, 1])
    for coefficient in reversed(polynomial.coeffs()):
        result = result * linear + coefficient
    return result


def certify(saved: dict, subdivisions: int = 32) -> dict:
    if saved.get('status') != 'certified_weil_entry_taylor_cell_not_ground_profile_budget':
        raise ValueError('certified whole-cell Weil Taylor matrix required')
    if type(subdivisions) is not int or subdivisions < 1:
        raise ValueError('positive integer subdivision count required')
    with ctx.workprec(1024):
        matrices = [arb_mat([[box(x) for x in row] for row in matrix])
                    for matrix in saved['even_matrix_coefficients']]
        size, degree = saved['modes'] + 1, saved['degree']
        half_width = Fraction(saved['cell_half_width'])
        radius = ball(half_width)
        polynomials = [[arb_poly([matrix[i, j].mid() for matrix in matrices])
                        for j in range(size)] for i in range(size)]
        coefficient_error = max(sum((sum((matrix[i, j].rad() * radius**k
                                          for k, matrix in enumerate(matrices)), arb(0))
                                     for j in range(size)), arb(0)).upper()
                                for i in range(size))
        truncation = ball(saved['even_value_operator_remainder_upper']) + coefficient_error
        cells = []
        for cell in range(subdivisions):
            offset = -half_width + Fraction(2 * cell + 1, subdivisions) * half_width
            translated = [[_translate(poly, ball(offset)) for poly in row] for row in polynomials]
            local_matrices = [arb_mat([[translated[i][j][k] for j in range(size)]
                                       for i in range(size)]) for k in range(degree + 1)]
            result = _validate(local_matrices, ball(half_width / subdivisions), truncation, degree,
                               arb(saved['upper_prime_power']).log())
            result.update({'index': cell, 'center_offset': str(offset),
                           'half_width': str(half_width / subdivisions)})
            cells.append(result)
        passed = all(cell['status'] == 'certified_finite_uniform_even_eigenfamily' for cell in cells)
        transfers = all(cell['uniform_origin_normalized_strip_profile_error_upper'] is not None for cell in cells)
        return {
            'status': ('certified_finite_whole_cell_even_eigenfamily' if passed else
                       'whole_cell_eigenfamily_validation_unresolved'),
            'lower_prime_power': saved['lower_prime_power'],
            'upper_prime_power': saved['upper_prime_power'], 'modes': saved['modes'],
            'degree': degree, 'working_bits': 1024, 'subdivisions': subdivisions,
            'log_support_center': saved['log_support_center'],
            'cell_half_width': saved['cell_half_width'],
            'matrix_coefficient_rounding_operator_error_upper': str(coefficient_error.fmpq()),
            'uniform_matrix_approximation_operator_error_upper': str(truncation.upper().fmpq()),
            'certified_subcells': sum(cell['status'] == 'certified_finite_uniform_even_eigenfamily' for cell in cells),
            'all_origin_strip_transfers_certified': transfers,
            'all_even_ground_eigenvalues_positive': all(cell['positive_even_ground_certified'] for cell in cells),
            'uniform_strip_profile_error_upper': str(max(ball(cell['uniform_origin_normalized_strip_profile_error_upper'])
                                                         for cell in cells).fmpq()) if transfers else None,
            'cells': cells,
            'scope': 'Complete finite support-cell cover; each eigenfamily requires all invertibility and spectral separation gates.',
            'remaining': 'All-support/all-rank profile budget, Xi identification, theta-curvature argument, and RH.',
        }


def run(path: Path, subdivisions: int = 32) -> dict:
    raw = path.read_bytes()
    saved = json.loads(raw)
    source_dir = Path(__file__).parent
    for name, digest in saved['source_hashes'].items():
        if hashlib.sha256((source_dir / name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale Taylor source: ' + name)
    result = certify(saved, subdivisions)
    result['input_sha256'] = hashlib.sha256(raw).hexdigest()
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--taylor', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--subdivisions', type=int, default=32)
    args = parser.parse_args()
    result = run(args.taylor, args.subdivisions)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])
    print('certified subcells', result['certified_subcells'], '/', result['subdivisions'])


if __name__ == '__main__':
    main()
