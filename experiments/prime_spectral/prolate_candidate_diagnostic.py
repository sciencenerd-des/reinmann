"""Floating prolate projection and exact finite Weil Rayleigh-gate audit.

The prolate eigenfunctions and quadrature are floating diagnostics.  The
Rayleigh inequality is certified only for the explicit rounded coefficient
vector recorded in the output, not for the exact prolate projection.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from math import isqrt
import json
from pathlib import Path


def _legendre_a(index: int) -> float:
    if index == 0:
        return 0.0
    return index / ((2 * index - 1) * (2 * index + 1)) ** 0.5


def project_candidate(cutoff: int, modes: int, legendre_terms: int,
                      quadrature_nodes: int) -> dict:
    """Project E(h_lambda) onto the centered orthonormal cosine basis."""
    import numpy as np
    from numpy.polynomial.legendre import leggauss, legval
    from scipy.integrate import solve_ivp
    from scipy.linalg import eigh_tridiagonal

    if cutoff < 2 or modes < 1 or legendre_terms < 3 or quadrature_nodes < 8:
        raise ValueError('invalid prolate projection parameters')
    length = float(np.log(cutoff))
    lam = float(np.sqrt(cutoff))
    angular = 2 * np.pi * cutoff
    degrees = 2 * np.arange(legendre_terms)
    diagonal = np.array([
        ell * (ell + 1) + angular**2 *
        (_legendre_a(ell + 1)**2 + _legendre_a(ell)**2)
        for ell in degrees
    ])
    off_diagonal = np.array([
        angular**2 * _legendre_a(ell + 1) * _legendre_a(ell + 2)
        for ell in degrees[:-1]
    ])
    eigenvalues, eigenvectors = eigh_tridiagonal(
        diagonal, off_diagonal, select='i', select_range=(0, 2))
    h0, h4 = eigenvectors[:, 0], eigenvectors[:, 2]
    ode_check = 0.0
    for column in (0, 2):
        legendre_coefficients = np.zeros(2 * legendre_terms - 1)
        legendre_coefficients[::2] = eigenvectors[:, column] * np.sqrt(
            (2 * degrees + 1) / 2)
        center = legval(0, legendre_coefficients)
        eigenvalue = eigenvalues[column]
        def ode(z, state):
            return [state[1],
                    (2 * z * state[1] + (angular**2 * z**2 - eigenvalue) * state[0])
                    / (1 - z**2)]
        solution = solve_ivp(ode, (0, 0.4), (1.0, 0.0), method='DOP853',
                             rtol=1e-12, atol=1e-14, dense_output=True)
        if not solution.success:
            raise ArithmeticError('prolate ODE cross-check failed')
        for z in (0.05, 0.1, 0.2, 0.3, 0.4):
            ode_check = max(ode_check, abs(
                legval(z, legendre_coefficients) / center - solution.sol(z)[0]))
    # Only the degree-zero normalized Legendre function has nonzero integral.
    h = h4 - (h4[0] / h0[0]) * h0
    coefficients = np.zeros(2 * legendre_terms - 1)
    coefficients[::2] = h * np.sqrt((2 * degrees + 1) / 2)

    def k_at(log_u):
        u = np.exp(log_u)
        value = np.zeros_like(u)
        for n in range(1, cutoff + 1):
            present = n * u <= lam
            value[present] += legval(n * u[present] / lam, coefficients)
        return np.sqrt(u) * value

    nodes, weights = leggauss(quadrature_nodes)
    thresholds = sorted(float(np.log(lam / n)) for n in range(1, cutoff + 1))
    projected = np.zeros(modes + 1)
    full_norm_squared = 0.0
    symmetry_squared = 0.0
    for left, right in zip(thresholds[:-1], thresholds[1:]):
        t = (left + right) / 2 + (right - left) * nodes / 2
        integration_weights = (right - left) * weights / 2
        k = k_at(t)
        projected[0] += np.sum(integration_weights * k) / np.sqrt(length)
        for mode in range(1, modes + 1):
            projected[mode] += np.sqrt(2 / length) * np.sum(
                integration_weights * k *
                np.cos(2 * np.pi * mode * (t + length / 2) / length))
        full_norm_squared += np.sum(integration_weights * k**2)
        symmetry_squared += np.sum(integration_weights * (k - k_at(-t))**2)
    projection_norm = float(np.linalg.norm(projected))
    if not projection_norm > 0 or not full_norm_squared > 0:
        raise ArithmeticError('zero numerical prolate candidate')
    unit = projected / projection_norm
    if unit[0] < 0:
        unit = -unit
    return {
        'unit_coefficients': [float(x) for x in unit],
        'prolate_even_eigenvalues': [float(x) for x in eigenvalues],
        'reflection_defect_ratio': float(np.sqrt(symmetry_squared / full_norm_squared)),
        'projected_l2_fraction': float(projection_norm / np.sqrt(full_norm_squared)),
        'zero_integral_coefficient': float(h[0]),
        'ode_crosscheck_max_abs_error_to_0p4': float(ode_check),
    }


def _interval(record: dict) -> tuple[Fraction, Fraction]:
    lower, upper = Fraction(record['lo']), Fraction(record['hi'])
    if lower > upper:
        raise ValueError('reversed matrix enclosure')
    return lower, upper


def _add(a, b):
    return a[0] + b[0], a[1] + b[1]


def _multiply(a, b):
    values = [x * y for x in a for y in b]
    return min(values), max(values)


def _square(a):
    if a[0] <= 0 <= a[1]:
        return Fraction(0), max(a[0] * a[0], a[1] * a[1])
    values = a[0] * a[0], a[1] * a[1]
    return min(values), max(values)


def certified_rayleigh(certificate: dict, rounded_coefficients: list[str]) -> dict:
    """Exact rational Rayleigh and residual intervals for the recorded vector."""
    if certificate.get('status') != 'certified_finite_weil_gates':
        raise ValueError('finite Weil gate certificate required')
    modes = certificate['modes']
    if len(rounded_coefficients) != modes + 1:
        raise ValueError('candidate dimension mismatch')
    vector = [Fraction(x) for x in rounded_coefficients]
    norm_squared = sum(x * x for x in vector)
    if norm_squared == 0:
        raise ValueError('zero candidate vector')
    matrix = [[_interval(x) for x in row] for row in certificate['matrix']]
    if len(matrix) != 2 * modes + 1 or any(len(row) != len(matrix) for row in matrix):
        raise ValueError('matrix dimension mismatch')
    scale = 10**60
    root = isqrt(2 * scale * scale)
    root_two = Fraction(root, scale), Fraction(root + 1, scale)
    even = []
    for i in range(modes + 1):
        row = []
        for j in range(modes + 1):
            if i == 0 and j == 0:
                entry = matrix[modes][modes]
            elif i == 0:
                entry = _multiply(root_two, matrix[modes][modes + j])
            elif j == 0:
                entry = _multiply(root_two, matrix[modes + i][modes])
            else:
                entry = _add(matrix[modes + i][modes + j],
                             matrix[modes + i][modes - j])
            row.append(entry)
        even.append(row)
    total = Fraction(0), Fraction(0)
    for i in range(modes + 1):
        for j in range(modes + 1):
            factor = vector[i] * vector[j]
            total = _add(total, _multiply((factor, factor), even[i][j]))
    rayleigh = total[0] / norm_squared, total[1] / norm_squared
    residual_squared = Fraction(0), Fraction(0)
    for i, row in enumerate(even):
        image = Fraction(0), Fraction(0)
        for entry, coordinate in zip(row, vector):
            image = _add(image, _multiply(entry, (coordinate, coordinate)))
        rayleigh_coordinate = _multiply(rayleigh, (vector[i], vector[i]))
        residual = (image[0] - rayleigh_coordinate[1],
                    image[1] - rayleigh_coordinate[0])
        residual_squared = _add(residual_squared, _square(residual))
    residual_squared = (residual_squared[0] / norm_squared,
                        residual_squared[1] / norm_squared)
    second = _interval(certificate['second_even_eigenvalue'])
    if second[0] <= 0:
        raise ValueError('positive second eigenvalue not certified')
    clearance = second[0] - rayleigh[1]
    return {
        'rayleigh_interval': {'lo': str(rayleigh[0]), 'hi': str(rayleigh[1])},
        'residual_norm_squared_interval': {
            'lo': str(residual_squared[0]), 'hi': str(residual_squared[1])},
        'second_even_interval': {'lo': str(second[0]), 'hi': str(second[1])},
        'rayleigh_below_second': clearance > 0,
        'rayleigh_above_second': rayleigh[0] > second[1],
        'lower_excess_ratio': str(rayleigh[0] / second[1]),
        'residual_over_clearance_squared_upper': (
            str(residual_squared[1] / (clearance * clearance))
            if clearance > 0 else None),
    }


def run(certificate_path: Path, legendre_terms: int = 80,
        quadrature_nodes: int = 100) -> dict:
    raw = certificate_path.read_bytes()
    certificate = json.loads(raw)
    for name, digest in certificate['source_hashes'].items():
        path = Path(__file__).with_name(name)
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError('stale finite Weil certificate source')
    cutoff, modes = certificate['cutoff'], certificate['modes']
    primary = project_candidate(cutoff, modes, legendre_terms, quadrature_nodes)
    other = [project_candidate(cutoff, modes, terms, nodes)
             for terms, nodes in ((48, 64), (120, 160))]
    max_coordinate_change = max(
        abs(a - b)
        for run in other for a, b in zip(
            primary['unit_coefficients'], run['unit_coefficients']))
    rounded = [format(x, '.17g') for x in primary['unit_coefficients']]
    gate = certified_rayleigh(certificate, rounded)
    return {
        'schema_version': 1,
        'status': ('rounded_finite_prolate_candidate_above_second_eigenvalue'
                   if gate['rayleigh_above_second'] else 'finite_gate_unresolved'),
        'cutoff': cutoff, 'modes': modes,
        'lambda_squared': cutoff,
        'legendre_terms': legendre_terms,
        'quadrature_nodes_per_piece': quadrature_nodes,
        'floating_projection': primary,
        'max_coordinate_refinement_change': max_coordinate_change,
        'rounded_candidate_coefficients': rounded,
        'exact_rounded_candidate_gate': gate,
        'input_sha256': hashlib.sha256(raw).hexdigest(),
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': ('The exact rational gate concerns the rounded vector in this finite '
                  'matrix. The prolate projection and convergence checks use floating '
                  'arithmetic and do not enclose the exact prolate eigenfunction.'),
        'remaining': ('No residual-over-gap decay or finite-to-continuous Weil '
                      'comparison is proved; RH remains open.'),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--legendre-terms', type=int, default=80)
    parser.add_argument('--quadrature-nodes', type=int, default=100)
    args = parser.parse_args()
    result = run(args.certificate, args.legendre_terms, args.quadrature_nodes)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])
    print('rayleigh/second lower:', float(Fraction(
        result['exact_rounded_candidate_gate']['lower_excess_ratio'])))


if __name__ == '__main__':
    main()
