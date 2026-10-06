"""Certified coupled ground-profile change between two support cutoffs.

The even Fourier dimensions agree, but their support lengths and Fourier
functionals differ. This is a finite identity, not a uniform support bound.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb, acb_mat, arb, arb_mat, ctx

from certified_weil import certified_matrix, endpoints, inertia
from eigenvalue_response import _fourier_functional
from isolated_kernel import isolated_spectrum, run as isolated_run


def _dot(left: list[arb], right: list[arb]) -> arb:
    return sum((a * b for a, b in zip(left, right)), arb(0))


def _spectral_solve(matrix: arb_mat, source: list[arb]) -> tuple[list[arb], arb]:
    values, vectors = acb_mat(matrix).eig(right=True, algorithm='rump')
    size = len(source)
    if len(values) != size:
        raise ArithmeticError('complete constrained spectrum unresolved')
    ordered = sorted(range(size), key=lambda index: values[index].real.mid())
    if not all(values[index].is_finite() and values[index].imag.contains(0)
               and values[index].real > 0 for index in ordered):
        raise ArithmeticError('positive real constrained spectrum unresolved')
    if not all(values[left].real < values[right].real
               for left, right in zip(ordered, ordered[1:])):
        raise ArithmeticError('simple constrained spectrum unresolved')
    result = [arb(0) for _ in range(size)]
    units = []
    for index in ordered:
        raw = [vectors[row, index] for row in range(size)]
        if not all(value.is_finite() and value.imag.contains(0) for value in raw):
            raise ArithmeticError('real constrained eigenvector unresolved')
        real = [value.real for value in raw]
        norm = _dot(real, real).sqrt()
        if not norm > 0:
            raise ArithmeticError('nonzero constrained eigenvector unresolved')
        unit = [value / norm for value in real]
        for earlier in units:
            if not _dot(earlier, unit).contains(0):
                raise ArithmeticError('constrained eigenvector orthogonality unresolved')
        units.append(unit)
        coefficient = _dot(unit, source) / values[index].real
        result = [old + value * coefficient for old, value in zip(result, unit)]
    for row in range(size):
        if not (sum((matrix[row, col] * result[col] for col in range(size)),
                    arb(0)) - source[row]).contains(0):
            raise ArithmeticError('constrained spectral solve residual unresolved')
    return result, values[ordered[0]].real


def certify(first: dict, second: dict) -> dict:
    if (first.get('status') != 'certified_finite_isolated_prime_kernel_not_uniform'
            or second.get('status') != 'certified_finite_isolated_prime_kernel_not_uniform'):
        raise ValueError('two isolated finite Weil certificates required')
    if first['modes'] != second['modes'] or first['cutoff'] >= second['cutoff']:
        raise ValueError('same rank and increasing support required')
    modes = first['modes']
    with ctx.workprec(1024):
        _, old, _ = certified_matrix(first['cutoff'], modes)
        _, new, _ = certified_matrix(second['cutoff'], modes)
        old_values, old_raw = isolated_spectrum(old)
        new_values, new_raw = isolated_spectrum(new)
        for values, stored in ((old_values, first), (new_values, second)):
            for value, enclosure in zip(values, stored['even_spectrum']):
                if (Fraction(str(value.upper().fmpq())) < Fraction(enclosure['lo'])
                        or Fraction(str(value.lower().fmpq())) > Fraction(enclosure['hi'])):
                    raise ValueError('recomputed Weil spectrum disjoint from stored enclosure')
        if old_raw[0].contains(0) or new_raw[0].contains(0):
            raise ArithmeticError('origin-normalized ground unresolved')
        old_vector = [arb(1)] + [entry / old_raw[0] for entry in old_raw[1:]]
        new_vector = [arb(1)] + [entry / new_raw[0] for entry in new_raw[1:]]
        old_lambda, new_lambda = old_values[0], new_values[0]
        constrained = [[new[i][j] - (new_lambda if i == j else 0)
                        for j in range(1, modes + 1)] for i in range(1, modes + 1)]
        if inertia(constrained)[0] != 0:
            raise ArithmeticError('new origin-constrained block not certified positive')
        operator = arb_mat(constrained)
        matrix_source = [
            new[i][0] - old[i][0]
            + sum(((new[i][j] - old[i][j]) * old_vector[j]
                   for j in range(1, modes + 1)), arb(0))
            for i in range(1, modes + 1)]
        shift_source = [(old_lambda - new_lambda) * old_vector[i]
                        for i in range(1, modes + 1)]
        coupled_source = [a + b for a, b in zip(matrix_source, shift_source)]
        spectral_solution, constrained_lowest = _spectral_solve(operator, coupled_source)
        coupled_change = [-value for value in spectral_solution]
        direct_solve = operator.solve(arb_mat([[value] for value in coupled_source]))
        direct_solve_change = [-direct_solve[index, 0] for index in range(modes)]
        direct_change = [new_vector[i] - old_vector[i]
                         for i in range(1, modes + 1)]
        if not all((a - b).contains(0) for a, b in zip(coupled_change, direct_change)):
            raise ArithmeticError('support recurrence disagrees with ground vectors')
        if not all((a - b).contains(0) for a, b in zip(direct_solve_change,
                                                       coupled_change)):
            raise ArithmeticError('spectral and direct constrained solves disagree')
        profiles = {}
        old_length = arb(first['cutoff']).log()
        new_length = arb(second['cutoff']).log()
        for name, argument in (('real_4', acb(4)), ('real_8', acb(8)),
                               ('imag_1', acb(0, 1))):
            old_functional = _fourier_functional(modes, old_length, argument)
            new_functional = _fourier_functional(modes, new_length, argument)
            basis_drift = _dot([a - b for a, b in zip(new_functional, old_functional)],
                               old_vector)
            vector_change = _dot(new_functional[1:], coupled_change)
            direct_inverse_change = _dot(new_functional[1:], direct_solve_change)
            direct_profile_change = (_dot(new_functional, new_vector)
                                     - _dot(old_functional, old_vector))
            if not (basis_drift + vector_change - direct_profile_change).contains(0):
                raise ArithmeticError('support profile decomposition disagrees')
            if not (direct_inverse_change - vector_change).contains(0):
                raise ArithmeticError('support spectral response disagrees with direct inverse')
            profiles[name] = {
                'basis_length_drift': endpoints(basis_drift),
                'coupled_ground_change': endpoints(vector_change),
                'direct_interval_inverse_ground_change': endpoints(direct_inverse_change),
                'total_support_step': endpoints(basis_drift + vector_change),
                'direct_profile_change': endpoints(direct_profile_change),
            }
        return {
            'status': 'certified_finite_coupled_support_step_not_uniform',
            'first_cutoff': first['cutoff'], 'second_cutoff': second['cutoff'],
            'modes': modes, 'working_bits': 1024,
            'first_ground_eigenvalue': endpoints(old_lambda),
            'second_ground_eigenvalue': endpoints(new_lambda),
            'new_origin_constrained_lowest_eigenvalue': endpoints(constrained_lowest),
            'matrix_perturbation_source': [endpoints(x) for x in matrix_source],
            'eigenvalue_shift_source': [endpoints(x) for x in shift_source],
            'coupled_source': [endpoints(x) for x in coupled_source],
            'coupled_coefficient_change': [endpoints(x) for x in coupled_change],
            'direct_coefficient_change': [endpoints(x) for x in direct_change],
            'profile_change': profiles,
            'scope': ('Exact support-step identity for two finite prime-defined '
                      'Weil matrices at equal Fourier rank, including Fourier basis drift.'),
            'remaining': ('No cumulative support bound, growing-rank estimate, '
                          'or Xi convergence is proved.'),
        }


def run(first_path: Path, second_path: Path) -> dict:
    first_raw, second_raw = first_path.read_bytes(), second_path.read_bytes()
    first, second = json.loads(first_raw), json.loads(second_raw)
    source_dir = Path(__file__).parent
    for saved in (first, second):
        for name, digest in saved['source_hashes'].items():
            if hashlib.sha256((source_dir / name).read_bytes()).hexdigest() != digest:
                raise ValueError('stale isolated Weil source: ' + name)
        if isolated_run(saved['cutoff'], saved['modes']) != saved:
            raise ValueError('isolated Weil certificate replay disagrees')
    result = certify(first, second)
    result['input_sha256'] = {
        'first_isolated_weil': hashlib.sha256(first_raw).hexdigest(),
        'second_isolated_weil': hashlib.sha256(second_raw).hexdigest(),
    }
    result['source_hashes'] = {
        name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
        for name in ('support_schur_recurrence.py', 'certified_weil.py',
                     'eigenvalue_response.py', 'isolated_kernel.py')}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first', type=Path, required=True)
    parser.add_argument('--second', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.first, args.second)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['first_cutoff'], result['second_cutoff'], result['modes'])


if __name__ == '__main__':
    main()
