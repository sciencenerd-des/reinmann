"""Certified spectral-band pairing for one nested prime Weil rank step.

The Rump eigenpairs are finite interval certificates. No all-rank bound is
inferred from the finite alignment calculation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, acb, arb_mat, acb_mat, ctx

from certified_mode_comparison import box
from certified_weil import endpoints, inertia
from ground_schur import origin_schur_vector
from rank_schur_recurrence import _even_matrix, _tail_fourier, _lower_abs, _upper_abs


def compare(first: dict, second: dict) -> dict:
    if (first.get('status') != 'certified_finite_weil_gates'
            or second.get('status') != 'certified_finite_weil_gates'):
        raise ValueError('two certified finite Weil gates required')
    if first['cutoff'] != second['cutoff'] or not first['modes'] < second['modes']:
        raise ValueError('nested modes at the same support required')
    small, large = first['modes'], second['modes']
    old_matrix, new_matrix = _even_matrix(first), _even_matrix(second)
    if not all((old_matrix[i][j] - new_matrix[i][j]).contains(0)
               for i in range(small + 1) for j in range(small + 1)):
        raise ArithmeticError('nested Weil entries disagree')
    old_vector, _ = origin_schur_vector(first)
    old_lam = box(first['smallest_even_eigenvalue'])
    new_lam = box(second['smallest_even_eigenvalue'])
    shift = old_lam - new_lam
    if not shift > 0:
        raise ArithmeticError('strict nested ground-eigenvalue shift unresolved')
    matrix = [[new_matrix[i][j] - (new_lam if i == j else 0)
               for j in range(1, large + 1)] for i in range(1, large + 1)]
    if inertia(matrix)[0] != 0:
        raise ArithmeticError('positive origin-constrained block unresolved')
    operator = arb_mat(matrix)
    source = ([shift * old_vector[index] for index in range(1, small + 1)]
              + [new_matrix[index][0]
                 + sum((new_matrix[index][j] * old_vector[j]
                        for j in range(1, small + 1)), arb(0))
                 for index in range(small + 1, large + 1)])
    source_matrix = arb_mat([[value] for value in source])
    solution = operator.solve(source_matrix)

    values, vectors = acb_mat(operator).eig(right=True, algorithm='rump')
    if len(values) != large:
        raise ArithmeticError('complete constrained spectrum unresolved')
    order = sorted(range(large), key=lambda index: values[index].real.mid())
    if not all(values[index].is_finite() and values[index].imag.contains(0)
               and values[index].real > 0 for index in order):
        raise ArithmeticError('positive real constrained spectrum unresolved')
    if not all(values[left].real < values[right].real
               for left, right in zip(order, order[1:])):
        raise ArithmeticError('simple ordered constrained spectrum unresolved')
    modes = []
    for index in order:
        raw = [vectors[row, index] for row in range(large)]
        if not all(value.is_finite() and value.imag.contains(0) for value in raw):
            raise ArithmeticError('real constrained eigenvector unresolved')
        real = [value.real for value in raw]
        norm = sum((value**2 for value in real), arb(0)).sqrt()
        if not norm > 0:
            raise ArithmeticError('nonzero constrained eigenvector unresolved')
        modes.append((values[index].real, [value / norm for value in real]))
    for left in range(large):
        for right in range(left + 1, large):
            if not sum((a*b for a, b in zip(modes[left][1], modes[right][1])),
                       arb(0)).contains(0):
                raise ArithmeticError('constrained eigenvector orthogonality unresolved')

    length = arb(first['cutoff']).log()
    output = {}
    for name, argument in (('real_4', acb(4)), ('real_8', acb(8)),
                           ('imag_1', acb(0, 1))):
        functional = []
        for index in range(large):
            basis = [arb(0)] * large
            basis[index] = arb(1)
            value = _tail_fourier(basis, length, argument)
            if not value.imag.contains(0):
                raise ArithmeticError('even Fourier functional reality unresolved')
            functional.append(value.real)
        terms = []
        absolute_upper = Fraction(0)
        dual_energy = arb(0)
        residual_energy = arb(0)
        for eigenvalue, vector in modes:
            projection_f = sum((a*b for a, b in zip(vector, functional)), arb(0))
            projection_r = sum((a*b for a, b in zip(vector, source)), arb(0))
            dual_energy += projection_f**2 / eigenvalue
            residual_energy += projection_r**2 / eigenvalue
            term = -projection_f * projection_r / eigenvalue
            bound = _upper_abs(term)
            absolute_upper += bound
            terms.append({'eigenvalue': endpoints(eigenvalue),
                          'signed_profile_term': endpoints(term),
                          'absolute_term_upper': str(bound)})
        signed = sum((box(term['signed_profile_term']) for term in terms), arb(0))
        direct_complex = -_tail_fourier(
            [solution[index, 0] for index in range(large)], length, argument)
        if not direct_complex.imag.contains(0):
            raise ArithmeticError('direct profile change reality unresolved')
        direct = direct_complex.real
        if not (signed - direct).contains(0):
            raise ArithmeticError('spectral pairing disagrees with direct solve')
        signed_lower = _lower_abs(signed)
        if signed_lower > absolute_upper:
            raise ArithmeticError('spectral absolute bound contradicts signed sum')
        cauchy = (dual_energy * residual_energy).sqrt()
        if not cauchy > 0:
            raise ArithmeticError('positive global Cauchy bound unresolved')
        output[name] = {
            'eigenmode_terms': terms,
            'direct_profile_change': endpoints(direct),
            'signed_spectral_profile_change': endpoints(signed),
            'spectral_absolute_sum_upper': str(absolute_upper),
            'alignment_to_actual_ratio_upper': (
                str(absolute_upper / signed_lower) if signed_lower > 0 else None),
            'global_cauchy_upper': str(cauchy.upper().fmpq()),
            'spectral_improves_global_cauchy_certified': bool(
                cauchy - arb(str(absolute_upper)) > 0),
        }
    return {
        'status': 'certified_finite_spectral_alignment_not_uniform',
        'cutoff': first['cutoff'], 'mode_pair': [small, large],
        'profile_change': output,
        'scope': ('One nested finite Weil pair. The spectral-band inequality '
                  'has no verified support-uniform or all-rank bound.'),
    }


def run(first_path: Path, second_path: Path) -> dict:
    source_dir = Path(__file__).parent
    inputs = []
    for path in (first_path, second_path):
        raw = path.read_bytes()
        certificate = json.loads(raw)
        for name, digest in certificate['source_hashes'].items():
            if hashlib.sha256((source_dir / name).read_bytes()).hexdigest() != digest:
                raise ValueError('stale finite Weil certificate source: ' + name)
        inputs.append((raw, certificate))
    with ctx.workprec(512):
        result = compare(inputs[0][1], inputs[1][1])
    result['input_sha256'] = [hashlib.sha256(raw).hexdigest() for raw, _ in inputs]
    result['source_hashes'] = {
        name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
        for name in ('spectral_alignment.py', 'rank_schur_recurrence.py',
                     'ground_schur.py', 'certified_mode_comparison.py',
                     'certified_weil.py')}
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
    print(result['status'])


if __name__ == '__main__':
    main()
