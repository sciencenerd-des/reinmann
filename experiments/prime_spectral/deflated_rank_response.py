"""Certified signed low-mode extraction for finite Weil rank responses.

The projected coupled source is retained through the low-mode solve.
Only its complementary positive energy is transferred by Cauchy--Schwarz.
This supplies finite bounds and an all-rank interface, not its hypotheses.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from flint import acb, arb, arb_mat, ctx
from certified_mode_comparison import box
from certified_weil import endpoints
from eigenvalue_response import _fourier_functional
from ground_schur import origin_schur_vector
from rank_schur_recurrence import _even_matrix
from weil_eigenfamily import center_basis


def square(value):
    if value.contains(0):
        upper = (abs(value).upper() * abs(value).upper()).upper()
        return arb(0).union(upper)
    return value * value


def dot(left, right):
    return sum((x * y for x, y in zip(left, right)), arb(0))


def deflate(operator, source, energy, count, functionals):
    size = operator.nrows()
    if (operator.ncols() != size or len(source) != size or type(count) is not int
            or not 0 <= count < size):
        raise ValueError('square constrained block, matching source and at least one retained complementary mode required')
    if any(not value.is_finite() for value in source) or not energy > 0:
        raise ArithmeticError('finite source and positive rank energy required')
    if any(endpoints(operator[i, j]) != endpoints(operator[j, i])
           for i in range(size) for j in range(i)):
        raise ValueError('symmetric constrained-matrix enclosure required')
    values, basis = center_basis(operator)
    if not all(value > 0 for value in values):
        raise ArithmeticError('positive complete constrained spectrum required')
    projections = [sum((basis[i, k] * source[i] for i in range(size)), arb(0)) for k in range(size)]
    modal_energy = [square(a) / mu for a, mu in zip(projections, values)]
    projected_total = sum(modal_energy, arb(0))
    if not projected_total.overlaps(energy):
        raise ArithmeticError('coupled energy and spectral energy disagree')
    removed_energy = sum(modal_energy[:count], arb(0))
    complement = sum(modal_energy[count:], arb(0))
    difference = energy - removed_energy
    if not difference.overlaps(complement):
        raise ArithmeticError('complementary energy identity disagrees')
    # Both are enclosures of the same nonnegative complementary energy.
    complement_upper = min(complement.upper(), difference.upper())
    if not complement_upper >= 0:
        raise ArithmeticError('nonnegative complementary energy unresolved')
    low_norm_squared = sum((square(a / mu) for a, mu in zip(projections[:count], values[:count])), arb(0)).upper()
    norm_squared_bound = (low_norm_squared + complement_upper / values[count].lower()).upper()
    low_vector = [sum((basis[i, k] * projections[k] / values[k] for k in range(count)), arb(0)) for i in range(size)]
    profiles = {}
    for label, functional in functionals.items():
        if len(functional) != size:
            raise ValueError('Fourier functional dimension mismatch')
        projected_functional = [sum((basis[i, k] * functional[i] for i in range(size)), arb(0)) for k in range(size)]
        low_pairing = dot(functional, low_vector)
        dual_total = sum((square(f) / mu for f, mu in zip(projected_functional, values)), arb(0))
        dual_complement = sum((square(f) / mu for f, mu in zip(projected_functional[count:], values[count:])), arb(0))
        radius = (complement_upper * dual_complement.upper()).sqrt().upper()
        # Rank profile change is minus the source-inverse pairing.
        interval = -low_pairing + arb(0, radius)
        full_pairing = -sum((a * f / mu for a, f, mu in zip(projections, projected_functional, values)), arb(0))
        if not interval.overlaps(full_pairing):
            raise ArithmeticError('deflated profile interval disagrees with full spectral pairing')
        profiles[label] = {
            'signed_low_mode_profile_change': endpoints(-low_pairing),
            'complementary_fourier_dual_energy': endpoints(dual_complement),
            'complementary_profile_radius_upper': str(radius.fmpq()),
            'deflated_profile_change_interval': endpoints(interval),
            'deflated_absolute_profile_upper': str((abs(low_pairing).upper() + radius).upper().fmpq()),
            'unseparated_energy_profile_upper': str((energy.upper() * dual_total.upper()).sqrt().upper().fmpq()),
            'full_spectral_profile_change_check': endpoints(full_pairing),
        }
    return {
        'deflated_modes': count,
        'constrained_spectrum': [endpoints(value) for value in values],
        'coupled_source_eigenprojections': [endpoints(value) for value in projections],
        'exact_rank_energy_interval': endpoints(energy),
        'independent_total_modal_energy_interval': endpoints(projected_total),
        'removed_low_mode_energy_interval': endpoints(removed_energy),
        'complementary_energy_interval': endpoints(complement),
        'complementary_energy_upper_used': str(complement_upper.fmpq()),
        'complementary_spectral_lower': str(values[count].lower().fmpq()),
        'low_mode_inverse_vector_norm_squared_upper': str(low_norm_squared.fmpq()),
        'deflated_total_inverse_vector_norm_upper': str(norm_squared_bound.sqrt().upper().fmpq()),
        'profile_change': profiles,
    }


def compare(first, second, count=2, sigma=Fraction(1)):
    if (first.get('status') != 'certified_finite_weil_gates'
            or second.get('status') != 'certified_finite_weil_gates'):
        raise ValueError('two certified finite Weil gates required')
    small, large = first['modes'], second['modes']
    if first['cutoff'] != second['cutoff'] or not 0 < small < large:
        raise ValueError('same support and strictly increasing positive ranks required')
    sigma = Fraction(sigma)
    if sigma < 0:
        raise ValueError('nonnegative rational strip height required')
    old_matrix, new_matrix = _even_matrix(first), _even_matrix(second)
    if any(not (old_matrix[i][j] - new_matrix[i][j]).contains(0)
           for i in range(small + 1) for j in range(small + 1)):
        raise ArithmeticError('nested principal blocks disagree')
    old_vector, _ = origin_schur_vector(first)
    old_lambda, new_lambda = box(first['smallest_even_eigenvalue']), box(second['smallest_even_eigenvalue'])
    shift = old_lambda - new_lambda
    if not shift > 0:
        raise ArithmeticError('positive nested least-eigenvalue shift required')
    operator = arb_mat([[new_matrix[i][j] - (new_lambda if i == j else 0)
                         for j in range(1, large + 1)] for i in range(1, large + 1)])
    source = ([shift * old_vector[i] for i in range(1, small + 1)]
              + [new_matrix[i][0] + sum((new_matrix[i][j] * old_vector[j] for j in range(1, small + 1)), arb(0))
                 for i in range(small + 1, large + 1)])
    energy = shift * dot(old_vector, old_vector)
    length = arb(first['cutoff']).log()
    functionals = {name: _fourier_functional(large, length, z)[1:] for name, z in
                   (('real_4', acb(4)), ('real_8', acb(8)), ('imag_1', acb(0, 1)))}
    result = deflate(operator, source, energy, count, functionals)
    argument = (arb(sigma.numerator) / sigma.denominator) * length
    weight = arb(1) if sigma == 0 else (argument.sinh() / argument).sqrt()
    result.update({
        'status': 'certified_finite_signed_deflated_rank_response_not_all_rank_budget',
        'cutoff': first['cutoff'], 'mode_pair': [small, large], 'working_bits': 1024,
        'ground_eigenvalue_shift': endpoints(shift), 'strip_height': str(sigma),
        'uniform_strip_rank_increment_upper': str((weight * arb(result['deflated_total_inverse_vector_norm_upper'])).upper().fmpq()),
        'scope': 'One finite rank transition; full real-part uniformity on the saved strip comes from the Fourier functional norm and the deflated inverse-vector bound.',
        'remaining': 'Uniform low-mode projection control, positive origin-normalized infinite ground, cumulative support/rank budget, Xi identification, theta curvature and RH.'})
    return result


def run(first_path, second_path, count=2, sigma=Fraction(1)):
    raw = [path.read_bytes() for path in (first_path, second_path)]
    inputs = [json.loads(value) for value in raw]
    src = Path(__file__).parent
    for certificate in inputs:
        for name, digest in certificate['source_hashes'].items():
            if hashlib.sha256((src / name).read_bytes()).hexdigest() != digest:
                raise ValueError('stale Weil source: ' + name)
    with ctx.workprec(1024):
        result = compare(*inputs, count, sigma)
    result['input_sha256'] = [hashlib.sha256(value).hexdigest() for value in raw]
    result['source_hashes'] = {name: hashlib.sha256((src / name).read_bytes()).hexdigest() for name in
                               ('deflated_rank_response.py', 'weil_eigenfamily.py', 'ground_schur.py', 'rank_schur_recurrence.py',
                                'eigenvalue_response.py', 'certified_mode_comparison.py', 'certified_weil.py')}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first', type=Path, required=True)
    parser.add_argument('--second', type=Path, required=True)
    parser.add_argument('--deflate', type=int, default=2)
    parser.add_argument('--sigma', type=Fraction, default=Fraction(1))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.first, args.second, args.deflate, args.sigma)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])
    print(float(Fraction(result['uniform_strip_rank_increment_upper'])))


if __name__ == '__main__':
    main()
