"""Coupled origin-constrained recurrence for nested finite Weil spaces.

Only the finite saved matrices are certified. No summability or RH claim.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, acb, arb_mat, ctx

from certified_mode_comparison import box
from certified_weil import endpoints, inertia
from ground_schur import origin_schur_vector


def _even_matrix(certificate: dict) -> list[list[arb]]:
    modes = certificate['modes']
    full = [[box(value) for value in row] for row in certificate['matrix']]
    if len(full) != 2 * modes + 1 or any(len(row) != len(full) for row in full):
        raise ValueError('finite Weil matrix dimension mismatch')
    root_two = arb(2).sqrt()
    even = [[arb(0) for _ in range(modes + 1)] for _ in range(modes + 1)]
    even[0][0] = full[modes][modes]
    for i in range(1, modes + 1):
        even[0][i] = even[i][0] = root_two * full[modes][modes + i]
        for j in range(1, modes + 1):
            even[i][j] = full[modes + i][modes + j] + full[modes + i][modes - j]
    return even


def _tail_fourier(tail: list[arb], length: arb, z: acb) -> acb:
    """Centered Fourier functional on vectors with zeroth coordinate zero."""
    total = acb(0)
    for index, coordinate in enumerate(tail, 1):
        total += ((-1)**index * coordinate / arb(2).sqrt()
                  * ((arb.pi() * index - z * length / 2).sinc()
                     + (-arb.pi() * index - z * length / 2).sinc()))
    return total


def _lower_abs(value: arb) -> Fraction:
    if value.contains(0):
        return Fraction(0)
    return min(abs(Fraction(str(value.lower().fmpq()))),
               abs(Fraction(str(value.upper().fmpq()))))


def _upper_abs(value: arb) -> Fraction:
    return max(abs(Fraction(str(value.lower().fmpq()))),
               abs(Fraction(str(value.upper().fmpq()))))


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
    new_vector, _ = origin_schur_vector(second)
    old_lam = box(first['smallest_even_eigenvalue'])
    new_lam = box(second['smallest_even_eigenvalue'])
    shift = old_lam - new_lam
    if not shift > 0:
        raise ArithmeticError('strict nested ground-eigenvalue shift unresolved')
    constrained = [[new_matrix[i][j] - (new_lam if i == j else 0)
                    for j in range(1, large + 1)] for i in range(1, large + 1)]
    if inertia(constrained)[0] != 0:
        raise ArithmeticError('positive large origin-constrained block unresolved')
    shift_source = ([shift * old_vector[index] for index in range(1, small + 1)]
                    + [arb(0)] * (large - small))
    new_source = ([arb(0)] * small
                  + [new_matrix[index][0]
                     + sum((new_matrix[index][j] * old_vector[j]
                            for j in range(1, small + 1)), arb(0))
                     for index in range(small + 1, large + 1)])
    operator = arb_mat(constrained)
    solve = lambda values: operator.solve(arb_mat([[value] for value in values]))
    shift_solution, new_solution = solve(shift_source), solve(new_source)
    coupled_source = [a + b for a, b in zip(shift_source, new_source)]
    coupled_solution = solve(coupled_source)
    old_padded = old_vector[1:] + [arb(0)] * (large - small)
    if not all((coupled_solution[index, 0] - old_padded[index]
                + new_vector[index + 1]).contains(0) for index in range(large)):
        raise ArithmeticError('coupled rank recurrence disagrees with ground vectors')

    # Eliminate the old noncentral modes first. The resulting Schur energy
    # is the drop in the old scalar secular function at the new eigenvalue.
    old_block = arb_mat([row[:small] for row in constrained[:small]])
    bridge = arb_mat([[new_matrix[i][j] for j in range(small + 1, large + 1)]
                      for i in range(1, small + 1)])
    new_block = arb_mat([[constrained[i - 1][j - 1]
                          for j in range(small + 1, large + 1)]
                         for i in range(small + 1, large + 1)])
    old_coupling = arb_mat([[new_matrix[i][0]] for i in range(1, small + 1)])
    new_coupling = arb_mat([[new_matrix[i][0]] for i in range(small + 1, large + 1)])
    resolved_coupling = old_block.solve(old_coupling)
    resolved_bridge = old_block.solve(bridge)
    reduced_block = new_block - bridge.transpose() * resolved_bridge
    if inertia([[reduced_block[i, j] for j in range(large - small)]
                for i in range(large - small)])[0] != 0:
        raise ArithmeticError('positive reduced new-mode block unresolved')
    effective_coupling = new_coupling - bridge.transpose() * resolved_coupling
    new_tail = -reduced_block.solve(effective_coupling)
    old_tail = -resolved_coupling - resolved_bridge * new_tail
    if not (all((old_tail[i, 0] - new_vector[i + 1]).contains(0)
                for i in range(small))
            and all((new_tail[i, 0] - new_vector[small + i + 1]).contains(0)
                    for i in range(large - small))):
        raise ArithmeticError('reduced Schur vector disagrees with ground vector')
    coupling_energy = (effective_coupling.transpose()
                       * reduced_block.solve(effective_coupling))[0, 0]
    old_secular_drop = (new_matrix[0][0] - new_lam
                        - (old_coupling.transpose() * resolved_coupling)[0, 0])
    if not coupling_energy > 0 or not (old_secular_drop - coupling_energy).contains(0):
        raise ArithmeticError('positive secular coupling identity unresolved')
    resolvent_norm_squared = sum((resolved_coupling[i, 0]**2
                                  for i in range(small)), arb(0))
    old_norm_squared = sum((old_vector[i]**2 for i in range(1, small + 1)), arb(0))
    energy_lower = shift * (1 + resolvent_norm_squared)
    energy_upper = shift * (1 + old_norm_squared)
    if not coupling_energy - energy_lower > 0 or not energy_upper - coupling_energy > 0:
        raise ArithmeticError('two-sided secular energy bracket unresolved')
    old_origin_norm_squared = 1 + old_norm_squared
    normalized_energy = coupling_energy / old_origin_norm_squared
    if not normalized_energy > 0 or not shift - normalized_energy > 0:
        raise ArithmeticError('scale-free rank-energy budget unresolved')
    coupled_residual_energy = sum((coupled_source[index]
                                   * coupled_solution[index, 0]
                                   for index in range(large)), arb(0))
    exact_rank_energy = shift * old_origin_norm_squared
    if (not coupled_residual_energy > 0
            or not (coupled_residual_energy - exact_rank_energy).contains(0)):
        raise ArithmeticError('exact coupled rank-energy identity unresolved')
    length = arb(first['cutoff']).log()
    profile = {}
    for name, argument in (('real_4', acb(4)), ('real_8', acb(8)),
                           ('imag_1', acb(0, 1))):
        contributions = {}
        for label, solution in (('eigenvalue_shift', shift_solution),
                                ('new_modes', new_solution),
                                ('coupled_change', coupled_solution)):
            value = -_tail_fourier([solution[index, 0] for index in range(large)],
                                   length, argument)
            if not value.imag.contains(0):
                raise ArithmeticError('even rank-profile reality unresolved')
            contributions[label] = value.real
        if not (contributions['eigenvalue_shift']
                + contributions['new_modes']
                - contributions['coupled_change']).contains(0):
            raise ArithmeticError('profile contributions disagree')
        numerator = (_lower_abs(contributions['eigenvalue_shift'])
                     + _lower_abs(contributions['new_modes']))
        denominator = _upper_abs(contributions['coupled_change'])
        if denominator == 0:
            raise ArithmeticError('nonzero coupled profile change unresolved')
        profile[name] = {
            label: endpoints(value) for label, value in contributions.items()
        }
        profile[name]['separate_to_coupled_absolute_ratio_lower'] = str(
            numerator / denominator)
        functional = []
        for index in range(large):
            basis = [arb(0)] * large
            basis[index] = arb(1)
            value = _tail_fourier(basis, length, argument)
            if not value.imag.contains(0):
                raise ArithmeticError('even Fourier dual reality unresolved')
            functional.append(value.real)
        functional_matrix = arb_mat([[value] for value in functional])
        dual_energy = (functional_matrix.transpose()
                       * operator.solve(functional_matrix))[0, 0]
        if not dual_energy > 0:
            raise ArithmeticError('positive Fourier dual energy unresolved')
        cauchy_bound = (exact_rank_energy * dual_energy).sqrt()
        if not cauchy_bound - abs(contributions['coupled_change']) > 0:
            raise ArithmeticError('Fourier energy transfer bound unresolved')
        profile[name]['dual_fourier_energy'] = endpoints(dual_energy)
        profile[name]['cauchy_profile_upper'] = endpoints(cauchy_bound)
        profile[name]['cauchy_to_actual_ratio_lower'] = str(
            _lower_abs(cauchy_bound) / denominator)
    return {
        'status': 'certified_finite_coupled_rank_recurrence_not_uniform',
        'cutoff': first['cutoff'], 'mode_pair': [small, large],
        'ground_eigenvalue_shift': endpoints(shift),
        'coupled_rank_energy': {
            'residual_inverse_energy': endpoints(coupled_residual_energy),
            'eigenvalue_shift_times_old_origin_norm_squared': endpoints(exact_rank_energy),
        },
        'feshbach': {
            'effective_new_mode_coupling_energy': endpoints(coupling_energy),
            'old_secular_function_at_new_eigenvalue': endpoints(old_secular_drop),
            'energy_lower_from_eigenvalue_shift': endpoints(energy_lower),
            'energy_upper_from_eigenvalue_shift': endpoints(energy_upper),
            'old_origin_norm_squared': endpoints(old_origin_norm_squared),
            'normalized_coupling_energy': endpoints(normalized_energy),
        },
        'profile_change': profile,
        'scope': ('One nested finite support pair; no cumulative rank '
                  'budget or growing-support convergence.'),
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
        for name in ('rank_schur_recurrence.py', 'ground_schur.py',
                     'certified_mode_comparison.py', 'certified_weil.py')}
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
