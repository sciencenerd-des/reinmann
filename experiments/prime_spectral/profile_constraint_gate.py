"""Certify a two-frequency obstruction to finite Weil Rayleigh repair.

The target values are those of the exact projected prolate candidate,
enclosed via its replayed eigenfunction and Fourier-projection errors.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_mode_comparison import box
from certified_weil import inertia
from exact_prolate_finite_gate import run as exact_prolate_gate


FREQUENCIES = (4, 8)
PIVOT_COLUMNS = (0, 3)


def _ball(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


def _endpoints(value: arb) -> dict[str, str]:
    return {'lo': str(value.lower().fmpq()), 'hi': str(value.upper().fmpq())}


def _fourier_row(length: arb, modes: int, frequency: int) -> list[arb]:
    angle = arb(frequency) * length / 2
    root_two = arb(2).sqrt()
    return [angle.sinc()] + [
        ((-1) ** j) / root_two
        * ((arb.pi() * j - angle).sinc() + (arb.pi() * j + angle).sinc())
        for j in range(1, modes + 1)
    ]


def _even_matrix(certificate: dict) -> list[list[arb]]:
    modes = certificate['modes']
    full = [[box(cell) for cell in row] for row in certificate['matrix']]
    if len(full) != 2 * modes + 1 or any(len(row) != len(full) for row in full):
        raise ValueError('certified Weil matrix dimension mismatch')
    root_two = arb(2).sqrt()
    result = []
    for i in range(modes + 1):
        row = []
        for j in range(modes + 1):
            if i == 0 and j == 0:
                value = full[modes][modes]
            elif i == 0:
                value = root_two * full[modes][modes + j]
            elif j == 0:
                value = root_two * full[modes + i][modes]
            else:
                value = full[modes + i][modes + j] + full[modes + i][modes - j]
            row.append(value)
        result.append(row)
    return result


def certify(certificate: dict, exact_gate: dict, excess: Fraction,
            profile_tolerance: Fraction = Fraction(0)) -> dict:
    if certificate.get('status') != 'certified_finite_weil_gates':
        raise ValueError('certified Weil matrix required')
    if ((certificate['cutoff'], certificate['modes']) !=
            (exact_gate['cutoff'], exact_gate['modes']) or
            exact_gate.get('rayleigh_above_second_even_certified') is not True):
        raise ValueError('matching exact-prolate finite gate required')
    if excess <= 0 or profile_tolerance < 0 or certificate['modes'] < 4:
        raise ValueError('positive excess, nonnegative tolerance, and at least four modes required')
    with ctx.workprec(1024):
        modes = certificate['modes']
        dimension = modes + 1
        length = arb(certificate['cutoff']).log()
        trial = [box(cell) for cell in exact_gate['projection_trial']['unit_coefficient_intervals']]
        if len(trial) != dimension:
            raise ValueError('prolate Fourier dimension mismatch')
        error = _ball(Fraction(exact_gate['exact_to_trial_unit_coefficient_distance_upper']))
        central_lower = trial[0].lower()
        if not central_lower > error:
            raise ArithmeticError('exact prolate Fourier origin unresolved')
        rows = []
        profiles = {}
        for frequency in FREQUENCIES:
            functional = _fourier_row(length, modes, frequency)
            trial_profile = sum((a * b for a, b in zip(functional, trial)), arb(0)) / trial[0]
            functional_norm = sum((a * a for a in functional), arb(0)).sqrt().upper()
            profile_error = (functional_norm * error / (central_lower - error)
                             * (1 + 1 / central_lower)).upper().fmpq()
            profile_error = Fraction(str(profile_error)) + profile_tolerance
            exact_profile = trial_profile + arb(str(-profile_error)).union(arb(str(profile_error)))
            profiles[str(frequency)] = _endpoints(exact_profile)
            functional[0] -= exact_profile
            rows.append(functional)

        first, second = PIVOT_COLUMNS
        determinant = rows[0][first] * rows[1][second] - rows[0][second] * rows[1][first]
        if determinant.contains(0):
            raise ArithmeticError('two profile constraints are dependent')
        free = [j for j in range(dimension) if j not in PIVOT_COLUMNS]
        columns = []
        for index in free:
            right_first, right_second = rows[0][index], rows[1][index]
            vector = [arb(0) for _ in range(dimension)]
            vector[first] = (-right_first * rows[1][second]
                             + right_second * rows[0][second]) / determinant
            vector[second] = (-right_second * rows[0][first]
                              + right_first * rows[1][first]) / determinant
            vector[index] = arb(1)
            columns.append(vector)

        matrix = _even_matrix(certificate)
        second_upper = box(certificate['second_even_eigenvalue']).upper().fmpq()
        shift = _ball(Fraction(str(second_upper)) + excess)
        constrained = [[sum((columns[i][k] *
                             (matrix[k][l] - (shift if k == l else 0)) *
                             columns[j][l]
                             for k in range(dimension) for l in range(dimension)), arb(0))
                        for j in range(len(columns))] for i in range(len(columns))]
        negative, pivots = inertia(constrained)
        if negative != 0 or not all(pivot > 0 for pivot in pivots):
            raise ArithmeticError('profile-constrained Rayleigh excess unresolved')
        return {
            'status': 'certified_two_point_profile_constraint_above_second_even',
            'cutoff': certificate['cutoff'],
            'modes': modes,
            'working_bits': 1024,
            'frequencies': list(FREQUENCIES),
            'allowed_profile_error_at_each_frequency': str(profile_tolerance),
            'exact_prolate_profile_intervals': profiles,
            'constraint_pivot_columns': list(PIVOT_COLUMNS),
            'constraint_pivot_determinant_interval': _endpoints(determinant),
            'second_even_upper': str(second_upper),
            'strict_rayleigh_excess_over_second_even_lower': str(excess),
            'constrained_shifted_ldl_pivot_lower': [str(p.lower().fmpq()) for p in pivots],
            'scope': ('Any nonzero even Fourier vector whose origin-normalized profile '
                      'is within the stated tolerance of the exact projected prolate '
                      'profile at both listed frequencies has Rayleigh quotient '
                      'greater than the certified '
                      'second even eigenvalue by the stated excess.'),
            'remaining': ('The two-frequency obstruction is finite only; approximate '
                          'profile matching, growing support, and RH remain open.'),
        }


def run(certificate_path: Path, candidate_path: Path, jacobi_path: Path,
        vectors_path: Path, excess: Fraction,
        profile_tolerance: Fraction = Fraction(0)) -> dict:
    certificate_bytes = certificate_path.read_bytes()
    certificate = json.loads(certificate_bytes)
    exact_gate = exact_prolate_gate(certificate_path, candidate_path, jacobi_path, vectors_path)
    result = certify(certificate, exact_gate, excess, profile_tolerance)
    result['input_sha256'] = {
        'weil_certificate': hashlib.sha256(certificate_bytes).hexdigest(),
        'rounded_candidate': hashlib.sha256(candidate_path.read_bytes()).hexdigest(),
        'prolate_jacobi': hashlib.sha256(jacobi_path.read_bytes()).hexdigest(),
        'prolate_vectors': hashlib.sha256(vectors_path.read_bytes()).hexdigest(),
    }
    result['generator_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--jacobi', type=Path, required=True)
    parser.add_argument('--vectors', type=Path, required=True)
    parser.add_argument('--excess', type=Fraction, required=True)
    parser.add_argument('--profile-tolerance', type=Fraction, default=Fraction(0))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.certificate, args.candidate, args.jacobi, args.vectors,
                 args.excess, args.profile_tolerance)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
