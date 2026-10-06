"""Residual-centered exact-prolate error transfer in a finite Weil space.

The candidate's Rayleigh variation is 2*rho*eta + M_shift*eta^2.
This keeps the trial residual instead of replacing it by the matrix norm.
No uniform support or rank hypothesis is inferred from a finite audit.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from flint import arb, ctx
from certified_mode_comparison import box
from certified_weil import certified_matrix, endpoints
from deflated_rank_response import square
from exact_prolate_finite_gate import run as replay_small
from higher_mode_prolate_gate import run as replay_large
from isolated_kernel import isolated_spectrum
from rank_schur_recurrence import _even_matrix


def rational(value):
    return Fraction(str(value.fmpq()))


def ball(value):
    value = Fraction(value)
    return arb(value.numerator) / value.denominator


def coupled_gate(matrix, trial, eta, lowest, second):
    size = len(trial)
    eta = Fraction(eta)
    if (size < 2 or len(matrix) != size or any(len(row) != size for row in matrix)
            or not 0 <= eta < 1 or any(not x.is_finite() for x in trial)):
        raise ValueError('finite matching unit-vector enclosure and error in [0,1) required')
    if any(endpoints(matrix[i][j]) != endpoints(matrix[j][i])
           for i in range(size) for j in range(i)):
        raise ValueError('symmetric matrix enclosure required')
    if not lowest > 0 or not second > lowest:
        raise ArithmeticError('positive isolated even spectrum required')
    norm = sum((square(x) for x in trial), arb(0))
    if not norm.contains(1):
        raise ValueError('unit trial norm is not enclosed')
    image = [sum((matrix[i][j] * trial[j] for j in range(size)), arb(0))
             for i in range(size)]
    mu = sum((x*y for x, y in zip(trial, image)), arb(0))
    rho = sum((square(image[i]-mu*trial[i]) for i in range(size)), arb(0)).sqrt()
    shifted_norm = max(sum((rational(abs(matrix[i][j]-(mu if i == j else 0)).upper())
                           for j in range(size)), Fraction(0)) for i in range(size))
    rayleigh_error = 2*rational(rho.upper())*eta + shifted_norm*eta*eta
    exact_mu = mu + ball(-rayleigh_error).union(ball(rayleigh_error))
    # The exact Rayleigh quotient minimizes ||(A-s I)v|| over real s.
    residual_upper = rational(rho.upper()) + shifted_norm*eta
    residual_lower = max(Fraction(0), rational(rho.lower())-shifted_norm*eta-rayleigh_error)
    clearance = second-exact_mu
    origin_lower = max(Fraction(0), rational(abs(trial[0]).lower())-eta)
    distance = None
    if clearance > 0:
        distance = rational((arb(2).sqrt()*ball(residual_upper)/clearance.lower()).upper())
        status = ('certified_finite_strip_transfer_inputs' if origin_lower > distance
                  else 'positive_clearance_origin_unresolved')
    else:
        status = 'certified_above_second' if clearance < 0 else 'clearance_inconclusive'
    norm_a = max(sum((rational(abs(x).upper()) for x in row), Fraction(0)) for row in matrix)
    return {
        'residual_and_gap_gate': status,
        'trial_unit_norm_squared_interval': endpoints(norm),
        'trial_rayleigh_interval': endpoints(mu),
        'trial_residual_norm_interval': endpoints(rho),
        'shifted_operator_norm_upper': str(shifted_norm),
        'exact_to_trial_unit_error_upper': str(eta),
        'coupled_rayleigh_error_upper': str(rayleigh_error),
        'uncoupled_rayleigh_error_upper': str(2*norm_a*eta),
        'exact_rayleigh_interval': endpoints(exact_mu),
        'exact_residual_norm_enclosure': {'lo': str(residual_lower), 'hi': str(residual_upper)},
        'second_even_interval': endpoints(second),
        'even_gap_interval': endpoints(second-lowest),
        'second_minus_exact_rayleigh_interval': endpoints(clearance),
        'exact_candidate_origin_lower': str(origin_lower),
        'ground_distance_upper_from_residual': str(distance) if distance is not None else None,
        'origin_protected_by_residual': distance is not None and origin_lower > distance,
    }


def run(exact_path, spectrum_path, jacobi_path, vectors_path, candidate_path=None):
    paths = {'exact_prolate_gate': exact_path, 'weil_spectrum': spectrum_path,
             'prolate_jacobi': jacobi_path, 'prolate_vectors': vectors_path}
    if candidate_path is not None:
        paths['rounded_candidate'] = candidate_path
    raw = {name: path.read_bytes() for name, path in paths.items()}
    exact, spectral = json.loads(raw['exact_prolate_gate']), json.loads(raw['weil_spectrum'])
    small = spectral.get('status') == 'certified_finite_weil_gates'
    if small:
        if candidate_path is None:
            raise ValueError('rounded candidate provenance required for original finite gate')
        replay = replay_small(spectrum_path, candidate_path, jacobi_path, vectors_path)
    else:
        if spectral.get('status') != 'certified_finite_isolated_prime_kernel_not_uniform':
            raise ValueError('certified Weil spectrum required')
        replay = replay_large(spectrum_path, jacobi_path, vectors_path)
    if replay != exact:
        raise ValueError('stored exact-prolate gate differs from complete replay')
    with ctx.workprec(1024):
        if small:
            matrix = _even_matrix(spectral)
            lowest, second = (box(spectral[name]) for name in
                              ('smallest_even_eigenvalue', 'second_even_eigenvalue'))
        else:
            with ctx.workprec(512):
                _, matrix, _ = certified_matrix(spectral['cutoff'], spectral['modes'])
                eigenvalues, _ = isolated_spectrum(matrix)
                if [endpoints(x) for x in eigenvalues] != spectral['even_spectrum']:
                    raise ValueError('stored Weil spectrum differs from independent replay')
            lowest, second = eigenvalues[:2]
        trial = [box(x) for x in exact['projection_trial']['unit_coefficient_intervals']]
        result = coupled_gate(matrix, trial,
                              Fraction(exact['exact_to_trial_unit_coefficient_distance_upper']),
                              lowest, second)
    result.update({
        'status': 'certified_finite_residual_centered_exact_prolate_audit',
        'cutoff': exact['cutoff'], 'modes': exact['modes'], 'working_bits': 1024,
        'input_sha256': {name: hashlib.sha256(blob).hexdigest() for name, blob in raw.items()},
        'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                          for name in ('coupled_prolate_residual.py', 'deflated_rank_response.py',
                                       'certified_mode_comparison.py', 'certified_prolate_projection.py',
                                       'certified_prolate_vectors.py', 'certified_prolate_jacobi.py',
                                       'exact_prolate_finite_gate.py', 'higher_mode_prolate_gate.py',
                                       'certified_weil.py', 'rank_schur_recurrence.py', 'isolated_kernel.py')},
        'scope': 'Exact prolate projection into the same finite orthonormal even Fourier space as the certified prime-defined Weil matrix.',
        'remaining': 'No uniform residual clearance, all-rank ground theorem, convergence to Xi, theta curvature proof or RH proof.',
    })
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('exact', 'spectrum', 'jacobi', 'vectors', 'output'):
        parser.add_argument('--'+name, type=Path, required=True)
    parser.add_argument('--candidate', type=Path)
    args = parser.parse_args()
    result = run(args.exact, args.spectrum, args.jacobi, args.vectors, args.candidate)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['residual_and_gap_gate'])


if __name__ == '__main__':
    main()
