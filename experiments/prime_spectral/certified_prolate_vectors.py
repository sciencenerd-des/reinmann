"""Certify low even prolate eigenvectors using exact trial-vector residuals.

mpmath supplies decimal trial vectors only. The Arb residual, infinite
Jacobi tail coupling, and spectral-gap angle bound are the certificate.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_prolate_jacobi import jacobi_entries, run as certify_jacobi


def _ball(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


def trial_vectors(cutoff: int, terms: int) -> dict[str, dict]:
    import mpmath as mp

    mp.mp.dps = 90
    c = 2 * mp.pi * cutoff

    def a(index: int):
        return mp.mpf(0) if index == 0 else mp.mpf(index) / mp.sqrt((2 * index - 1) * (2 * index + 1))

    matrix = mp.matrix(terms)
    for k in range(terms):
        degree = 2 * k
        matrix[k, k] = degree * (degree + 1) + c**2 * (a(degree)**2 + a(degree + 1)**2)
        if k + 1 < terms:
            matrix[k, k + 1] = matrix[k + 1, k] = c**2 * a(degree + 1) * a(degree + 2)
    eigenvalues, vectors = mp.eigsy(matrix)
    result = {}
    for index in (0, 2):
        sign = 1 if vectors[0, index] > 0 else -1
        result[str(index)] = {
            'trial_eigenvalue': mp.nstr(eigenvalues[index], 75),
            'trial_vector': [mp.nstr(sign * vectors[k, index], 75) for k in range(terms)],
        }
    return result


def certify_trials(jacobi: dict, trials: dict[str, dict]) -> dict:
    if jacobi.get('status') != 'certified_even_prolate_low_mode_isolation_not_candidate_projection':
        raise ValueError('certified Jacobi tail isolation required')
    cutoff = jacobi['cutoff']
    terms = jacobi['even_legendre_terms']
    replay = certify_jacobi(cutoff, terms, jacobi['tail_cut'])
    for key in ('finite_eigenvalue_intervals', 'full_eigenvalue_intervals',
                'tail_floor', 'schur_shift_upper', 'coupling_beta_interval'):
        if replay[key] != jacobi[key]:
            raise ValueError('stored Jacobi tail gate disagrees with Arb replay')
    full = jacobi['full_eigenvalue_intervals']
    finite = jacobi['finite_eigenvalue_intervals']
    with ctx.workprec(512):
        diagonal, off_diagonal, beta, floor = jacobi_entries(cutoff, terms)
        if floor != jacobi['tail_floor']:
            raise ValueError('Jacobi tail floor differs from certificate')
        certified = {}
        for index in (0, 2):
            trial = trials[str(index)]
            mu = Fraction(trial['trial_eigenvalue'])
            if not Fraction(finite[index]['lo']) <= mu <= Fraction(finite[index]['hi']):
                raise ValueError('trial eigenvalue outside certified finite bracket')
            entries = [Fraction(text) for text in trial['trial_vector']]
            if len(entries) != terms:
                raise ValueError('trial vector dimension mismatch')
            vector = [_ball(x) for x in entries]
            mu_ball = _ball(mu)
            norm_squared = sum((x**2 for x in vector), arb(0))
            if not norm_squared > 0:
                raise ValueError('zero or unresolved trial-vector norm')
            residual_squared = (beta * vector[-1])**2
            for k in range(terms):
                component = (diagonal[k] - mu_ball) * vector[k]
                if k > 0:
                    component += off_diagonal[k - 1] * vector[k - 1]
                if k + 1 < terms:
                    component += off_diagonal[k] * vector[k + 1]
                residual_squared += component**2
            rho = (residual_squared / norm_squared).sqrt().upper().fmpq()
            if index == 0:
                delta = Fraction(full[1]['lo']) - mu
            else:
                delta = min(mu - Fraction(full[1]['hi']),
                            Fraction(full[3]['lo']) - mu)
            if delta <= 0:
                raise ArithmeticError('other exact eigenvalues not separated from trial')
            angle = (arb(2).sqrt() * _ball(Fraction(str(rho))) / _ball(delta)).upper().fmpq()
            certified[str(index)] = {
                **trial,
                'unit_residual_norm_upper': str(rho),
                'other_eigenvalue_distance_lower': str(delta),
                'oriented_unit_eigenvector_l2_error_upper': str(angle),
            }
        return {
            'status': 'certified_prolate_modes_0_4_not_fourier_projection',
            'cutoff': cutoff,
            'even_legendre_terms': terms,
            'working_bits': 512,
            'modes': certified,
            'scope': ('Decimal trial vectors are certified by Arb residuals in the '
                      'infinite Jacobi operator and the tail-isolated spectral gaps.'),
            'remaining': ('This eigenvector certificate alone does not give '
                          'Fourier-projection coefficients or the exact-prolate '
                          'Weil Rayleigh gate; RH remains open.'),
        }


def run(jacobi_path: Path) -> dict:
    raw = jacobi_path.read_bytes()
    jacobi = json.loads(raw)
    trials = trial_vectors(jacobi['cutoff'], jacobi['even_legendre_terms'])
    result = certify_trials(jacobi, trials)
    result['jacobi_certificate_sha256'] = hashlib.sha256(raw).hexdigest()
    result['generator_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jacobi', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.jacobi)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
