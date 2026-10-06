"""Certify a finite ground Fourier profile from least-eigenvalue secants.

Concavity brackets the derivatives of two rank-one perturbation
responses. Their ratio is the origin-normalized ground profile. This
does not establish a support-uniform response limit or RH.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, acb, ctx

from certified_weil import eigen_interval
from rank_schur_recurrence import _even_matrix, _tail_fourier


def _fraction(value: arb, side: str) -> Fraction:
    endpoint = value.lower() if side == 'lo' else value.upper()
    return Fraction(str(endpoint.fmpq()))


def _interval(lower: Fraction, upper: Fraction) -> dict[str, str]:
    if lower > upper:
        raise ArithmeticError('reversed derivative or profile interval')
    return {'lo': str(lower), 'hi': str(upper)}


def _secants(matrix: list[list[arb]], q: list[arb],
             step: Fraction, central: arb) -> dict[str, str]:
    """Outward bracket for d/dt lambda_min(A+t(e q*+q e*))."""
    size = len(matrix)
    if len(q) != size:
        raise ValueError('perturbation vector dimension mismatch')
    h = arb(step.numerator) / arb(step.denominator)
    perturbation = [[(q[j] if i == 0 else arb(0))
                     + (q[i] if j == 0 else arb(0))
                     for j in range(size)] for i in range(size)]
    plus = eigen_interval([[matrix[i][j] + h * perturbation[i][j]
                            for j in range(size)] for i in range(size)], 0)
    minus = eigen_interval([[matrix[i][j] - h * perturbation[i][j]
                             for j in range(size)] for i in range(size)], 0)
    # The least-eigenvalue surface is concave. The positive secant is
    # below its derivative at zero; the negative secant is above it.
    lower = (_fraction(plus, 'lo') - _fraction(central, 'hi')) / step
    upper = (_fraction(central, 'hi') - _fraction(minus, 'lo')) / step
    return _interval(lower, upper)


def _profile_interval(numerator: dict[str, str],
                      denominator: dict[str, str]) -> dict[str, str]:
    low_d, high_d = Fraction(denominator['lo']), Fraction(denominator['hi'])
    if low_d <= 0:
        raise ArithmeticError('positive origin response unresolved')
    possibilities = [Fraction(numerator[key]) / (2 * value)
                     for key in ('lo', 'hi') for value in (low_d, high_d)]
    return _interval(min(possibilities), max(possibilities))


def _fourier_functional(modes: int, length: arb, z: acb) -> list[arb]:
    center = (-z * length / 2).sinc()
    if not center.imag.contains(0):
        raise ArithmeticError('center Fourier functional reality unresolved')
    result = [center.real]
    for index in range(modes):
        basis = [arb(0)] * modes
        basis[index] = arb(1)
        value = _tail_fourier(basis, length, z)
        if not value.imag.contains(0):
            raise ArithmeticError('tail Fourier functional reality unresolved')
        result.append(value.real)
    return result


def certify(certificate: dict, step: Fraction) -> dict:
    if certificate.get('status') != 'certified_finite_weil_gates':
        raise ValueError('certified finite Weil gate required')
    if step <= 0:
        raise ValueError('positive rational secant step required')
    with ctx.workprec(512):
        modes = certificate['modes']
        matrix = _even_matrix(certificate)
        central = eigen_interval(matrix, 0)
        length = arb(certificate['cutoff']).log()
        origin = _secants(matrix, [arb(1) / 2] + [arb(0)] * modes,
                          step, central)
        if Fraction(origin['lo']) <= 0:
            raise ArithmeticError('positive origin response unresolved')
        profiles = {}
        for name, argument in (('real_4', acb(4)), ('real_8', acb(8)),
                               ('imag_1', acb(0, 1))):
            functional = _fourier_functional(modes, length, argument)
            response = _secants(matrix, functional, step, central)
            profiles[name] = {
                'fourier_response_derivative': response,
                'origin_normalized_profile': _profile_interval(response, origin),
            }
        return {
            'status': 'certified_finite_profile_via_eigenvalue_secants_not_convergence',
            'cutoff': certificate['cutoff'], 'modes': modes,
            'positive_secant_step': str(step),
            'origin_response_derivative': origin,
            'profile': profiles,
            'scope': ('Concave secants of finite least-eigenvalue surfaces; '
                      'no gap-free convergence theorem is asserted.'),
        }


def run(certificate_path: Path, step: Fraction) -> dict:
    raw = certificate_path.read_bytes()
    certificate = json.loads(raw)
    source_dir = Path(__file__).parent
    for name, digest in certificate['source_hashes'].items():
        if hashlib.sha256((source_dir / name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale finite Weil certificate source: ' + name)
    result = certify(certificate, step)
    result['input_sha256'] = hashlib.sha256(raw).hexdigest()
    result['source_hashes'] = {
        name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
        for name in ('eigenvalue_response.py', 'certified_weil.py',
                     'rank_schur_recurrence.py')}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--step', type=Fraction, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.certificate, args.step)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
