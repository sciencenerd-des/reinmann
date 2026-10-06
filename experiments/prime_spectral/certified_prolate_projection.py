"""Analytic Arb projection of the certified prolate trial vectors.

Legendre polynomials are expanded with exact rational coefficients. All
logarithmic Fourier integrals are then evaluated by closed formulas,
without quadrature across support thresholds.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx


def _ball(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


def _polynomials(max_degree: int) -> list[list[Fraction]]:
    result = [[Fraction(1)], [Fraction(0), Fraction(1)]]
    for degree in range(1, max_degree):
        current = result[degree]
        previous = result[degree - 1]
        following = [Fraction(0) for _ in range(degree + 2)]
        for power, coefficient in enumerate(current):
            following[power + 1] += Fraction(2 * degree + 1, degree + 1) * coefficient
        for power, coefficient in enumerate(previous):
            following[power] -= Fraction(degree, degree + 1) * coefficient
        result.append(following)
    return result


def _normalized_trial(values: list[str]) -> list[arb]:
    vector = [_ball(Fraction(value)) for value in values]
    norm = sum((value**2 for value in vector), arb(0)).sqrt()
    if not norm > 0:
        raise ArithmeticError('trial-vector normalization unresolved')
    return [value / norm for value in vector]


def project_trials(cutoff: int, modes: int, trial_zero: list[str],
                   trial_four: list[str]) -> dict:
    if type(cutoff) is not int or cutoff < 2 or type(modes) is not int or modes < 1:
        raise ValueError('integer cutoff at least 2 and positive Fourier modes required')
    if len(trial_zero) != len(trial_four) or len(trial_zero) < 3:
        raise ValueError('equal prolate trial-vector dimensions required')
    with ctx.workprec(1024):
        zero = _normalized_trial(trial_zero)
        four = _normalized_trial(trial_four)
        if not zero[0] > arb('0.4') or not four[0] > 0 or not four[0] < arb('0.3'):
            raise ArithmeticError('expected prolate orientation or center bound unresolved')
        ratio = four[0] / zero[0]
        legendre = _polynomials(2 * len(zero) - 2)
        coefficients = [arb(0) for _ in range(len(zero))]
        for k in range(len(zero)):
            weight = (arb(4 * k + 1) / 2).sqrt()
            amplitude = (four[k] - ratio * zero[k]) * weight
            for power in range(k + 1):
                coefficients[power] += amplitude * _ball(legendre[2 * k][2 * power])
        length = arb(cutoff).log()
        prefactor = arb(cutoff).sqrt().sqrt()
        projected = []
        for mode in range(modes + 1):
            omega = 2 * arb.pi() * mode / length
            total = arb(0)
            for n in range(1, cutoff):
                ratio_n = arb(n) / cutoff
                endpoint = (arb(cutoff) / n).log()
                phase = omega * endpoint
                sine, cosine = phase.sin(), phase.cos()
                root_inverse = (arb(cutoff) / n).sqrt()
                power_n = arb(1)
                for power, coefficient in enumerate(coefficients):
                    exponent = arb(2 * power) + arb(1) / 2
                    numerator = (root_inverse * (exponent * cosine + omega * sine)
                                 -power_n * exponent)
                    total += coefficient * numerator / (exponent**2 + omega**2)
                    power_n *= ratio_n**2
            basis_scale = 1 / length.sqrt() if mode == 0 else (2 / length).sqrt()
            projected.append(total * basis_scale / prefactor)
        norm = sum((value**2 for value in projected), arb(0)).sqrt()
        if not norm > 0 or not projected[0] > 0:
            raise ArithmeticError('candidate origin or projection norm unresolved')
        unit = [value / norm for value in projected]
        return {
            'working_bits': 1024,
            'projection_norm_interval': {'lo': str(norm.lower().fmpq()),
                                         'hi': str(norm.upper().fmpq())},
            'unit_coefficient_intervals': [
                {'lo': str(value.lower().fmpq()), 'hi': str(value.upper().fmpq())}
                for value in unit],
            'zero_integral_ratio_interval': {'lo': str(ratio.lower().fmpq()),
                                             'hi': str(ratio.upper().fmpq())},
        }


def run(vectors_path: Path, modes: int) -> dict:
    raw = vectors_path.read_bytes()
    vectors = json.loads(raw)
    if vectors.get('status') != 'certified_prolate_modes_0_4_not_fourier_projection':
        raise ValueError('certified prolate vector input required')
    result = project_trials(vectors['cutoff'], modes,
                            vectors['modes']['0']['trial_vector'],
                            vectors['modes']['2']['trial_vector'])
    result.update({
        'status': 'certified_decimal_trial_projection',
        'cutoff': vectors['cutoff'],
        'modes': modes,
        'vectors_sha256': hashlib.sha256(raw).hexdigest(),
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': ('Closed-form Arb integrals enclose the Fourier coefficients '
                  'of the saved decimal prolate trial combination.'),
        'remaining': ('This trial-projection certificate alone does not transfer '
                      'the eigenfunction error to the exact prolate candidate.'),
    })
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--vectors', type=Path, required=True)
    parser.add_argument('--modes', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.vectors, args.modes)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
