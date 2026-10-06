"""Certified coupled least-eigenvalue response for a nested Weil rank step.

The determinant preserves cancellation between Fourier and origin
responses. Its finite interval enclosure is not an all-rank budget.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from eigenvalue_response import run as response_run


Interval = tuple[Fraction, Fraction]


def _box(record: dict[str, str]) -> Interval:
    low, high = Fraction(record['lo']), Fraction(record['hi'])
    if low > high:
        raise ValueError('reversed response interval')
    return low, high


def _record(value: Interval) -> dict[str, str]:
    return {'lo': str(value[0]), 'hi': str(value[1])}


def _subtract(left: Interval, right: Interval) -> Interval:
    return left[0] - right[1], left[1] - right[0]


def _multiply(left: Interval, right: Interval) -> Interval:
    values = [a * b for a in left for b in right]
    return min(values), max(values)


def _divide_positive(numerator: Interval, denominator: Interval) -> Interval:
    if denominator[0] <= 0:
        raise ArithmeticError('positive origin-response product unresolved')
    values = [a / b for a in numerator for b in denominator]
    return min(values), max(values)


def _lower_abs(value: Interval) -> Fraction:
    if value[0] <= 0 <= value[1]:
        return Fraction(0)
    return min(abs(value[0]), abs(value[1]))


def _upper_abs(value: Interval) -> Fraction:
    return max(abs(value[0]), abs(value[1]))


def _overlap(first: Interval, second: Interval) -> bool:
    return first[0] <= second[1] and second[0] <= first[1]


def compare(first: dict, second: dict) -> dict:
    status = 'certified_finite_profile_via_eigenvalue_secants_not_convergence'
    if first.get('status') != status or second.get('status') != status:
        raise ValueError('two certified finite response records required')
    if first['cutoff'] != second['cutoff'] or not first['modes'] < second['modes']:
        raise ValueError('nested responses at the same support required')
    old_origin = _box(first['origin_response_derivative'])
    new_origin = _box(second['origin_response_derivative'])
    if old_origin[0] <= 0 or new_origin[0] <= 0:
        raise ArithmeticError('positive origin responses unresolved')
    denominator = _multiply((2 * old_origin[0], 2 * old_origin[1]), new_origin)
    output = {}
    for name in first['profile']:
        if name not in second['profile']:
            raise ValueError('Fourier response arguments disagree')
        old_fourier = _box(first['profile'][name]['fourier_response_derivative'])
        new_fourier = _box(second['profile'][name]['fourier_response_derivative'])
        first_product = _multiply(new_fourier, old_origin)
        second_product = _multiply(old_fourier, new_origin)
        determinant = _subtract(first_product, second_product)
        increment = _divide_positive(determinant, denominator)
        direct = _subtract(_box(second['profile'][name]['origin_normalized_profile']),
                           _box(first['profile'][name]['origin_normalized_profile']))
        if not _overlap(increment, direct):
            raise ArithmeticError('response determinant disagrees with profile secants')
        determinant_upper = _upper_abs(determinant)
        cancellation = ((_lower_abs(first_product) + _lower_abs(second_product))
                        / determinant_upper if determinant_upper > 0 else None)
        output[name] = {
            'new_fourier_times_old_origin': _record(first_product),
            'old_fourier_times_new_origin': _record(second_product),
            'coupled_response_determinant': _record(determinant),
            'profile_increment': _record(increment),
            'separate_to_coupled_ratio_lower': (
                str(cancellation) if cancellation is not None else None),
        }
    return {
        'status': 'certified_finite_coupled_response_not_all_rank',
        'cutoff': first['cutoff'],
        'mode_pair': [first['modes'], second['modes']],
        'profile_change': output,
        'scope': ('Finite rank-response determinant only; no uniform '
                  'cumulative bound or Xi identification.'),
    }


def run(first_response_path: Path, second_response_path: Path,
        first_weil_path: Path, second_weil_path: Path) -> dict:
    responses = []
    source_dir = Path(__file__).parent
    for response_path, weil_path in ((first_response_path, first_weil_path),
                                     (second_response_path, second_weil_path)):
        raw = response_path.read_bytes()
        response = json.loads(raw)
        for name, digest in response['source_hashes'].items():
            if hashlib.sha256((source_dir / name).read_bytes()).hexdigest() != digest:
                raise ValueError('stale finite response source: ' + name)
        if response['input_sha256'] != hashlib.sha256(weil_path.read_bytes()).hexdigest():
            raise ValueError('response and Weil provenance mismatch')
        if response_run(weil_path, Fraction(response['positive_secant_step'])) != response:
            raise ValueError('saved finite response replay disagrees')
        responses.append((raw, response))
    result = compare(responses[0][1], responses[1][1])
    result['response_sha256'] = [hashlib.sha256(raw).hexdigest()
                                 for raw, _ in responses]
    result['source_hashes'] = {
        name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
        for name in ('rank_response_determinant.py', 'eigenvalue_response.py')}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first-response', type=Path, required=True)
    parser.add_argument('--second-response', type=Path, required=True)
    parser.add_argument('--first-weil', type=Path, required=True)
    parser.add_argument('--second-weil', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.first_response, args.second_response,
                 args.first_weil, args.second_weil)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
