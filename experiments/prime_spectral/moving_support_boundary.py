"""Certify the rank-one boundary flux of a moving Fourier interval.

The cross-support Gram derivative has a skew dilation part and a
rank-one symmetric boundary part. This audit relates the latter to the
independently certified prime-power Weil eigenvalue derivative jump.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_mode_comparison import box
from certified_weil import endpoints
from cross_support_physical_overlap import unit_even_coefficients
from isolated_kernel import run as replay_isolated
from prime_threshold_jump import run as replay_threshold


def gram_log_length_derivative(index: int, other: int) -> arb:
    """L times the right b-derivative of <e_(L,index),e_(b,other)> at b=L."""
    if type(index) is not int or type(other) is not int or index < 0 or other < 0:
        raise ValueError('nonnegative integer Fourier indices required')
    if index == other == 0:
        return -arb(1) / 2
    if other == 0:
        return arb(0)
    if index == 0:
        return -arb(2).sqrt()
    if index == other:
        return -arb(1)
    return arb(2 * other * other) / arb(index * index - other * other)


def certify(isolated: dict, threshold: dict) -> dict:
    if isolated.get('status') != 'certified_finite_isolated_prime_kernel_not_uniform':
        raise ValueError('certified finite Weil ground vector required')
    if threshold.get('status') != 'certified_finite_negative_prime_threshold_derivative_jump':
        raise ValueError('certified prime-power threshold jump required')
    if (isolated['cutoff'], isolated['modes']) != (threshold['cutoff'], threshold['modes']):
        raise ValueError('support and rank mismatch')
    with ctx.workprec(512):
        length = arb(isolated['cutoff']).log()
        unit = unit_even_coefficients(isolated)
        boundary = [arb(1)] + [arb(2).sqrt() for _ in unit[1:]]
        size = len(unit)
        derivative = [[gram_log_length_derivative(i, j) for j in range(size)]
                      for i in range(size)]
        for i in range(size):
            for j in range(size):
                if not (derivative[i][j] + derivative[j][i]
                        + boundary[i] * boundary[j]).contains(0):
                    raise ArithmeticError('Gram derivative boundary identity unresolved')
        # The saved half-vector is normalized so c_0+2*sum(c_n)=1
        # algebraically. Summing the tiny boundary value after unit
        # normalization loses many orders to interval cancellation.
        half = [box(cell) for cell in isolated['boundary_normalized_positive_half']]
        raw_boundary = half[0] + 2 * sum(half[1:], arb(0))
        if not (raw_boundary - 1).contains(0):
            raise ArithmeticError('boundary-normalized half-vector disagrees')
        raw_norm_squared = half[0]**2 + 2 * sum((x**2 for x in half[1:]), arb(0))
        if not raw_norm_squared > 0:
            raise ArithmeticError('boundary-normalized ground norm unresolved')
        boundary_square = 1 / raw_norm_squared
        direct_boundary_square = sum((x * y for x, y in zip(boundary, unit)), arb(0))**2
        if not (direct_boundary_square - boundary_square).contains(0):
            raise ArithmeticError('two boundary square enclosures disagree')
        direct_contraction = sum((
            unit[i] * derivative[i][j] * unit[j]
            for i in range(size) for j in range(size)), arb(0)) / length
        boundary_slope = -boundary_square / (2 * length)
        if not (direct_contraction - boundary_slope).contains(0):
            raise ArithmeticError('physical overlap slope differs from boundary flux')
        stored_boundary = threshold['unit_ground_boundary_squared']
        stored_jump = threshold['lowest_even_eigenvalue_derivative_jump']
        if (Fraction(str(boundary_square.upper().fmpq())) < Fraction(stored_boundary['lo'])
                or Fraction(str(boundary_square.lower().fmpq())) > Fraction(stored_boundary['hi'])):
            raise ValueError('boundary square disagrees with prime threshold certificate')
        exponent = threshold['exponent']
        prime_kick = -(arb(2) / (arb(exponent) * arb(isolated['cutoff']).sqrt())) * boundary_square
        if (Fraction(str(prime_kick.upper().fmpq())) < Fraction(stored_jump['lo'])
                or Fraction(str(prime_kick.lower().fmpq())) > Fraction(stored_jump['hi'])):
            raise ValueError('prime derivative kick disagrees with boundary identity')
        ratio = arb(4) * length / (arb(exponent) * arb(isolated['cutoff']).sqrt())
        if not (prime_kick - ratio * boundary_slope).contains(0):
            raise ArithmeticError('geometric and prime boundary kicks disagree')
        if not boundary_slope < 0 or not prime_kick < 0:
            raise ArithmeticError('strict negative boundary slope unresolved')
        return {
            'status': 'certified_finite_moving_support_rank_one_boundary_identity',
            'cutoff': isolated['cutoff'], 'modes': isolated['modes'],
            'prime': threshold['prime'], 'exponent': exponent,
            'working_bits': 512,
            'unit_boundary_square': endpoints(boundary_square),
            'direct_interval_unit_boundary_square': endpoints(direct_boundary_square),
            'physical_overlap_right_derivative': endpoints(boundary_slope),
            'direct_interval_gram_contraction': endpoints(direct_contraction),
            'origin_matched_norm_squared_right_derivative': endpoints(-2 * boundary_slope),
            'prime_eigenvalue_derivative_jump': endpoints(prime_kick),
            'prime_to_geometric_slope_factor': endpoints(ratio),
            'matrix_identity': 'D+D^T=-u*u^T, D=L*d_b G(L,b)|b=L+, u=(1,sqrt(2),...)',
            'scope': ('One-sided first-order geometry at one finite prime-power '
                      'support with a simple normalized even ground vector.'),
            'remaining': ('No second-order or cumulative physical overlap bound, '
                          'profile susceptibility estimate, all-rank limit, or RH proof.'),
        }


def run(isolated_path: Path, threshold_path: Path) -> dict:
    isolated_raw, threshold_raw = isolated_path.read_bytes(), threshold_path.read_bytes()
    isolated, threshold = json.loads(isolated_raw), json.loads(threshold_raw)
    if replay_isolated(isolated['cutoff'], isolated['modes']) != isolated:
        raise ValueError('saved isolated Weil certificate replay disagrees')
    if replay_threshold(isolated_path) != threshold:
        raise ValueError('saved prime threshold certificate replay disagrees')
    result = certify(isolated, threshold)
    result['input_sha256'] = {
        'isolated_weil': hashlib.sha256(isolated_raw).hexdigest(),
        'prime_threshold': hashlib.sha256(threshold_raw).hexdigest(),
    }
    result['source_hashes'] = {
        name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        for name in ('moving_support_boundary.py', 'cross_support_physical_overlap.py',
                     'prime_threshold_jump.py', 'isolated_kernel.py',
                     'certified_mode_comparison.py', 'certified_weil.py')
    }
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--isolated', type=Path, required=True)
    parser.add_argument('--threshold', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.isolated, args.threshold)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['cutoff'], result['modes'])


if __name__ == '__main__':
    main()
