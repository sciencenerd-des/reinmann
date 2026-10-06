"""Certify physical L2 overlap and a strip profile bound across supports.

Both finite ground Fourier functions are extended by zero to L2(R). The
cross-basis Gram matrix is integrated analytically, so this does not mistake
coefficient-coordinate overlap for physical-function overlap.
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
from isolated_kernel import run as replay_isolated


def _dot(left: list[arb], right: list[arb]) -> arb:
    return sum((x * y for x, y in zip(left, right)), arb(0))


def unit_even_coefficients(certificate: dict) -> list[arb]:
    """Convert boundary-normalized half coefficients to the orthonormal basis."""
    half = [box(cell) for cell in certificate['boundary_normalized_positive_half']]
    if len(half) != certificate['modes'] + 1 or not half[0] > 0:
        raise ArithmeticError('positive finite ground origin unresolved')
    raw = [half[0]] + [arb(2).sqrt() * value for value in half[1:]]
    norm = _dot(raw, raw).sqrt()
    if not norm > 0:
        raise ArithmeticError('ground-vector norm unresolved')
    unit = [value / norm for value in raw]
    if not unit[0] > 0:
        raise ArithmeticError('unit ground orientation unresolved')
    return unit


def cross_gram(index: int, other: int, small_length: arb,
               large_length: arb) -> arb:
    """Integral of centered cosine modes over the smaller interval."""
    if index < 0 or other < 0 or not small_length > 0 or small_length > large_length:
        raise ValueError('nonnegative modes and ordered positive support lengths required')
    ratio = small_length / large_length
    if index == other == 0:
        return ratio.sqrt()
    if other == 0:
        return arb(0)
    if index == 0:
        return (2 * ratio).sqrt() * (-1)**other * (arb.pi() * other * ratio).sinc()
    return ratio.sqrt() * (-1)**(index + other) * (
        (arb.pi() * (index - other * ratio)).sinc()
        + (arb.pi() * (index + other * ratio)).sinc())


def _strip_functional_norm(length: arb, height: Fraction) -> arb:
    if height == 0:
        return length.sqrt()
    sigma = arb(height.numerator) / arb(height.denominator)
    return ((sigma * length).sinh() / sigma).sqrt()


def certify(first: dict, second: dict, height: Fraction = Fraction(2, 5)) -> dict:
    if first.get('status') != 'certified_finite_isolated_prime_kernel_not_uniform' or second.get('status') != 'certified_finite_isolated_prime_kernel_not_uniform':
        raise ValueError('two certified finite isolated prime kernels required')
    if first['modes'] != second['modes'] or first['cutoff'] >= second['cutoff']:
        raise ValueError('same rank and strictly increasing support required')
    if not 0 <= height < Fraction(1, 2):
        raise ValueError('closed critical-substrip height required')
    with ctx.workprec(512):
        small_length = arb(first['cutoff']).log()
        large_length = arb(second['cutoff']).log()
        old = unit_even_coefficients(first)
        new = unit_even_coefficients(second)
        modes = first['modes']
        coordinate_overlap = _dot(old, new)
        physical_overlap = sum((old[i] * cross_gram(i, j, small_length,
                                                       large_length) * new[j]
                                for i in range(modes + 1)
                                for j in range(modes + 1)), arb(0))
        if not physical_overlap > 0 or not physical_overlap < 1:
            raise ArithmeticError('positive physical overlap below one unresolved')
        distance = (2 * (1 - physical_overlap)).sqrt()
        first_origin = small_length.sqrt() * old[0]
        second_origin = large_length.sqrt() * new[0]
        if not first_origin > 0 or not second_origin > 0:
            raise ArithmeticError('positive Fourier origins unresolved')
        old_functional = _strip_functional_norm(small_length, height)
        new_functional = _strip_functional_norm(large_length, height)
        # Write P_D-P_C = F_z(g_D-g_C)/F_0(g_D)
        # + F_z(g_C)*(F_0(g_C)-F_0(g_D))/(F_0(g_D)*F_0(g_C)).
        # ||F_z|| on I_E is sqrt(sinh(sigma L_E)/sigma); the F_0
        # difference is supported on I_D and bounded by sqrt(L_D)*d.
        profile_bound = distance / second_origin * (
            new_functional
            + old_functional * large_length.sqrt() / first_origin)
        # Origin matching retains the cancellation discarded by the two-term
        # triangle bound: h=g_D-(alpha_D/alpha_C)g_C has integral zero and
        # P_D-P_C=F_z(h)/alpha_D.
        origin_ratio = second_origin / first_origin
        centered_norm_squared = (1 + origin_ratio**2
                                 - 2 * origin_ratio * physical_overlap)
        if not centered_norm_squared > 0:
            raise ArithmeticError('origin-matched physical norm unresolved')
        centered_norm = centered_norm_squared.sqrt()
        coupled_profile_bound = new_functional * centered_norm / second_origin
        return {
            'status': 'certified_finite_cross_support_physical_overlap_not_uniform',
            'first_cutoff': first['cutoff'],
            'second_cutoff': second['cutoff'],
            'modes': modes,
            'working_bits': 512,
            'strip_height': str(height),
            'coefficient_coordinate_overlap': endpoints(coordinate_overlap),
            'physical_l2_overlap': endpoints(physical_overlap),
            'physical_unit_distance': endpoints(distance),
            'first_fourier_origin': endpoints(first_origin),
            'second_fourier_origin': endpoints(second_origin),
            'uniform_strip_profile_difference_upper': str(profile_bound.upper().fmpq()),
            'origin_matched_physical_norm': endpoints(centered_norm),
            'coupled_uniform_strip_profile_difference_upper': str(
                coupled_profile_bound.upper().fmpq()),
            'scope': ('Zero-extended finite ground Fourier functions in one L2(R) space; '
                      'uniform in real frequency on this one closed horizontal strip.'),
            'remaining': ('No summable support-step bound, simultaneous rank growth, '
                          'candidate-to-ground convergence, or RH proof.'),
        }


def run(first_path: Path, second_path: Path,
        height: Fraction = Fraction(2, 5)) -> dict:
    first_raw, second_raw = first_path.read_bytes(), second_path.read_bytes()
    first, second = json.loads(first_raw), json.loads(second_raw)
    for certificate in (first, second):
        if replay_isolated(certificate['cutoff'], certificate['modes']) != certificate:
            raise ValueError('stored finite Weil certificate replay disagrees')
    result = certify(first, second, height)
    result['input_sha256'] = {
        'first_isolated_weil': hashlib.sha256(first_raw).hexdigest(),
        'second_isolated_weil': hashlib.sha256(second_raw).hexdigest(),
    }
    result['source_hashes'] = {
        name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        for name in ('cross_support_physical_overlap.py', 'isolated_kernel.py',
                     'certified_weil.py', 'certified_mode_comparison.py')
    }
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first', type=Path, required=True)
    parser.add_argument('--second', type=Path, required=True)
    parser.add_argument('--height', type=Fraction, default=Fraction(2, 5))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.first, args.second, args.height)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['first_cutoff'], result['second_cutoff'], result['modes'])


if __name__ == '__main__':
    main()
