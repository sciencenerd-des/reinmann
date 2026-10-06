"""Interval comparison of a finite prime quotient resolvent with xi in s>1.

The comparison is pointwise and finite; it makes no convergence or RH claim.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, arb_mat, ctx

from certified_weil import endpoints
from certified_mode_comparison import box
from quotient_operator import build
from weil_matrix import prime_powers


def _lower(value: arb) -> Fraction:
    return Fraction(str(value.lower().fmpq()))


def _upper(value: arb) -> Fraction:
    return Fraction(str(value.upper().fmpq()))


def trace_at_height(quotient, height: arb) -> arb:
    """Independent dense-matrix form of y Tr((B^2+y^2 I)^-1)."""
    matrix = arb_mat(quotient)
    square = matrix * matrix
    for index in range(square.nrows()):
        square[index, index] += height * height
    try:
        inverse = square.inv()
    except ZeroDivisionError as exc:
        raise ArithmeticError('quotient resolvent invertibility unresolved') from exc
    return height * sum((inverse[i, i] for i in range(square.nrows())), arb(0))


def secular_trace_at_height(coefficients, length: arb, height: arb) -> dict:
    """Rank-one quotient trace with one shared eigenvector denominator."""
    if len(coefficients) < 3 or len(coefficients) % 2 != 1:
        raise ValueError('odd Fourier coefficient list with positive modes required')
    modes = len(coefficients) // 2
    center = coefficients[modes]
    if center.contains(0) or not length > 0 or not height > 0:
        raise ValueError('nonzero center, positive length and height required')
    grid = arb(0)
    grid_product = arb(1)
    secular = center
    secular_derivative = arb(0)
    for index in range(1, modes + 1):
        weight = (length / (2 * arb.pi() * index))**2
        denominator = 1 + weight * height**2
        grid_product *= denominator
        coefficient = coefficients[modes + index]
        grid += 2 * height * weight / denominator
        secular += 2 * height**2 * coefficient * weight / denominator
        secular_derivative += 4 * height * coefficient * weight / denominator**2
    if secular.contains(0):
        raise ArithmeticError('secular denominator unresolved')
    correction = secular_derivative / secular
    characteristic_value = grid_product * secular / center
    if not characteristic_value > 0:
        raise ArithmeticError('positive imaginary-axis quotient unresolved')
    return {'derivative': grid + correction, 'grid': grid,
            'secular_correction': correction, 'secular_denominator': secular,
            'grid_product': grid_product,
            'secular_ratio': secular / center,
            'characteristic_value': characteristic_value}


def finite_prime_target(powers, height: arb) -> arb:
    """Derivative of log(A(s) Z_C(s)), with s=1/2+height."""
    s = height + arb(1) / 2
    return (1 / s + 1 / (s - 1) - arb.pi().log() / 2
            + (s / 2).digamma() / 2
            - sum((arb(p).log() / arb(power)**s for power, p in powers), arb(0)))


def mesh_error_budget(coefficients, length: arb, cutoff: int, segments: int) -> dict:
    """Whole-[1,2] trace-error bound from certified finite samples."""
    if type(segments) is not int or segments < 1:
        raise ValueError('positive integer mesh segment count required')
    if type(cutoff) is not int or cutoff < 3:
        raise ValueError('prime-power cutoff at least 3 required')
    powers = prime_powers(cutoff)
    anchor_upper = _upper(secular_trace_at_height(
        coefficients, length, arb(1))['characteristic_value'])
    if anchor_upper < 1:
        raise ArithmeticError('real-rooted one-point spectral bound unresolved')
    prime_derivative = sum((arb(p).log() * arb(power).log()
                            / arb(power)**(arb(3) / 2)
                            for power, p in powers), arb(0))
    target_lipschitz = max(Fraction(40, 9),
                           _upper(arb(7) / 9 + prime_derivative))
    sample_max = Fraction(0)
    sample_min_signed_gap = None
    sample_absolute_lower = []
    worst_node = 0
    for node in range(segments + 1):
        height = arb(1) + arb(node) / segments
        derivative = secular_trace_at_height(
            coefficients, length, height)['derivative']
        difference = derivative - finite_prime_target(powers, height)
        error = max(abs(_lower(difference)), abs(_upper(difference)))
        if error > sample_max:
            sample_max, worst_node = error, node
        signed_gap = -_upper(difference)
        sample_min_signed_gap = (signed_gap if sample_min_signed_gap is None
                                 else min(sample_min_signed_gap, signed_gap))
        sample_absolute_lower.append(max(Fraction(0), _lower(difference),
                                         -_upper(difference)))
    interpolation = (2 * (anchor_upper - 1) + target_lipschitz) / (2 * segments)
    total_lipschitz = 2 * (anchor_upper - 1) + target_lipschitz
    cell_width = Fraction(1, segments)
    integrated_lower = Fraction(0)
    for sample_lower in sample_absolute_lower[:-1]:
        reach = min(cell_width, sample_lower / total_lipschitz)
        integrated_lower += sample_lower * reach - total_lipschitz * reach**2 / 2
    uniform_gap_lower = sample_min_signed_gap - interpolation
    return {
        'segments': segments,
        'maximum_sample_error_upper': str(sample_max),
        'worst_sample_node': worst_node,
        'target_lipschitz_upper': str(target_lipschitz),
        'spectral_sum_upper_from_anchor': str(anchor_upper - 1),
        'interpolation_upper': str(interpolation),
        'minimum_sampled_target_minus_quotient_lower': str(sample_min_signed_gap),
        'uniform_target_minus_quotient_lower': str(uniform_gap_lower),
        'strict_quotient_below_finite_target_on_interval': uniform_gap_lower > 0,
        'integrated_absolute_error_lower': str(integrated_lower),
        'integrated_absolute_error_upper': str(sample_max + interpolation),
        'scope': ('Finite whole-interval bound under the certified real-rooted '
                  'quotient gate; not a sequence-wide convergence estimate.'),
    }


def _compare_coefficients(cutoff: int, modes: int, coefficients,
                          length: arb, height: str, input_kind: str) -> dict:
    if type(cutoff) is not int or cutoff < 3:
        raise ValueError('integer prime-power cutoff at least 3 required')
    y = arb(height)
    if not y.is_finite() or not y > arb(1) / 2:
        raise ValueError('finite Euler-region height greater than 1/2 required')
    secular = secular_trace_at_height(coefficients, length, y)
    anchor = secular_trace_at_height(coefficients, length, arb(1))
    derivative = secular['derivative']
    s = y + arb(1) / 2
    finite_target = finite_prime_target(prime_powers(cutoff), y)
    log_cutoff = arb(cutoff).log()
    tail = ((1 - s) * log_cutoff).exp() * (
        log_cutoff / (s - 1) + 1 / (s - 1)**2)
    # H_C - xi'/xi is the nonnegative omitted von Mangoldt sum.
    target_lower = _lower(finite_target) - _upper(tail)
    target_upper = _upper(finite_target)
    separated = _upper(derivative) < target_lower
    return {
        'status': ('certified_finite_quotient_derivative_below_xi'
                   if separated else 'finite_euler_derivative_comparison_inconclusive'),
        'cutoff': cutoff, 'modes': modes, 'input_kind': input_kind,
        'imaginary_height': height, 's': endpoints(s),
        'quotient_log_derivative': endpoints(derivative),
        'grid_log_derivative': endpoints(secular['grid']),
        'secular_log_derivative_correction': endpoints(secular['secular_correction']),
        'secular_denominator': endpoints(secular['secular_denominator']),
        'anchor_quotient_value': endpoints(anchor['characteristic_value']),
        'anchor_grid_product': endpoints(anchor['grid_product']),
        'anchor_secular_ratio': endpoints(anchor['secular_ratio']),
        'finite_prime_power_target': endpoints(finite_target),
        'omitted_prime_power_tail_upper': str(_upper(tail)),
        'xi_log_derivative_enclosure': {
            'lo': str(target_lower), 'hi': str(target_upper)},
        'strict_quotient_below_xi': separated,
        'scope': ('One finite quotient logarithmic derivative on the Euler '
                  'axis; no growing-cutoff convergence or RH inference.'),
    }


def compare(certificate: dict, height: str) -> dict:
    if certificate.get('status') != 'certified_finite_weil_gates':
        raise ValueError('certified finite Weil matrix required')
    with ctx.workprec(512):
        coefficients, length, _, _ = build(certificate)
        return _compare_coefficients(certificate['cutoff'], certificate['modes'],
                                     coefficients, length, height, 'certified_weil')


def compare_isolated(certificate: dict, height: str) -> dict:
    if certificate.get('status') != 'certified_finite_isolated_prime_kernel_not_uniform':
        raise ValueError('certified isolated prime kernel required')
    modes = certificate['modes']
    half = certificate['boundary_normalized_positive_half']
    if type(modes) is not int or modes < 1 or len(half) != modes + 1:
        raise ValueError('isolated Fourier dimension mismatch')
    with ctx.workprec(512):
        positive_half = [box(value) for value in half]
        if not positive_half[0] > 0:
            raise ArithmeticError('positive Fourier origin unresolved')
        coefficients = list(reversed(positive_half[1:])) + positive_half
        length = arb(certificate['cutoff']).log()
        return _compare_coefficients(certificate['cutoff'], modes,
                                     coefficients, length, height, 'isolated_kernel')


def run(certificate_path: Path, height: str, mesh_segments: int | None = None) -> dict:
    raw = certificate_path.read_bytes()
    certificate = json.loads(raw)
    source_dir = Path(__file__).parent
    for name, digest in certificate['source_hashes'].items():
        if hashlib.sha256((source_dir / name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale finite Weil certificate source: ' + name)
    if certificate.get('status') == 'certified_finite_weil_gates':
        result = compare(certificate, height)
    elif certificate.get('status') == 'certified_finite_isolated_prime_kernel_not_uniform':
        result = compare_isolated(certificate, height)
    else:
        raise ValueError('unsupported finite prime certificate')
    if mesh_segments is not None:
        with ctx.workprec(512):
            if result['input_kind'] == 'certified_weil':
                coefficients, length, _, _ = build(certificate)
            else:
                half = [box(value) for value in certificate['boundary_normalized_positive_half']]
                coefficients = list(reversed(half[1:])) + half
                length = arb(certificate['cutoff']).log()
            result['mesh_budget'] = mesh_error_budget(
                coefficients, length, certificate['cutoff'], mesh_segments)
    result['input_sha256'] = hashlib.sha256(raw).hexdigest()
    result['source_hashes'] = {
        name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
        for name in ('euler_region_trace.py', 'quotient_operator.py',
                     'certified_mode_comparison.py', 'weil_matrix.py')
    }
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--height', default='2')
    parser.add_argument('--mesh-segments', type=int)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.certificate, args.height, args.mesh_segments)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
