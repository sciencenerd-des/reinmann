"""Certify finite prolate-to-Weil ground angle and Fourier profile distances.

This uses Rump-isolated finite ground eigenvectors and the already
certified error of the exact prolate projection from its trial vector.
No rank- or support-uniform approximation is inferred.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, acb, arb_mat, ctx

from certified_mode_comparison import box
from certified_weil import certified_matrix, endpoints
from eigenvalue_response import _fourier_functional
from isolated_kernel import isolated_spectrum
from prolate_cluster_gate import run as cluster_run
from rank_schur_recurrence import _even_matrix


def _lower(value: arb) -> Fraction:
    return Fraction(str(value.lower().fmpq()))


def _upper(value: arb) -> Fraction:
    return Fraction(str(value.upper().fmpq()))


def _ball(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


def _upper_abs(value: arb) -> Fraction:
    return max(abs(_lower(value)), abs(_upper(value)))


def certify(exact_gate: dict, spectral: dict) -> dict:
    if exact_gate['cutoff'] != spectral['cutoff'] or exact_gate['modes'] != spectral['modes']:
        raise ValueError('prolate and Weil support or rank mismatch')
    modes = exact_gate['modes']
    status = spectral.get('status')
    if status not in ('certified_finite_weil_gates',
                      'certified_finite_isolated_prime_kernel_not_uniform'):
        raise ValueError('certified finite Weil gate required')
    with ctx.workprec(512):
        if status == 'certified_finite_weil_gates':
            even = arb_mat(_even_matrix(spectral))
        else:
            _, matrix, _ = certified_matrix(spectral['cutoff'], modes)
            even = arb_mat(matrix)
        values, raw_ground = isolated_spectrum(even)
        if status == 'certified_finite_isolated_prime_kernel_not_uniform' and [
                endpoints(value) for value in values] != spectral['even_spectrum']:
            raise ValueError('higher-mode isolated spectrum disagrees')
        norm = sum((value**2 for value in raw_ground), arb(0)).sqrt()
        if not norm > 0 or raw_ground[0].contains(0):
            raise ArithmeticError('ground orientation or norm unresolved')
        sign = 1 if raw_ground[0] > 0 else -1
        ground = [sign * value / norm for value in raw_ground]
        trial = [box(cell) for cell in exact_gate['projection_trial']['unit_coefficient_intervals']]
        if len(trial) != modes + 1 or not trial[0] > 0:
            raise ArithmeticError('prolate trial origin unresolved')
        error = Fraction(exact_gate['exact_to_trial_unit_coefficient_distance_upper'])
        trial_origin_lower = _lower(trial[0])
        exact_origin_lower = trial_origin_lower - error
        if exact_origin_lower <= 0:
            raise ArithmeticError('exact prolate origin unresolved')
        overlap = sum((a*b for a, b in zip(ground, trial)), arb(0))
        overlap_lower = _lower(overlap) - error
        if overlap_lower <= 0 or overlap_lower > 1:
            raise ArithmeticError('positive prolate-ground orientation unresolved')
        trial_distance = sum(((a-b)**2 for a, b in zip(ground, trial)), arb(0)).sqrt()
        distance_lower = max(Fraction(0), _lower(trial_distance) - error)
        distance_upper = _upper(trial_distance) + error
        if distance_upper >= exact_origin_lower:
            raise ArithmeticError('origin-normalized strip transfer unresolved')
        excited_mass_upper = 1 - overlap_lower**2
        length = arb(spectral['cutoff']).log()
        height = arb(2) / 5
        strip_weight = ((height * length).sinh() / (height * length)).sqrt()
        c = _ball(exact_origin_lower)
        d = _ball(distance_upper)
        strip_upper = _upper(strip_weight * d / (c - d) * (1 + 1 / c))
        trial_origin = _ball(trial_origin_lower)
        exact_trial_coefficient_error = (_ball(error) / (trial_origin - _ball(error))
                                         * (1 + 1 / trial_origin))
        # Both origin-normalized vectors have zeroth coordinate exactly one.
        normalized_difference = [arb(0)] + [
            ground[index] / ground[0] - trial[index] / trial[0]
            for index in range(1, modes + 1)]
        normalized_difference_norm = sum((value**2 for value in normalized_difference),
                                         arb(0)).sqrt()
        normalized_difference_lower = max(
            Fraction(0), _lower(normalized_difference_norm)
            - _upper(exact_trial_coefficient_error))
        coupled_strip_upper = _upper(strip_weight
                                     * (normalized_difference_norm
                                        + exact_trial_coefficient_error))
        profiles = {}
        for name, z, point_weight in (
                ('real_4', acb(4), arb(1)),
                ('real_8', acb(8), arb(1)),
                ('imag_1', acb(0, 1), (length.sinh() / length).sqrt())):
            functional = _fourier_functional(modes, length, z)
            ground_profile = sum((a*b for a, b in zip(ground, functional)), arb(0)) / ground[0]
            trial_profile = sum((a*b for a, b in zip(trial, functional)), arb(0)) / trial[0]
            trial_to_exact = _upper(point_weight * _ball(error)
                                    / (_ball(trial_origin_lower) - _ball(error))
                                    * (1 + 1 / _ball(trial_origin_lower)))
            difference = ground_profile - trial_profile
            exact_difference = difference + arb(0).union(
                _ball(-trial_to_exact)).union(_ball(trial_to_exact))
            profiles[name] = {
                'ground_profile': endpoints(ground_profile),
                'prolate_trial_profile': endpoints(trial_profile),
                'ground_minus_exact_prolate': endpoints(exact_difference),
                'absolute_difference_upper': str(_upper_abs(exact_difference)),
            }
        return {
            'status': 'certified_finite_prolate_ground_alignment_not_uniform',
            'cutoff': spectral['cutoff'], 'modes': modes,
            'ground_overlap_lower': str(overlap_lower),
            'squared_excited_mass_upper': str(excited_mass_upper),
            'unit_distance_lower': str(distance_lower),
            'unit_distance_upper': str(distance_upper),
            'exact_prolate_origin_lower': str(exact_origin_lower),
            'strip_height': '2/5',
            'uniform_strip_profile_difference_upper': str(strip_upper),
            'origin_normalized_coefficient_distance_upper': str(
                _upper(normalized_difference_norm) + _upper(exact_trial_coefficient_error)),
            'origin_normalized_coefficient_distance_lower': str(
                normalized_difference_lower),
            'coupled_uniform_strip_profile_difference_upper': str(coupled_strip_upper),
            'selected_profile_differences': profiles,
            'scope': ('One finite Fourier space; no increasing-rank or '
                      'increasing-support convergence bound.'),
        }


def run(exact_gate_path: Path, spectral_path: Path, cluster_path: Path | None,
        jacobi_path: Path, vectors_path: Path,
        candidate_path: Path | None = None) -> dict:
    exact_raw = exact_gate_path.read_bytes()
    spectral_raw = spectral_path.read_bytes()
    cluster_raw = None
    if cluster_path is not None:
        cluster_raw = cluster_path.read_bytes()
        cluster = cluster_run(exact_gate_path, spectral_path,
                              jacobi_path, vectors_path, candidate_path)
        if cluster != json.loads(cluster_raw):
            raise ValueError('saved prolate cluster certificate replay disagrees')
    result = certify(json.loads(exact_raw), json.loads(spectral_raw))
    result['input_sha256'] = {
        'exact_prolate_gate': hashlib.sha256(exact_raw).hexdigest(),
        'weil_spectrum': hashlib.sha256(spectral_raw).hexdigest(),
        **({'prolate_cluster': hashlib.sha256(cluster_raw).hexdigest()}
           if cluster_raw is not None else {}),
    }
    source_dir = Path(__file__).parent
    result['source_hashes'] = {
        name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
        for name in ('prolate_ground_alignment.py', 'prolate_cluster_gate.py',
                     'certified_weil.py', 'isolated_kernel.py',
                     'eigenvalue_response.py')}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exact-gate', type=Path, required=True)
    parser.add_argument('--spectrum', type=Path, required=True)
    parser.add_argument('--cluster', type=Path)
    parser.add_argument('--jacobi', type=Path, required=True)
    parser.add_argument('--vectors', type=Path, required=True)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.exact_gate, args.spectrum, args.cluster,
                 args.jacobi, args.vectors, args.candidate)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
