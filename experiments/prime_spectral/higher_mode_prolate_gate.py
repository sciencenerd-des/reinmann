"""Certify the exact prolate Rayleigh gate at higher Fourier dimensions.

Recompute the prime-defined interval matrix and its isolated spectrum,
then transfer the infinite-prolate eigenfunction error to its projection.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_mode_comparison import box
from certified_prolate_projection import project_trials
from certified_prolate_vectors import certify_trials
from certified_weil import certified_matrix, endpoints
from exact_prolate_finite_gate import prolate_projection_error
from isolated_kernel import isolated_spectrum


def certify(isolated: dict, jacobi: dict, vectors: dict) -> dict:
    if isolated.get('status') != 'certified_finite_isolated_prime_kernel_not_uniform':
        raise ValueError('certified higher-mode Weil spectrum required')
    cutoff, modes = isolated['cutoff'], isolated['modes']
    if cutoff != jacobi['cutoff'] or cutoff != vectors['cutoff'] or modes < 2:
        raise ValueError('prolate and Weil support or dimension mismatch')
    trials = {key: {'trial_eigenvalue': mode['trial_eigenvalue'],
                    'trial_vector': mode['trial_vector']}
              for key, mode in vectors['modes'].items()}
    replay = certify_trials(jacobi, trials)
    if replay['modes'] != vectors['modes']:
        raise ValueError('stored prolate vector bounds disagree with Arb replay')
    with ctx.workprec(512):
        _, even, odd = certified_matrix(cutoff, modes)
        even_spectrum, _ = isolated_spectrum(even)
        odd_spectrum, _ = isolated_spectrum(odd)
        if ([endpoints(value) for value in even_spectrum] != isolated['even_spectrum'] or
                [endpoints(value) for value in odd_spectrum] != isolated['odd_spectrum']):
            raise ValueError('stored prime spectrum disagrees with matrix replay')
        if not even_spectrum[0] > 0 or not odd_spectrum[0] > even_spectrum[0]:
            raise ArithmeticError('positive simple-even Weil ground unresolved')
    projection = project_trials(cutoff, modes,
                                trials['0']['trial_vector'], trials['2']['trial_vector'])
    input_error, projected_error, unit_error = prolate_projection_error(
        cutoff, vectors, projection, trials)
    with ctx.workprec(1024):
        unit_trial = [box(cell) for cell in projection['unit_coefficient_intervals']]
        trial_rayleigh = sum((unit_trial[i] * even[i][j] * unit_trial[j]
                              for i in range(modes + 1) for j in range(modes + 1)), arb(0))
        norm_upper = max(sum((Fraction(str(abs(cell).upper().fmpq())) for cell in row), Fraction(0))
                         for row in even)
        excess_lower = (Fraction(str(trial_rayleigh.lower().fmpq()))
                        - Fraction(str(even_spectrum[1].upper().fmpq()))
                        - 2 * norm_upper * unit_error)
        if excess_lower <= 0:
            raise ArithmeticError('exact-prolate higher-mode Rayleigh gate unresolved')
        return {
            'status': 'certified_exact_prolate_higher_mode_rayleigh_above_second_even',
            'cutoff': cutoff, 'modes': modes, 'working_bits': 1024,
            'trial_rayleigh_interval': endpoints(trial_rayleigh),
            'second_even_interval': isolated['even_spectrum'][1],
            'even_matrix_operator_norm_upper': str(norm_upper),
            'zero_integral_input_l2_error_upper': str(input_error),
            'projected_coefficient_l2_error_upper': str(projected_error),
            'exact_to_trial_unit_coefficient_distance_upper': str(unit_error),
            'exact_rayleigh_excess_over_second_even_lower': str(excess_lower),
            'projection_trial': projection,
            'scope': ('The exact projected prolate candidate has Rayleigh quotient '
                      'above the second even eigenvalue of this certified finite '
                      'prime-defined Weil matrix.'),
            'remaining': ('No increasing-support exclusion or prolate-to-Weil '
                          'ground-state comparison; RH remains open.'),
        }


def run(isolated_path: Path, jacobi_path: Path, vectors_path: Path) -> dict:
    isolated_raw = isolated_path.read_bytes()
    jacobi_raw = jacobi_path.read_bytes()
    vectors_raw = vectors_path.read_bytes()
    isolated, jacobi, vectors = map(json.loads,
                                    (isolated_raw, jacobi_raw, vectors_raw))
    source_dir = Path(__file__).parent
    for name, digest in isolated['source_hashes'].items():
        if hashlib.sha256((source_dir / name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale higher-mode Weil source')
    if vectors['jacobi_certificate_sha256'] != hashlib.sha256(jacobi_raw).hexdigest():
        raise ValueError('prolate Jacobi provenance mismatch')
    result = certify(isolated, jacobi, vectors)
    result['input_sha256'] = {
        'isolated_weil': hashlib.sha256(isolated_raw).hexdigest(),
        'prolate_jacobi': hashlib.sha256(jacobi_raw).hexdigest(),
        'prolate_vectors': hashlib.sha256(vectors_raw).hexdigest(),
    }
    result['generator_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--isolated', type=Path, required=True)
    parser.add_argument('--jacobi', type=Path, required=True)
    parser.add_argument('--vectors', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.isolated, args.jacobi, args.vectors)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
