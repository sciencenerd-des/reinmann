"""Transfer exact prolate mode errors to the finite Weil Rayleigh gate.

This certifies only a finite cutoff and Fourier dimension. It does not
bound the continuous Weil ground state or any increasing-support path.
"""
from __future__ import annotations

from fractions import Fraction
import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_prolate_projection import _normalized_trial, project_trials
from certified_prolate_vectors import certify_trials
from robust_prolate_gate import robust_radius


def _ball(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


def _upper(value: arb) -> Fraction:
    return Fraction(str(value.upper().fmpq()))


def _read(path: Path) -> tuple[dict, str]:
    raw = path.read_bytes()
    return json.loads(raw), hashlib.sha256(raw).hexdigest()


def prolate_projection_error(cutoff: int, vectors: dict, projection: dict,
                             trials: dict) -> tuple[Fraction, Fraction, Fraction]:
    """Bound exact versus trial input, projected vector, and unit projection."""
    with ctx.workprec(1024):
        zero = _normalized_trial(trials['0']['trial_vector'])
        four = _normalized_trial(trials['2']['trial_vector'])
        center_zero_lower = Fraction(str(zero[0].lower().fmpq()))
        center_four_upper = Fraction(str(four[0].upper().fmpq()))
        eta_zero = Fraction(vectors['modes']['0']['oriented_unit_eigenvector_l2_error_upper'])
        eta_four = Fraction(vectors['modes']['2']['oriented_unit_eigenvector_l2_error_upper'])
        denominator = center_zero_lower - eta_zero
        if denominator <= 0 or center_four_upper <= 0:
            raise ArithmeticError('exact prolate center bound unresolved')
        ratio_upper = (center_four_upper + eta_four) / denominator
        ratio_error = (eta_four / denominator
                       + center_four_upper * eta_zero / (denominator * center_zero_lower))
        input_error = eta_four + ratio_upper * eta_zero + ratio_error
        # In the logarithmic L2 norm, sqrt(u) cancels dt=du/u:
        # ||sqrt(u) h(nu/sqrt(C))||^2 = sqrt(C)/n * ||h||^2
        # on the contributing subinterval. Sum n^(-1/2) <= 2sqrt(C)-1.
        map_norm = 2 * arb(cutoff).sqrt() - 1
        x_scale = arb(cutoff).sqrt().sqrt()
        projected_error = _upper(map_norm * x_scale * _ball(input_error))
        projected_norm_lower = Fraction(projection['projection_norm_interval']['lo'])
        if projected_error >= projected_norm_lower:
            raise ArithmeticError('exact candidate projection may vanish')
        exact_to_trial_unit = 2 * projected_error / (projected_norm_lower - projected_error)
        origin_lower = Fraction(projection['unit_coefficient_intervals'][0]['lo'])
        if projected_error >= origin_lower * projected_norm_lower:
            raise ArithmeticError('exact prolate orientation unresolved')
        return input_error, projected_error, exact_to_trial_unit


def certify(certificate: dict, candidate: dict, jacobi: dict, vectors: dict) -> dict:
    if certificate['cutoff'] != candidate['cutoff'] or certificate['cutoff'] != jacobi['cutoff'] or certificate['cutoff'] != vectors['cutoff']:
        raise ValueError('prolate and Weil cutoff mismatch')
    if vectors['even_legendre_terms'] != jacobi['even_legendre_terms']:
        raise ValueError('prolate Legendre dimension mismatch')
    trials = {key: {'trial_eigenvalue': mode['trial_eigenvalue'],
                    'trial_vector': mode['trial_vector']}
              for key, mode in vectors['modes'].items()}
    replay = certify_trials(jacobi, trials)
    if replay['modes'] != vectors['modes']:
        raise ValueError('stored prolate vector bounds disagree with Arb replay')
    exclusion = robust_radius(certificate, candidate)
    projection = project_trials(candidate['cutoff'], candidate['modes'],
                                trials['0']['trial_vector'], trials['2']['trial_vector'])
    input_error, projected_error, exact_to_trial_unit = prolate_projection_error(
        certificate['cutoff'], vectors, projection, trials)
    with ctx.workprec(1024):
        cutoff = certificate['cutoff']
        reference = [Fraction(x) for x in candidate['rounded_candidate_coefficients']]
        if len(reference) != len(projection['unit_coefficient_intervals']):
            raise ValueError('candidate Fourier dimension mismatch')
        distance_squared = sum((max(abs(Fraction(cell['lo']) - value),
                                    abs(Fraction(cell['hi']) - value)) ** 2
                                for cell, value in zip(projection['unit_coefficient_intervals'], reference)),
                               Fraction(0))
        trial_to_raw = _upper(_ball(distance_squared).sqrt())
        raw_norm = _ball(sum((value * value for value in reference), Fraction(0))).sqrt()
        raw_norm_correction = max(abs(Fraction(str(raw_norm.lower().fmpq())) - 1),
                                  abs(Fraction(str(raw_norm.upper().fmpq())) - 1))
        exact_to_rounded_unit = exact_to_trial_unit + trial_to_raw + raw_norm_correction
        radius = Fraction(exclusion['strict_unit_vector_l2_radius'])
        norm_upper = Fraction(exclusion['even_matrix_operator_norm_upper'])
        margin_lower = Fraction(exclusion['rayleigh_margin_lower'])
        exact_excess_lower = margin_lower - 2 * norm_upper * exact_to_rounded_unit
        passed = exact_excess_lower > 0
        return {
            'status': ('certified_exact_prolate_finite_rayleigh_above_second_even'
                       if passed else 'exact_prolate_finite_gate_inconclusive'),
            'cutoff': cutoff,
            'modes': candidate['modes'],
            'working_bits': 1024,
            'zero_integral_input_l2_error_upper': str(input_error),
            'projected_coefficient_l2_error_upper': str(projected_error),
            'exact_to_trial_unit_coefficient_distance_upper': str(exact_to_trial_unit),
            'trial_to_rounded_raw_coefficient_distance_upper': str(trial_to_raw),
            'rounded_normalization_correction_upper': str(raw_norm_correction),
            'exact_to_rounded_unit_coefficient_distance_upper': str(exact_to_rounded_unit),
            'robust_exclusion_radius': str(radius),
            'exact_rayleigh_excess_over_second_even_lower': str(exact_excess_lower),
            'rayleigh_above_second_even_certified': passed,
            'projection_trial': projection,
            'scope': ('For the exact normalized prolate combination in this finite '
                      'even Fourier space, Rayleigh exceeds the certified second '
                      'even Weil eigenvalue when the strict distance gate passes.'),
            'remaining': ('No all-mode or increasing-support exclusion, no continuous '
                          'Weil ground-state comparison, and no RH proof.'),
        }


def run(certificate_path: Path, candidate_path: Path,
        jacobi_path: Path, vectors_path: Path) -> dict:
    certificate, certificate_hash = _read(certificate_path)
    candidate, candidate_hash = _read(candidate_path)
    jacobi, jacobi_hash = _read(jacobi_path)
    vectors, vectors_hash = _read(vectors_path)
    if candidate['input_sha256'] != certificate_hash or vectors['jacobi_certificate_sha256'] != jacobi_hash:
        raise ValueError('input certificate provenance mismatch')
    source_dir = Path(__file__).parent
    for name, digest in certificate['source_hashes'].items():
        if hashlib.sha256((source_dir / name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale finite Weil certificate source')
    if hashlib.sha256((source_dir / 'prolate_candidate_diagnostic.py').read_bytes()).hexdigest() != candidate['generator_sha256']:
        raise ValueError('stale rounded-candidate generator')
    result = certify(certificate, candidate, jacobi, vectors)
    result['input_sha256'] = {
        'weil_certificate': certificate_hash,
        'rounded_candidate': candidate_hash,
        'prolate_jacobi': jacobi_hash,
        'prolate_vectors': vectors_hash,
    }
    result['generator_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--jacobi', type=Path, required=True)
    parser.add_argument('--vectors', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.certificate, args.candidate, args.jacobi, args.vectors)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
