"""Certify that the exact prolate candidate lies near a low Weil eigenspace.

This measures spectral-cluster membership at finite cutoff and rank.
It does not identify the ground eigenvector or prove a real-zero limit.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, arb_mat, ctx

from certified_weil import run as weil_run
from exact_prolate_finite_gate import run as low_prolate_run
from higher_mode_prolate_gate import run as high_prolate_run
from isolated_kernel import isolated_spectrum, run as isolated_run
from rank_schur_recurrence import _even_matrix


def _read(path: Path) -> tuple[bytes, dict]:
    raw = path.read_bytes()
    return raw, json.loads(raw)


def _fraction(record: dict[str, str], endpoint: str) -> Fraction:
    return Fraction(record[endpoint])


def certify(exact_gate: dict, spectrum: list[dict[str, str]],
            rayleigh_trial: dict[str, str], norm_upper: Fraction,
            unit_distance_upper: Fraction, retained: int = 4) -> dict:
    if retained < 1 or len(spectrum) <= retained:
        raise ValueError('spectral cluster dimension out of range')
    if norm_upper <= 0 or unit_distance_upper < 0:
        raise ValueError('positive operator norm and nonnegative error required')
    ground_lower = _fraction(spectrum[0], 'lo')
    threshold_lower = _fraction(spectrum[retained], 'lo')
    rayleigh_upper = _fraction(rayleigh_trial, 'hi') + 2 * norm_upper * unit_distance_upper
    if ground_lower <= 0 or not rayleigh_upper < threshold_lower:
        raise ArithmeticError('exact prolate cluster Rayleigh gate unresolved')
    # For unit w, mu >= lambda_0*(1-tail^2)+lambda_k*tail^2.
    # Since 0<lambda_0<mu<lambda_k, tail^2 <= mu/lambda_k.
    tail_mass_upper = rayleigh_upper / threshold_lower
    return {
        'status': 'certified_exact_prolate_low_cluster_not_ground',
        'cutoff': exact_gate['cutoff'], 'modes': exact_gate['modes'],
        'retained_even_eigenvectors': retained,
        'first_omitted_even_eigenvalue_lower': str(threshold_lower),
        'exact_prolate_rayleigh_upper': str(rayleigh_upper),
        'squared_mass_outside_cluster_upper': str(tail_mass_upper),
        'squared_mass_inside_cluster_lower': str(1 - tail_mass_upper),
        'scope': ('The exact finite prolate projection lies near the span of '
                  'the lowest even Weil modes, not necessarily the ground mode.'),
        'remaining': ('No all-rank or support-uniform cluster estimate, '
                      'real-zero theorem for cluster projections, or RH proof.'),
    }


def run(exact_gate_path: Path, spectral_path: Path,
        jacobi_path: Path, vectors_path: Path,
        candidate_path: Path | None = None) -> dict:
    exact_raw, exact_gate = _read(exact_gate_path)
    spectrum_raw, spectral = _read(spectral_path)
    source_dir = Path(__file__).parent
    if exact_gate['cutoff'] != spectral['cutoff'] or exact_gate['modes'] != spectral['modes']:
        raise ValueError('prolate and Weil support or rank mismatch')
    modes = spectral['modes']
    if spectral.get('status') == 'certified_finite_weil_gates':
        if candidate_path is None:
            raise ValueError('rounded candidate and certified finite Weil gate required')
        replay = low_prolate_run(spectral_path, candidate_path,
                                 jacobi_path, vectors_path)
        if replay != exact_gate:
            raise ValueError('exact low-mode prolate gate replay disagrees')
        candidate = json.loads(candidate_path.read_bytes())
        with ctx.workprec(512):
            regenerated = weil_run(spectral['cutoff'], modes)
            if json.loads(json.dumps(regenerated)) != spectral:
                raise ValueError('finite Weil matrix replay disagrees')
            even = arb_mat(_even_matrix(spectral))
            values, _ = isolated_spectrum(even)
            spectrum = [{'lo': str(value.lower().fmpq()),
                         'hi': str(value.upper().fmpq())} for value in values]
            norm_upper = max(
                sum((Fraction(str(abs(even[i, j]).upper().fmpq()))
                     for j in range(modes + 1)), Fraction(0))
                for i in range(modes + 1))
        rayleigh = candidate['exact_rounded_candidate_gate']['rayleigh_interval']
        distance = Fraction(exact_gate['exact_to_rounded_unit_coefficient_distance_upper'])
    elif spectral.get('status') == 'certified_finite_isolated_prime_kernel_not_uniform':
        if candidate_path is not None:
            raise ValueError('certified isolated higher-mode Weil gate required')
        replay = high_prolate_run(spectral_path, jacobi_path, vectors_path)
        if replay != exact_gate or isolated_run(spectral['cutoff'], modes) != spectral:
            raise ValueError('exact higher-mode prolate or Weil replay disagrees')
        spectrum = spectral['even_spectrum']
        rayleigh = exact_gate['trial_rayleigh_interval']
        norm_upper = Fraction(exact_gate['even_matrix_operator_norm_upper'])
        distance = Fraction(exact_gate['exact_to_trial_unit_coefficient_distance_upper'])
    else:
        raise ValueError('certified finite Weil spectrum required')
    result = certify(exact_gate, spectrum, rayleigh, norm_upper, distance)
    result['input_sha256'] = {
        'exact_prolate_gate': hashlib.sha256(exact_raw).hexdigest(),
        'weil_spectrum': hashlib.sha256(spectrum_raw).hexdigest(),
        'prolate_jacobi': hashlib.sha256(jacobi_path.read_bytes()).hexdigest(),
        'prolate_vectors': hashlib.sha256(vectors_path.read_bytes()).hexdigest(),
        **({'rounded_candidate': hashlib.sha256(candidate_path.read_bytes()).hexdigest()}
           if candidate_path is not None else {}),
    }
    result['source_hashes'] = {
        name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
        for name in ('prolate_cluster_gate.py', 'certified_weil.py',
                     'exact_prolate_finite_gate.py', 'higher_mode_prolate_gate.py',
                     'isolated_kernel.py', 'rank_schur_recurrence.py')}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exact-gate', type=Path, required=True)
    parser.add_argument('--spectrum', type=Path, required=True)
    parser.add_argument('--jacobi', type=Path, required=True)
    parser.add_argument('--vectors', type=Path, required=True)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.exact_gate, args.spectrum, args.jacobi,
                 args.vectors, args.candidate)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
