"""Certify the finite residual-and-gap gate for an exact prolate projection.

The decimal Legendre trial is enclosed by the existing infinite-Jacobi and
analytic Fourier-projection certificates. This audit transfers their unit
vector error to both the Weil Rayleigh quotient and its operator residual.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_mode_comparison import box
from certified_weil import certified_matrix, endpoints
from higher_mode_prolate_gate import run as replay_prolate_gate
from isolated_kernel import isolated_spectrum


def _ball(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


def _lower(value: arb) -> Fraction:
    return Fraction(str(value.lower().fmpq()))


def _upper(value: arb) -> Fraction:
    return Fraction(str(value.upper().fmpq()))


def residual_gate(matrix, trial: list[arb], unit_error: Fraction,
                  lowest: arb, second: arb) -> dict:
    """Enclose exact unit-vector Rayleigh and residual from a trial unit vector.

    ``matrix`` and the spectral intervals must describe the same real
    symmetric operator. The caller verifies that provenance independently.
    """
    if len(trial) != len(matrix) or not 0 <= unit_error < 1:
        raise ValueError('matrix, unit trial, or error bound invalid')
    if not lowest > 0 or not second > lowest:
        raise ArithmeticError('positive isolated even gap unresolved')
    norm_squared = sum((entry**2 for entry in trial), arb(0))
    if not norm_squared.contains(1):
        raise ValueError('trial unit normalization is not enclosed')
    operator_bound = max(
        sum((_upper(abs(cell)) for cell in row), Fraction(0)) for row in matrix)
    product = [sum((cell * trial[j] for j, cell in enumerate(row)), arb(0))
               for row in matrix]
    mu = sum((trial[i] * product[i] for i in range(len(trial))), arb(0))
    trial_residual = sum(((product[i] - mu * trial[i])**2
                          for i in range(len(trial))), arb(0)).sqrt()
    # For unit v,w with ||v-w||<=eta and ||A||<=M,
    # |mu(v)-mu(w)|<=2M eta and ||r(v)-r(w)||<=4M eta.
    rayleigh_error = 2 * operator_bound * unit_error
    residual_error = 4 * operator_bound * unit_error
    exact_rayleigh = mu + _ball(Fraction(-rayleigh_error)).union(
        _ball(Fraction(rayleigh_error)))
    residual_lower = max(Fraction(0), _lower(trial_residual) - residual_error)
    residual_upper = _upper(trial_residual) + residual_error
    clearance = second - exact_rayleigh
    origin_lower = max(Fraction(0), _lower(abs(trial[0])) - unit_error)
    if clearance > 0:
        distance_upper = _upper(arb(2).sqrt() * _ball(residual_upper)
                                / _ball(_lower(clearance)))
        status = ('certified_finite_strip_transfer_inputs'
                  if origin_lower > distance_upper
                  else 'positive_clearance_origin_unresolved')
    else:
        distance_upper = None
        status = ('certified_above_second' if clearance < 0
                  else 'clearance_inconclusive')
    return {
        'trial_unit_norm_squared_interval': endpoints(norm_squared),
        'trial_rayleigh_interval': endpoints(mu),
        'exact_rayleigh_interval': endpoints(exact_rayleigh),
        'trial_residual_norm_interval': endpoints(trial_residual),
        'exact_residual_norm_enclosure': {
            'lo': str(residual_lower), 'hi': str(residual_upper)},
        'even_gap_interval': endpoints(second - lowest),
        'second_minus_exact_rayleigh_interval': endpoints(clearance),
        'exact_candidate_origin_lower': str(origin_lower),
        'ground_distance_upper_from_residual': (
            str(distance_upper) if distance_upper is not None else None),
        'origin_protected_by_residual': (origin_lower > distance_upper
                                         if distance_upper is not None else False),
        'operator_norm_upper': str(operator_bound),
        'unit_vector_error_upper': str(unit_error),
        'rayleigh_error_upper': str(rayleigh_error),
        'residual_error_upper': str(residual_error),
        'residual_and_gap_gate': status,
    }


def run(exact_gate_path: Path, isolated_path: Path,
        jacobi_path: Path, vectors_path: Path) -> dict:
    raw = {name: path.read_bytes() for name, path in (
        ('exact_prolate_gate', exact_gate_path), ('isolated_weil', isolated_path),
        ('prolate_jacobi', jacobi_path), ('prolate_vectors', vectors_path))}
    gate, isolated = (json.loads(raw[name]) for name in
                      ('exact_prolate_gate', 'isolated_weil'))
    replay = replay_prolate_gate(isolated_path, jacobi_path, vectors_path)
    if replay != gate:
        raise ValueError('exact prolate gate does not replay from its inputs')
    cutoff, modes = gate['cutoff'], gate['modes']
    with ctx.workprec(512):
        _, matrix, _ = certified_matrix(cutoff, modes)
        spectrum, _ = isolated_spectrum(matrix)
        if [endpoints(value) for value in spectrum] != isolated['even_spectrum']:
            raise ValueError('stored finite Weil spectrum differs from replay')
        trial = [box(cell) for cell in gate['projection_trial']['unit_coefficient_intervals']]
        result = residual_gate(
            matrix, trial,
            Fraction(gate['exact_to_trial_unit_coefficient_distance_upper']),
            spectrum[0], spectrum[1])
    result.update({
        'schema_version': 1,
        'status': 'certified_finite_exact_prolate_residual_gap_audit',
        'cutoff': cutoff, 'modes': modes, 'working_bits': 512,
        'input_sha256': {name: hashlib.sha256(blob).hexdigest()
                         for name, blob in raw.items()},
        'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                          for name in ('prolate_residual_gap_audit.py',
                                       'higher_mode_prolate_gate.py',
                                       'certified_prolate_projection.py',
                                       'certified_weil.py', 'isolated_kernel.py')},
        'scope': 'Exact prolate projection and certified even Weil matrix at one finite cutoff and rank.',
        'remaining': 'No positive residual clearance here, all-rank estimate, support limit, or RH proof.',
    })
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exact-gate', type=Path, required=True)
    parser.add_argument('--isolated', type=Path, required=True)
    parser.add_argument('--jacobi', type=Path, required=True)
    parser.add_argument('--vectors', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.exact_gate, args.isolated, args.jacobi, args.vectors)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['residual_and_gap_gate'])


if __name__ == '__main__':
    main()
