"""Exact radius around a rounded candidate that still fails the Weil gate.

This certificate gives a sufficient coefficient-accuracy threshold.
The separate exact-prolate transfer may establish inclusion in it.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from math import isqrt
from pathlib import Path

from prolate_candidate_diagnostic import _add, _interval, _multiply, certified_rayleigh


def _even_interval_matrix(certificate: dict) -> list[list[tuple[Fraction, Fraction]]]:
    modes = certificate['modes']
    matrix = [[_interval(cell) for cell in row] for row in certificate['matrix']]
    if len(matrix) != 2 * modes + 1 or any(len(row) != len(matrix) for row in matrix):
        raise ValueError('full Weil matrix dimension mismatch')
    scale = 10**60
    root = isqrt(2 * scale * scale)
    root_two = Fraction(root, scale), Fraction(root + 1, scale)
    even = []
    for i in range(modes + 1):
        row = []
        for j in range(modes + 1):
            if i == 0 and j == 0:
                cell = matrix[modes][modes]
            elif i == 0:
                cell = _multiply(root_two, matrix[modes][modes + j])
            elif j == 0:
                cell = _multiply(root_two, matrix[modes + i][modes])
            else:
                cell = _add(matrix[modes + i][modes + j],
                            matrix[modes + i][modes - j])
            row.append(cell)
        even.append(row)
    return even


def robust_radius(certificate: dict, candidate: dict) -> dict:
    if certificate.get('status') != 'certified_finite_weil_gates':
        raise ValueError('certified finite Weil matrix required')
    if candidate.get('cutoff') != certificate.get('cutoff') or candidate.get('modes') != certificate.get('modes'):
        raise ValueError('candidate and matrix parameters differ')
    if candidate.get('status') != 'rounded_finite_prolate_candidate_above_second_eigenvalue':
        raise ValueError('recorded rounded candidate has no exclusion gate')
    gate = certified_rayleigh(certificate, candidate['rounded_candidate_coefficients'])
    if gate != candidate.get('exact_rounded_candidate_gate'):
        raise ValueError('stored rounded-candidate gate disagrees with exact replay')
    if gate['rayleigh_above_second'] is not True:
        raise ValueError('rounded candidate is not certified above second')
    margin = Fraction(gate['rayleigh_interval']['lo']) - Fraction(gate['second_even_interval']['hi'])
    if margin <= 0:
        raise ValueError('positive Rayleigh margin is not certified')
    even = _even_interval_matrix(certificate)
    norm_upper = max(sum(max(abs(lo), abs(hi)) for lo, hi in row) for row in even)
    if norm_upper <= 0:
        raise ValueError('positive matrix norm bound required')
    radius = margin / (2 * norm_upper)
    return {
        'status': 'rounded_candidate_robust_exclusion_radius',
        'cutoff': certificate['cutoff'],
        'modes': certificate['modes'],
        'rayleigh_margin_lower': str(margin),
        'even_matrix_operator_norm_upper': str(norm_upper),
        'strict_unit_vector_l2_radius': str(radius),
        'strict_max_coordinate_radius_sufficient': str(radius / (certificate['modes'] + 1)),
        'scope': ('Every unit even coefficient vector at Euclidean distance strictly '
                  'below this radius from the normalized recorded rounded candidate '
                  'has Rayleigh quotient above the certified second even eigenvalue.'),
        'remaining': ('This radius certificate alone does not enclose the exact '
                      'prolate projection or prove an all-support gap or RH.'),
    }


def run(certificate_path: Path, candidate_path: Path) -> dict:
    certificate_bytes = certificate_path.read_bytes()
    candidate_bytes = candidate_path.read_bytes()
    certificate = json.loads(certificate_bytes)
    candidate = json.loads(candidate_bytes)
    if candidate.get('input_sha256') != hashlib.sha256(certificate_bytes).hexdigest():
        raise ValueError('candidate was not generated from this certified matrix')
    result = robust_radius(certificate, candidate)
    result['certificate_sha256'] = hashlib.sha256(certificate_bytes).hexdigest()
    result['candidate_sha256'] = hashlib.sha256(candidate_bytes).hexdigest()
    result['generator_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.certificate, args.candidate)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
