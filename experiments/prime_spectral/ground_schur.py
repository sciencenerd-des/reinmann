"""Origin-normalized ground profiles from a constrained Weil resolvent.

The exact Schur identity uses the existing certified simple-even gate.
Interval residual containment alone is not used to infer an eigenvector.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, acb, arb_mat, ctx

from certified_mode_comparison import box, normalized_vector
from certified_weil import endpoints, inertia
from quotient_operator import fourier_profile


def origin_schur_vector(certificate: dict) -> tuple[list[arb], arb]:
    """Return (1, -(C-lambda_0 I)^-1 b) and its first-row residual.

    Requires a certified simple even lowest eigenvalue with nonzero origin.
    The constrained block is positive; its interval LDL is checked here.
    """
    if certificate.get('status') != 'certified_finite_weil_gates':
        raise ValueError('certified finite Weil gates required')
    modes = certificate['modes']
    if type(modes) is not int or modes < 1:
        raise ValueError('positive Fourier mode count required')
    matrix = [[box(value) for value in row] for row in certificate['matrix']]
    if len(matrix) != 2 * modes + 1 or any(len(row) != len(matrix) for row in matrix):
        raise ValueError('finite Weil matrix dimension mismatch')
    lam = box(certificate['smallest_even_eigenvalue'])
    root_two = arb(2).sqrt()
    coupling = [root_two * matrix[modes][modes + index]
                for index in range(1, modes + 1)]
    constrained = [[matrix[modes + i][modes + j]
                    + matrix[modes + i][modes - j]
                    - (lam if i == j else 0)
                    for j in range(1, modes + 1)]
                   for i in range(1, modes + 1)]
    if inertia(constrained)[0] != 0:
        raise ArithmeticError('positive origin-constrained Weil block unresolved')
    tail = arb_mat(constrained).solve(arb_mat([[-value] for value in coupling]))
    origin = [arb(1)] + [tail[index, 0] for index in range(modes)]
    if not all(value.is_finite() for value in origin):
        raise ArithmeticError('finite origin-normalized ground vector unresolved')
    first_row_residual = (matrix[modes][modes] - lam
                          + sum((coupling[index] * origin[index + 1]
                                 for index in range(modes)), arb(0)))
    if not first_row_residual.contains(0):
        raise ArithmeticError('ground-state Schur consistency unresolved')
    return origin, first_row_residual


def run(certificate_path: Path) -> dict:
    raw = certificate_path.read_bytes()
    certificate = json.loads(raw)
    source_dir = Path(__file__).parent
    for name, digest in certificate['source_hashes'].items():
        if hashlib.sha256((source_dir / name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale finite Weil certificate source: ' + name)
    with ctx.workprec(512):
        origin, residual = origin_schur_vector(certificate)
        existing_origin = normalized_vector(certificate)[2]
        if not all((a - b).contains(0) for a, b in zip(origin, existing_origin)):
            raise ArithmeticError('independent origin-normalized vectors disagree')
        root_two = arb(2).sqrt()
        modes = certificate['modes']
        coefficients = ([origin[index] / root_two
                         for index in range(modes, 0, -1)]
                        + [arb(1)]
                        + [origin[index] / root_two
                           for index in range(1, modes + 1)])
        length = arb(certificate['cutoff']).log()
        profiles = {}
        for name, argument in (('real_4', arb(4)), ('real_8', arb(8)),
                               ('imag_1', acb(0, 1))):
            value = fourier_profile(coefficients, length, argument)
            if not value.imag.contains(0):
                raise ArithmeticError('even-profile reality unresolved')
            profiles[name] = endpoints(value.real)
        widths = []
        for new, old in zip(origin[1:], existing_origin[1:]):
            new_box, old_box = endpoints(new), endpoints(old)
            new_width = Fraction(new_box['hi']) - Fraction(new_box['lo'])
            old_width = Fraction(old_box['hi']) - Fraction(old_box['lo'])
            if not new_width > 0 or not old_width > 0:
                raise ArithmeticError('positive interval-width comparison unresolved')
            widths.append(old_width / new_width)
        return {
            'status': 'certified_finite_origin_schur_profile_not_convergence',
            'cutoff': certificate['cutoff'], 'modes': modes,
            'origin_normalized_even_vector': [endpoints(value) for value in origin],
            'first_row_residual': endpoints(residual),
            'profile': profiles,
            'minimum_old_to_schur_coordinate_width_ratio': str(min(widths)),
            'input_sha256': hashlib.sha256(raw).hexdigest(),
            'source_hashes': {
                name: hashlib.sha256((source_dir / name).read_bytes()).hexdigest()
                for name in ('ground_schur.py', 'certified_mode_comparison.py',
                             'certified_weil.py', 'quotient_operator.py')},
            'scope': ('One certified finite Weil matrix; no growing-mode or '
                      'growing-support profile convergence.'),
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.certificate)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
