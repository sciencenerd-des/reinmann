"""Certify a finite Weil boundary-constrained eigenvalue and susceptibility.

The spectral identity is finite-dimensional. No all-mode or Xi limit follows.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from certified_mode_comparison import box, normalized_vector
from certified_weil import inertia


def restricted_first(even: list[list[arb]], boundary: list[arb],
                     first: tuple[Fraction, Fraction],
                     second: tuple[Fraction, Fraction],
                     iterations: int = 120) -> tuple[Fraction, Fraction]:
    """Enclose the least eigenvalue on the boundary kernel by interval LDL."""
    size = len(even)
    if (size < 2 or any(len(row) != size for row in even) or
            len(boundary) != size or not boundary[0] > 0 or
            not first[1] < second[0] or iterations < 1):
        raise ValueError('simple-lowest even block and valid boundary required')
    ratios = [entry / boundary[0] for entry in boundary[1:]]
    h = [[even[i+1][j+1] - ratios[j]*even[i+1][0]
          - ratios[i]*even[0][j+1] + ratios[i]*ratios[j]*even[0][0]
          for j in range(size-1)] for i in range(size-1)]
    gram = [[ratios[i]*ratios[j] + (arb(1) if i == j else arb(0))
             for j in range(size-1)] for i in range(size-1)]

    def count_below(shift: Fraction) -> int:
        shifted = [[h[i][j] - arb(str(shift))*gram[i][j]
                    for j in range(size-1)] for i in range(size-1)]
        return inertia(shifted)[0]

    lo, hi = first[1], second[1]
    if count_below(lo) != 0 or count_below(hi) == 0:
        raise ArithmeticError('boundary-constrained eigenvalue not bracketed')
    for _ in range(iterations):
        mid = (lo + hi) / 2
        if count_below(mid) == 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


def run(certificate_path: Path, iterations: int = 120) -> dict:
    raw = certificate_path.read_bytes()
    certificate = json.loads(raw)
    if certificate.get('status') != 'certified_finite_weil_gates':
        raise ValueError('certified finite Weil gates required')
    for name, digest in certificate['source_hashes'].items():
        if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() != digest:
            raise ValueError('stale Weil certificate source')
    with ctx.workprec(512):
        modes = certificate['modes']
        full = [[box(value) for value in row] for row in certificate['matrix']]
        if len(full) != 2*modes+1 or any(len(row) != len(full) for row in full):
            raise ValueError('Weil matrix dimension mismatch')
        root_two = arb(2).sqrt()
        even = [[arb(0) for _ in range(modes+1)] for _ in range(modes+1)]
        even[0][0] = full[modes][modes]
        for i in range(1, modes+1):
            even[0][i] = even[i][0] = root_two*full[modes][modes+i]
            for j in range(1, modes+1):
                even[i][j] = full[modes+i][modes+j] + full[modes+i][modes-j]
        first_record = certificate['smallest_even_eigenvalue']
        second_record = certificate['second_even_eigenvalue']
        first = Fraction(first_record['lo']), Fraction(first_record['hi'])
        second = Fraction(second_record['lo']), Fraction(second_record['hi'])
        lo, hi = restricted_first(even, [arb(1)]+[root_two]*modes,
                                  first, second, iterations)
        margin_lo, margin_hi = lo-first[1], hi-first[0]
        if margin_lo <= 0 or hi >= second[0]:
            raise ArithmeticError('strict boundary-constrained spectral bracket unresolved')
        _, unit, _ = normalized_vector(certificate)
        boundary = abs(unit[0] + root_two*sum(unit[1:], arb(0)))
        if not boundary > 0:
            raise ArithmeticError('unit ground boundary unresolved')
        b_lo = Fraction(str(boundary.lower().fmpq()))
        b_hi = Fraction(str(boundary.upper().fmpq()))
        return {
            'schema_version': 1,
            'status': 'certified_finite_boundary_susceptibility_not_uniform',
            'cutoff': certificate['cutoff'], 'modes': modes,
            'bisection_iterations': iterations,
            'boundary_zero_first': {'lo': str(lo), 'hi': str(hi)},
            'boundary_zero_margin': {'lo': str(margin_lo), 'hi': str(margin_hi)},
            'unit_ground_boundary_abs': {'lo': str(b_lo), 'hi': str(b_hi)},
            'susceptibility': {'lo': str(b_lo*b_lo/margin_hi),
                               'hi': str(b_hi*b_hi/margin_lo)},
            'certificate_sha256': hashlib.sha256(raw).hexdigest(),
            'source_hashes': {
                name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                for name in ('boundary_susceptibility.py', 'certified_mode_comparison.py',
                             'certified_weil.py')},
            'scope': ('Finite even Weil matrix only. The susceptibility equals '
                      'a positive higher-eigenmode resolvent sum by the exact '
                      'boundary secular identity.'),
            'remaining': ('No growing-mode or support bound on the boundary '
                          'susceptibility, trace, gap, or prolate approximation.'),
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--iterations', type=int, default=120)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.certificate, args.iterations)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['modes'])


if __name__ == '__main__':
    main()
