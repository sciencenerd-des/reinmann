"""Exact sufficient conditions for a two-sided neighboring-ratio tube.

Polynomial certificates cover every rank r>=R, not a rank grid. Xi envelope
and boundary hypotheses remain unproved. See RH_TWO_SIDED_RANK_TUBE_2026_09_20.md.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import fmpq, fmpq_poly, fmpq_mpoly_ctx


@dataclass(frozen=True)
class Envelope:
    amplitude: Fraction
    offset: Fraction

    def __post_init__(self):
        object.__setattr__(self, 'amplitude', Fraction(self.amplitude))
        object.__setattr__(self, 'offset', Fraction(self.offset))
        if self.amplitude <= 0:
            raise ValueError('positive rational amplitude required')

    def value(self, rank):
        if rank+self.offset <= 0:
            raise ValueError('positive envelope denominator required')
        return self.amplitude/(rank+self.offset)


def rational(value):
    value = Fraction(value)
    return fmpq(value.numerator, value.denominator)


def shifted_coefficients(poly, head):
    """Coefficients in powers of r-R. Their positivity is sufficient on r>=R."""
    return list(poly(fmpq_poly([head, 1])).coeffs())


def correction_polynomial(shift, center, left, right):
    r = fmpq_poly([0, 1])

    def numerator(j, envelope):
        return (r+j)*(r+rational(envelope.offset))-j*rational(envelope.amplitude)

    center_num = numerator(shift, center)
    left_num, right_num = numerator(shift-1, left), numerator(shift+1, right)
    return (center_num**2*(r+rational(left.offset))*(r+rational(right.offset))
            -((r+rational(center.offset))**2-1)*left_num*right_num)


def local_tube(head, shift, lower, upper):
    if type(head) is not int or type(shift) is not int or head < 1 or shift < 2:
        raise ValueError('integer head>=1 and interior shift>=2 required')
    if len(lower) != 3 or len(upper) != 3 or not all(isinstance(e, Envelope) for e in (*lower, *upper)):
        raise ValueError('three lower and three upper Envelope objects required')
    checks = {}
    for i, (lo, hi) in enumerate(zip(lower, upper)):
        if head+min(lo.offset, hi.offset) <= 1:
            raise ValueError('positive neighboring-step logarithm denominators required')
        r = fmpq_poly([0, 1])
        ordering = rational(hi.amplitude)*(r+rational(lo.offset))-rational(lo.amplitude)*(r+rational(hi.offset))
        checks[f'ordered_ratios_{i}'] = all(c >= 0 for c in shifted_coefficients(ordering, head))
        checks[f'upper_ratio_below_one_{i}'] = hi.value(head) < 1
        checks[f'ordered_slopes_{i}'] = hi.offset >= lo.offset
    lower_poly = correction_polynomial(shift, upper[1], lower[0], lower[2])
    upper_poly = -correction_polynomial(shift, lower[1], upper[0], upper[2])
    lower_coeffs = shifted_coefficients(lower_poly, head)
    upper_coeffs = shifted_coefficients(upper_poly, head)
    checks['lower_correction_polynomial'] = all(c >= 0 for c in lower_coeffs)
    checks['upper_correction_polynomial'] = all(c >= 0 for c in upper_coeffs)
    return {'status': 'conditional_two_sided_tube_pass' if all(checks.values()) else 'unresolved',
            'head_rank': head, 'shift': shift, 'conditions': checks,
            'lower_correction_shifted_coefficients': [str(c) for c in lower_coeffs],
            'upper_correction_shifted_coefficients': [str(c) for c in upper_coeffs],
            'polynomial_scope': 'All real r>=head_rank; zero polynomials pass exactly.',
            'hypotheses': 'Actual ratios and rank slopes start in the two-sided tube at every interior shift. Both exterior shift boundaries have positive determinant values and remain in their tubes at every later rank. The normalized recurrence and positive starting determinant rows hold.'}


def head_conditions(head, lower, upper, previous_lower, previous_upper, current_lower, current_upper):
    if type(head) is not int or head < 1 or not isinstance(lower, Envelope) or not isinstance(upper, Envelope):
        raise ValueError('positive integer head and lower/upper envelopes required')
    p0, p1, q0, q1 = map(Fraction, (previous_lower, previous_upper, current_lower, current_upper))
    if not 0 < p0 <= p1 or not 0 < q0 <= q1 or head+min(lower.offset, upper.offset) <= 1:
        raise ValueError('positive ordered ratio intervals and logarithm denominators required')
    lower_slope_ratio = (head+upper.offset)/(head+upper.offset-1)
    upper_slope_ratio = (head+lower.offset)/(head+lower.offset-1)
    return {'lower_curvature': q1 <= upper.value(head),
            'upper_curvature': q0 >= lower.value(head),
            'lower_slope': p0 >= lower_slope_ratio*q1,
            'upper_slope': p1 <= upper_slope_ratio*q0}


def repeated_root_identity():
    ring = fmpq_mpoly_ctx.get(('r', 'N', 'm'))
    r, N, m = ring.gens()
    k = N-m
    Q = (r+m)*(r+k)-m*k
    Qleft = (r+m-1)*(r+k+1)-(m-1)*(k+1)
    Qright = (r+m+1)*(r+k-1)-(m+1)*(k-1)
    polynomial = Q**2*(r+k+1)*(r+k-1)-((r+k)**2-1)*Qleft*Qright
    checks = {'central_numerator_factorization': Q == r*(r+N),
              'neighbor_numerator_factorizations': Qleft == r*(r+N) and Qright == r*(r+N),
              'joint_correction_polynomial_zero': polynomial == 0}
    if not all(checks.values()):
        raise ArithmeticError('symbolic repeated-root tube identity failed')
    return checks


def run(degree=6, head=4):
    if type(degree) is not int or degree < 4:
        raise ValueError('integer degree>=4 required')
    envelopes = {m: Envelope(Fraction(degree-m), Fraction(degree-m)) for m in range(1, degree)}
    rows = []
    for m in range(2, degree-1):
        triple = [envelopes[m+j] for j in (-1, 0, 1)]
        row = local_tube(head, m, triple, triple)
        center = envelopes[m]
        p, q = center.value(head-1), center.value(head)
        row['head_conditions'] = head_conditions(head, center, center, p, p, q, q)
        if row['status'] != 'conditional_two_sided_tube_pass' or not all(row['head_conditions'].values()):
            raise ArithmeticError('exact repeated-root tube failed')
        rows.append(row)
    return {'schema_version': 1, 'status': 'exact_repeated_root_two_sided_tube_checked',
            'symbolic_all_degree_identity': repeated_root_identity(),
            'degree': degree, 'head': head, 'interior_shifts': [2, degree-2], 'rows': rows,
            'boundary_control': 'At shifts 1 and N-1, t_r(m)=(N-m)/(r+N-m) for every r>=1, by the existing exact determinant proof.',
            'conclusion': 'Both correction polynomials vanish identically. The tube includes the exact logarithmic-growth model without forcing a positive limiting slope.',
            'remaining': 'No Xi two-sided envelopes, uniform all-shift parameter bounds, or exterior boundary tubes are certified here. RH is not proved.',
            'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                              for name in ('two_sided_rank_tube.py', 'repeated_root_rank_control.py')}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])


if __name__ == '__main__':
    main()
