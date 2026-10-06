"""Exact all-rank control showing a limit of positive-slope tail bootstraps.

For (1+z/N)^N, delta_r(m)=log(1+r/(N-m)), not linear in rank.
This is a limitation of a sufficient method, not a Xi counterexample.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


def parameters(degree, shift):
    if type(degree) is not int or type(shift) is not int or degree < 4 or not 2 <= shift <= degree-2:
        raise ValueError('integer degree>=4 and 2<=shift<=degree-2 required')


def normalized_minor(degree, rank, shift):
    if any(type(x) is not int for x in (degree, rank, shift)) or degree < 1 or rank < 0 or shift < 0:
        raise ValueError('positive integer degree and nonnegative integer rank/shift required')
    result = Fraction(1)
    for i in range(1, shift+1):
        for j in range(1, rank+1):
            result *= Fraction(degree+j-i, degree)
    return result


def control(degree=6, shift=3, head=4, steps=20):
    parameters(degree, shift)
    if type(head) is not int or type(steps) is not int or head < 1 or steps < 0:
        raise ValueError('positive integer head and nonnegative integer steps required')
    K = degree-shift
    x = K+head
    correction_product = Fraction(1)
    for j in range(steps):
        correction_product *= Fraction((x+j-1)*(x+j+1), (x+j)**2)
    expected = Fraction((x-1)*(x+steps), x*(x+steps-1))
    if correction_product != expected:
        raise ArithmeticError('exact cumulative correction identity failed')
    return {
        'schema_version': 1,
        'status': 'exact_control_excludes_positive_uniform_tail_slope',
        'degree': degree, 'shift': shift, 'head': head, 'prefix_steps': steps,
        'generating_polynomial': '(1+z/N)^N; sole zero -N has multiplicity N',
        'all_rank_formulas': {
            'normalized_minor': 'A_r(m)=N^(-r*m)*product_(i=1)^m product_(j=1)^r (N+j-i)',
            't': 't_r(m)=(N-m)/(N-m+r)',
            'B': 'B_r(m)=(N+r)/(N-m+r)',
            'delta': 'delta_r(m)=log(1+r/(N-m))',
            'exp_correction': 'exp(C_r(m))=1-1/(N-m+r)^2',
            'tail_slope': 'delta_r-delta_(r-1)=log((N-m+r)/(N-m+r-1)) -> 0',
            'infinite_correction_sum': 'sum_(r=R)^infinity C_r=-log((N-m+R)/(N-m+R-1))',
        },
        'exact_prefix_correction_product': str(correction_product),
        'exact_prefix_slope_exponential': str(Fraction(x, x-1)*correction_product),
        'conclusion': 'The existing scalar and compensated criteria cannot pass any head of this control with sustained slope b>0. Their conclusions would contradict its exact sublinear growth.',
        'trust_boundary': 'Written induction and elementary logarithm limits; exact rational regression checks are not the all-rank proof.',
        'remaining': 'This does not decide Xi heads or the RH question; it identifies an additional growth requirement of the sufficient criterion.',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = control()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])


if __name__ == '__main__':
    main()
