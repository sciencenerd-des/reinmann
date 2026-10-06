"""All-rank positive Xi correction curvature at shift two only.

Written proof: RH_SHIFT_TWO_CORRECTION_2026_09_20.md. Does not assert
positive correction at other shifts or prove the interior all-rank budget.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx
from dual_rank_budget import dual_grid
from laboratory import endpoints, load_coefficients
from shift_two_exponential_tube import load_base, log_error


def run(base_path, coefficients_path, head=90):
    if type(head) is not int or not 46 <= head <= 113:
        raise ValueError('integer correction head in 46..113 required')
    with ctx.workprec(2048):
        base, _, rate, terms = load_base(base_path, coefficients_path)
        if head-1 < base['tail']['start_rank']:
            raise ValueError('all three correction ranks must lie in the pole tail')
        sigma_fraction = max(q for row in terms for _, q in row)
        sigma = arb(str(sigma_fraction))
        error = (log_error(terms, head-1)+2*log_error(terms, head)+log_error(terms, head+1)).upper()
        scaled_error = error*(head+2)**2
        ratio = sigma*(arb(head+3)/(head+2))**2
        upper_constant = arb((head+2)**2)/((head+2)**2-1)+scaled_error
        if not ratio < 1 or not scaled_error < arb('0.5') or not upper_constant < arb('1.5'):
            raise ArithmeticError('uniform correction tail margins unresolved')
        mu, _ = load_coefficients(coefficients_path)
        grid = dual_grid(mu, max_rank=head, max_shift=2)
        bridge = []
        weighted_lowers = []
        for r in range(1, head):
            previous = grid[r-1, 2] if r > 1 else arb(1)
            correction = 2*grid[r, 2].log()-previous.log()-grid[r+1, 2].log()
            weighted = correction*(r+2)**2
            if not weighted > arb('0.11'):
                raise ArithmeticError('finite correction lower bound unresolved')
            weighted_lowers.append(weighted.lower())
            bridge.append({'rank': r, 'correction': endpoints(correction),
                           'weighted_correction': endpoints(weighted)})
        first_slope = -grid[1, 2].log()
        beta = -rate.log()
        total = beta-first_slope
        if not total > 0:
            raise ArithmeticError('positive total correction unresolved')
        lower = min(weighted_lowers+[(1-scaled_error).lower()])
        sources = dict(base['source_hashes'])
        for name in ('shift_two_correction.py', 'shift_two_exponential_tube.py'):
            sources[name] = hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        return {'schema_version': 1,
                'status': 'analytic_numerical_positive_correction_all_ranks_shift_two',
                'head_rank': head, 'shift': 2,
                'geometric_error_rate': str(sigma_fraction),
                'head_second_difference_error_upper': str(error.fmpq()),
                'scaled_tail_error_upper': str(scaled_error.upper().fmpq()),
                'successive_scaled_error_ratio_upper': str(ratio.upper().fmpq()),
                'weighted_tail_upper': str(upper_constant.upper().fmpq()),
                'weighted_global_lower': str(lower.fmpq()),
                'finite_bridge': bridge,
                'first_slope': endpoints(first_slope), 'limiting_slope': endpoints(beta),
                'infinite_correction_sum': endpoints(total),
                'claim': f'C_r(2)>11/[100*(r+2)^2] for every integer r>=1. For r>={head}, 1/[2*(r+2)^2]<C_r(2)<3/[2*(r+2)^2].',
                'cumulative_identity': 'sum_(r=1)^infinity C_r(2)=beta-delta_1(2); every partial sum is positive and strictly increasing.',
                'remaining_cumulative_gain': 'For r>=head_rank, 1/[2*(r+2)]<beta-v_r(2)<3/[2*(r+1)].',
                'input_sha256': hashlib.sha256(coefficients_path.read_bytes()).hexdigest(),
                'base_certificate_sha256': hashlib.sha256(base_path.read_bytes()).hexdigest(),
                'source_hashes': sources,
                'remaining': 'Only shift two is covered. The all-shift interior rank budget and RH remain unproved; correction positivity fails at some other certified shifts.',
                'trust_boundary': 'Existing pole certificate, common logarithmic error bounds, explicit second differences, and FLINT arithmetic; not Lean formalized.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, required=True)
    parser.add_argument('--coefficients', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.base, args.coefficients)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])
    print('weighted lower:', arb(result['weighted_global_lower']))


if __name__ == '__main__':
    main()
