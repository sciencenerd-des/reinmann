"""Conditional infinite rank-tail budgets from finite head data.

A passed head budget is not an unconditional Xi rank-tail certificate:
neighboring positive correction factors must hold throughout the tail.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, ctx
from laboratory import load_coefficients, endpoints
from dual_rank_budget import dual_grid


def tail_budget(delta, slope):
    delta, slope = arb(delta), arb(slope)
    if not all(x.is_finite() and x > 0 for x in (delta, slope)):
        raise ValueError('positive finite head curvature and rank slope required')
    d, v = delta.lower(), slope.lower()
    b = v/2
    # Use expm1 so a small positive head does not disappear in subtraction.
    q = (-d).exp()
    loss = 2*q/((-d).expm1()*(-b).expm1())
    margin = v-b-loss
    return {'status': 'conditional_tail_budget_pass' if margin > 0 else 'unresolved',
            'head_curvature_lower': str(d.fmpq()),
            'head_slope_lower': str(v.fmpq()),
            'sustained_slope_lower': str(b.lower().fmpq()),
            'total_negative_tail_bound': str(loss.upper().fmpq()),
            'margin': endpoints(margin),
            'hypothesis': 'At every subsequent correction rank, the neighboring correction factors are positive. A finite head does not establish this.'}


def run(coefficients_path, max_rank=113, max_shift=7):
    with ctx.workprec(2048):
        mu, _ = load_coefficients(coefficients_path)
        ratios = dual_grid(mu, max_rank=max_rank, max_shift=max_shift)
        rows = []
        for m in range(2, max_shift):
            earliest = None
            for rank in range(2, max_rank+1):
                delta = -ratios[rank, m].log()
                slope = delta+ratios[rank-1, m].log()
                if not delta > 0 or not slope > 0:
                    continue
                budget = tail_budget(delta, slope)
                if budget['status'] == 'conditional_tail_budget_pass':
                    earliest = {'shift': m, 'head_rank': rank, 'budget': budget}
                    break
            rows.append(earliest or {'shift': m, 'status': 'no_passing_head_in_scanned_range'})
        return {'schema_version': 1,
                'status': 'finite_heads_for_conditional_rank_tail_theorem',
                'max_rank': max_rank, 'ratio_shift_range': [1, max_shift],
                'heads': rows,
                'input_sha256': hashlib.sha256(coefficients_path.read_bytes()).hexdigest(),
                'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ('rank_tail_bootstrap.py', 'dual_rank_budget.py', 'laboratory.py')},
                'remaining': 'Uniform compatible head bounds at all shifts and positive neighboring correction factors on the tail; no unconditional all-rank Xi result.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.coefficients)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    for row in result['heads']:
        print(row['shift'], row.get('head_rank'), row.get('budget', {}).get('status', row.get('status')))


if __name__ == '__main__':
    main()
