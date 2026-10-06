"""Conditional rank-tail comparison with an explicit logarithmic barrier.

Exact rational head tests; no all-shift or neighboring-factor assumption
is inferred from a finite pass. See RH_LOGARITHMIC_RANK_TAIL_2026_09_20.md.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import ctx
from dual_rank_budget import dual_grid
from laboratory import load_coefficients


def logarithmic_head(rank, shift, ratio_upper, previous_ratio_lower):
    if type(rank) is not int or type(shift) is not int or rank < 1 or shift < 2:
        raise ValueError('integer rank>=1 and shift>=2 required')
    q, p = Fraction(ratio_upper), Fraction(previous_ratio_lower)
    if q <= 0 or p <= 0:
        raise ValueError('positive rational ratio bounds required')
    n = rank+shift
    amplitude_margin = 1-shift*n*q
    slope_margin = (n-1)*p-n*q
    passed = amplitude_margin >= 0 and slope_margin >= 0
    return {'status': 'conditional_logarithmic_tail_pass' if passed else 'unresolved',
            'head_rank': rank, 'shift': shift,
            'current_ratio_upper': str(q), 'previous_ratio_lower': str(p),
            'amplitude_margin': str(amplitude_margin),
            'slope_cross_product_margin': str(slope_margin),
            'ratio_barrier': 't_(R+j)(m)<=q*(R+m)/(R+m+j), for every j>=0',
            'slope_barrier': 'delta_(R+j)-delta_(R+j-1)>=log((R+m+j)/(R+m+j-1))',
            'structural_limit': 'Strictly positive neighboring t values yield an additional persistent positive slope after one step. This criterion still excludes the repeated-root logarithmic-growth control.',
            'hypothesis': 'The recurrence holds, all relevant t values stay positive, and both neighboring B factors stay positive at every later rank. Actual head ratios obey the supplied one-sided bounds.',
            'remaining': 'Uniform all-shift heads and neighboring-factor control for Xi are not established.'}


def run(path):
    with ctx.workprec(2048):
        mu, _ = load_coefficients(path)
        ratios = dual_grid(mu)
        heads = []
        for m in range(2, 7):
            for r in range(2, 114):
                q = str(ratios[r, m].upper().fmpq())
                p = str(ratios[r-1, m].lower().fmpq())
                result = logarithmic_head(r, m, q, p)
                if result['status'] == 'conditional_logarithmic_tail_pass':
                    heads.append(result)
                    break
            else:
                heads.append({'shift': m, 'status': 'no_passing_head_in_scanned_range'})
        return {'schema_version': 1,
                'status': 'finite_heads_for_conditional_logarithmic_comparison',
                'heads': heads, 'scanned_ranks': [2, 113],
                'input_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ('logarithmic_rank_tail.py', 'dual_rank_budget.py', 'laboratory.py')},
                'remaining': 'Uniform Xi head estimates and simultaneous neighboring positivity; RH is not proved.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.coefficients)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    for row in result['heads']:
        print(row['shift'], row.get('head_rank'), row['status'])


if __name__ == '__main__':
    main()
