"""Conditional rank-tail budgets retaining the factorial baseline and shift.

A finite prefix is followed by an analytic infinite geometric tail bound.
No neighboring-factor or all-shift Xi hypothesis is inferred from a pass.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, ctx
from laboratory import load_coefficients, endpoints
from dual_rank_budget import dual_grid


def compensated_budget(rank, shift, delta, slope, steps=16):
    if any(type(x) is not int for x in (rank, shift, steps)) or rank < 1 or shift < 2 or not 0 <= steps <= 10000:
        raise ValueError('integer rank>=1, shift>=2, and 0<=steps<=10000 required')
    delta, slope = arb(delta), arb(slope)
    if not all(x.is_finite() and x > 0 for x in (delta, slope)):
        raise ValueError('positive finite head curvature and slope required')
    d, v = delta.lower(), slope.lower()
    b = v/2
    n = rank+shift
    corrections = arb(0)
    prefixes = []
    for j in range(steps):
        z = arb(shift)/(n+j)*(-d-j*b).exp()
        corrections += 2*(-z).log1p()
        # Sum_{k=0}^j log((n+k)^2/((n+k)^2-1)), exactly telescoped.
        baseline = (arb(n)*(n+j)/((n-1)*(n+j+1))).log()
        margin = v-b+baseline+corrections
        prefixes.append(margin)
    at_cutoff = v-b if steps == 0 else prefixes[-1]
    z = arb(shift)/(n+steps)*(-d-steps*b).exp()
    loss = 2*z/((1-z)*(-(-b).expm1()))
    tail_margin = at_cutoff-loss
    passed = all(p > 0 for p in prefixes) and tail_margin > 0
    return {'status': 'conditional_compensated_tail_pass' if passed else 'unresolved',
            'head_rank': rank, 'shift': shift, 'prefix_steps': steps,
            'head_curvature_lower': str(d.fmpq()), 'head_slope_lower': str(v.fmpq()),
            'sustained_slope_lower': str(b.lower().fmpq()),
            'prefix_margins': [endpoints(p) for p in prefixes],
            'infinite_residual_loss_upper': str(loss.upper().fmpq()),
            'tail_margin': endpoints(tail_margin),
            'hypothesis': 'Neighboring correction factors must remain positive at every later rank; uniform all-shift head conditions are not supplied.'}


def run(path):
    with ctx.workprec(2048):
        mu, _ = load_coefficients(path)
        ratios = dual_grid(mu)
        heads = []
        for m in range(2, 7):
            found = None
            for r in range(2, 114):
                delta = -ratios[r, m].log()
                slope = delta+ratios[r-1, m].log()
                if not delta > 0 or not slope > 0:
                    continue
                budget = compensated_budget(r, m, delta, slope)
                if budget['status'] == 'conditional_compensated_tail_pass':
                    found = budget
                    break
            heads.append(found or {'shift': m, 'status': 'no_passing_head_in_scanned_range'})
        return {'schema_version': 1, 'status': 'conditional_finite_head_witnesses_not_all_rank_Xi_proof',
                'scanned_ranks': [2, 113], 'heads': heads,
                'input_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ('compensated_rank_tail.py', 'dual_rank_budget.py', 'laboratory.py')},
                'remaining': 'Uniform compatible heads at every shift and the positive neighboring-factor hypothesis.'}


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
