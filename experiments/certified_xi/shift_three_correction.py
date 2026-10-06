"""All-rank positive Xi correction curvature at fixed shift three only."""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

from dual_rank_budget import dual_grid
from laboratory import endpoints, interval, load_coefficients


def load_base(base_path: Path, coefficients_path: Path):
    base = json.loads(base_path.read_text())
    if base.get('status') != 'analytic_numerical_all_ranks_shift_three_not_all_shifts':
        raise ValueError('established shift-three pole certificate required')
    if base['input_sha256'] != hashlib.sha256(coefficients_path.read_bytes()).hexdigest():
        raise ValueError('coefficient input hash mismatch')
    for name, digest in base['source_hashes'].items():
        if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() != digest:
            raise ValueError(f'base certificate source mismatch: {name}')
    if [row['size'] for row in base['determinant_models']] != [1, 2, 3, 4]:
        raise ValueError('four leading determinant models required')
    models = base['determinant_models'][1:]
    weights = [interval(row['leading_weight']) for row in models]
    rates = [interval(row['leading_rate']) for row in models]
    terms = [[(Fraction(item['coefficient_upper']),
               Fraction(item['geometric_ratio_upper'])) for item in row['error_terms']]
             for row in models]
    if not all(w > 0 for w in weights) or not all(x > 0 for x in rates):
        raise ArithmeticError('positive leading determinant models unresolved')
    if any(not row or not all(c >= 0 and 0 < q < 1 for c, q in row)
           for row in terms):
        raise ValueError('decreasing geometric error terms required')
    amplitude = weights[0]*weights[2]/(3*weights[1]**2)
    rate = rates[0]*rates[2]/rates[1]**2
    if not amplitude > 0 or not 0 < rate < 1:
        raise ArithmeticError('positive separated leading ratio model unresolved')
    return base, amplitude, rate, terms


def log_error(terms, rank: int):
    if type(rank) is not int or rank < 4 or len(terms) != 3:
        raise ValueError('rank>=4 and size-2/3/4 error rows required')
    errors = [sum((arb(str(c))*arb(str(q))**rank for c, q in row), arb(0))
              for row in terms]
    if not all(0 <= value < 1 for value in errors):
        raise ArithmeticError('positive determinant clearance unresolved')
    return (-(-errors[0]).log1p()-2*(-errors[1]).log1p()
            -(-errors[2]).log1p())


def run(base_path: Path, coefficients_path: Path, head: int = 137) -> dict:
    if type(head) is not int or not 84 <= head <= 196:
        raise ValueError('integer correction head in 84..196 required')
    with ctx.workprec(2048):
        base, amplitude, rate, terms = load_base(base_path, coefficients_path)
        if head-1 < base['tail']['start_rank']:
            raise ValueError('three correction ranks must lie in pole tail')
        sigma_fraction = max(q for row in terms for _, q in row)
        sigma = arb(str(sigma_fraction))
        error = (log_error(terms, head-1)+2*log_error(terms, head)
                 +log_error(terms, head+1)).upper()
        scaled_error = error*(head+3)**2
        successive = sigma*(arb(head+4)/(head+3))**2
        upper = arb((head+3)**2)/((head+3)**2-1)+scaled_error
        if not successive < 1 or not scaled_error < arb('0.5') or not upper < arb('1.5'):
            raise ArithmeticError('uniform correction tail margins unresolved')

        mu, _ = load_coefficients(coefficients_path)
        grid = dual_grid(mu, max_rank=head, max_shift=3)
        bridge, weighted_lowers = [], []
        for rank in range(1, head):
            previous = grid[rank-1, 3] if rank > 1 else arb(1)
            correction = (2*grid[rank, 3].log()-previous.log()
                          -grid[rank+1, 3].log())
            weighted = correction*(rank+3)**2
            if not weighted > arb('0.1'):
                raise ArithmeticError('finite shift-three correction lower bound unresolved')
            weighted_lowers.append(weighted.lower())
            bridge.append({'rank': rank, 'correction': endpoints(correction),
                           'weighted_correction': endpoints(weighted)})
        first_slope = -grid[1, 3].log()
        beta = -rate.log()
        total = beta-first_slope
        if not total > 0:
            raise ArithmeticError('positive total correction unresolved')
        lower = min(weighted_lowers+[(1-scaled_error).lower()])
        sources = dict(base['source_hashes'])
        sources['shift_three_correction.py'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        return {
            'schema_version': 1,
            'status': 'analytic_numerical_positive_correction_all_ranks_shift_three',
            'head_rank': head,
            'shift': 3,
            'geometric_error_rate': str(sigma_fraction),
            'head_second_difference_error_upper': str(error.fmpq()),
            'scaled_tail_error_upper': str(scaled_error.upper().fmpq()),
            'successive_scaled_error_ratio_upper': str(successive.upper().fmpq()),
            'weighted_tail_upper': str(upper.upper().fmpq()),
            'weighted_global_lower': str(lower.fmpq()),
            'finite_bridge': bridge,
            'first_slope': endpoints(first_slope),
            'limiting_slope': endpoints(beta),
            'infinite_correction_sum': endpoints(total),
            'claim': f'C_r(3)>1/[10*(r+3)^2] for every integer r>=1; for r>={head}, 1/[2*(r+3)^2]<C_r(3)<3/[2*(r+3)^2].',
            'cumulative_identity': 'sum_(r=1)^infinity C_r(3)=beta-delta_1(3); every partial sum is positive.',
            'input_sha256': hashlib.sha256(coefficients_path.read_bytes()).hexdigest(),
            'base_certificate_sha256': hashlib.sha256(base_path.read_bytes()).hexdigest(),
            'source_hashes': sources,
            'trust_boundary': 'Five-pole certificate, geometric log-error bounds and FLINT balls; not Lean formalized.',
            'remaining': 'Only fixed shift three is covered. Negative Xi corrections occur at shift four; no all-shift interior budget or RH proof.',
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', required=True, type=Path)
    parser.add_argument('--coefficients', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    result = run(args.base, args.coefficients)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])
    print('weighted lower:', arb(result['weighted_global_lower']))


if __name__ == '__main__':
    main()
