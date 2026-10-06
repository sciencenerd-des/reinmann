"""Xi-specific exponential boundary tube and all-rank positive shift-two slope.

Uses the established three-pole certificate; no additional real-zero
assumption. See RH_SHIFT_TWO_EXPONENTIAL_TUBE_2026_09_20.md.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx
from dual_rank_budget import dual_grid
from laboratory import endpoints, interval, load_coefficients


def load_base(path, coefficients_path):
    base = json.loads(path.read_text())
    if base.get('status') != 'analytic_numerical_all_ranks_shift_two_not_all_shifts':
        raise ValueError('established shift-two pole certificate required')
    if base['input_sha256'] != hashlib.sha256(coefficients_path.read_bytes()).hexdigest():
        raise ValueError('coefficient input hash mismatch')
    for name, digest in base['source_hashes'].items():
        if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() != digest:
            raise ValueError(f'base certificate source mismatch: {name}')
    if [row['size'] for row in base['determinant_models']] != [1, 2, 3]:
        raise ValueError('three leading determinant models required')
    terms = []
    rates = []
    weights = []
    for model in base['determinant_models']:
        weights.append(interval(model['leading_weight']))
        rates.append(interval(model['leading_rate']))
        row = [(Fraction(t['coefficient_upper']), Fraction(t['geometric_ratio_upper'])) for t in model['error_terms']]
        if not row or not all(c >= 0 and 0 < q < 1 for c, q in row):
            raise ValueError('positive decreasing geometric error terms required')
        terms.append(row)
    amplitude = weights[0]*weights[2]/(2*weights[1]**2)
    rate = rates[0]*rates[2]/rates[1]**2
    if not all(w > 0 for w in weights) or not all(x > 0 for x in rates) or not amplitude > 0 or not 0 < rate < 1:
        raise ArithmeticError('positive separated leading ratio model unresolved')
    return base, amplitude, rate, terms


def log_error(terms, rank):
    if type(rank) is not int or rank < 2:
        raise ValueError('integer rank at least two required')
    errors = [sum((arb(str(c))*arb(str(q))**rank for c, q in row), arb(0)) for row in terms]
    if not all(0 <= e < 1 for e in errors):
        raise ArithmeticError('positive determinant clearance unresolved')
    return -(-errors[0]).log1p()-2*(-errors[1]).log1p()-(-errors[2]).log1p()


def run(base_path, coefficients_path, head=60):
    if type(head) is not int or head < 46 or head > 113:
        raise ValueError('integer head in 46..113 required for the available bridge')
    with ctx.workprec(2048):
        base, amplitude, rate, terms = load_base(base_path, coefficients_path)
        if head-1 < base['tail']['start_rank']:
            raise ValueError('slope tail needs two consecutive valid pole-model ranks')
        sigma_fraction = max(q for row in terms for _, q in row)
        sigma = arb(str(sigma_fraction))
        K_prev, K_head = log_error(terms, head-1), log_error(terms, head)
        slope_error = (K_prev+K_head).upper()
        # Rational endpoints define explicit functions, with no correlated
        # parameter chosen differently at each later rank.
        A_lower, A_upper = amplitude.lower(), amplitude.upper()
        q_lower, q_upper = rate.lower(), rate.upper()
        beta_lower, beta_upper = -q_upper.log(), -q_lower.log()
        tail_slope_lower = beta_lower-(arb(head+2)/(head+1)).log()-slope_error
        head_curvature_lower = beta_lower*head-A_upper.log()-arb(head+2).log()-slope_error
        if not tail_slope_lower > 0 or not head_curvature_lower > 0:
            raise ArithmeticError('increasing positive lower boundary tube unresolved')
        mu, _ = load_coefficients(coefficients_path)
        grid = dual_grid(mu, max_rank=head, max_shift=2)
        bridge = []
        slopes = []
        for r in range(1, head):
            previous = grid[r-1, 2] if r > 1 else arb(1)
            current = grid[r, 2]
            slope = (previous/current).log()
            if not 0 < current < 1 or not slope > 0:
                raise ArithmeticError('finite shift-two slope bridge unresolved')
            slopes.append(slope)
            bridge.append({'rank': r, 'ratio': endpoints(current), 'rank_slope': endpoints(slope)})
        global_slope = min([s.lower() for s in slopes]+[tail_slope_lower.lower()])
        if not global_slope > arb('0.06085'):
            raise ArithmeticError('requested global slope constant unresolved')
        # A finite consistency check of the pole-model log error, not the
        # justification of the uniform geometric continuation.
        for r in (head-1, head):
            residual = grid[r, 2].log()-amplitude.log()-arb(r+2).log()-r*rate.log()
            if not abs(residual) < log_error(terms, r):
                raise ArithmeticError('direct determinant/model comparison unresolved')
        constants = {'amplitude_lower': A_lower, 'amplitude_upper': A_upper,
                     'rate_lower': q_lower, 'rate_upper': q_upper,
                     'slope_limit_lower': beta_lower.lower(), 'slope_limit_upper': beta_upper.upper(),
                     'head_log_error_upper': K_head.upper(),
                     'head_slope_error_upper': slope_error,
                     'tail_slope_lower': tail_slope_lower.lower(),
                     'head_curvature_lower': head_curvature_lower.lower(),
                     'global_slope_lower': global_slope.lower()}
        sources = dict(base['source_hashes'])
        sources['shift_two_exponential_tube.py'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        return {'schema_version': 1, 'status': 'analytic_numerical_all_rank_shift_two_slope_and_boundary_tube',
                'head_rank': head, 'shift': 2,
                'constants': {name: str(value.fmpq()) for name, value in constants.items()},
                'geometric_error_rate': str(sigma_fraction),
                'tube_width': 'W(r)=E*(1-sigma^(r-R+1))/(1-sigma), r>=R-1; E=head_slope_error_upper',
                'lower_curvature': 'g(r)=-log(A_upper)-log(r+2)-r*log(q_upper)-W(r)',
                'upper_curvature': 'h(r)=-log(A_lower)-log(r+2)-r*log(q_lower)+W(r)',
                'claim': 'For every r>=R, g(r)<=delta_r(2)<=h(r) and nabla g(r)<=v_r(2)<=nabla h(r). For every integer r>=1, v_r(2)>0.06085 and t_r(2)<=exp(-0.06085*r).',
                'finite_slope_bridge': bridge,
                'rational_lower_envelope_obstruction': 'No fixed a>0,k can satisfy a/(r+k)<=t_r(2) for all sufficiently large ranks.',
                'input_sha256': hashlib.sha256(coefficients_path.read_bytes()).hexdigest(),
                'base_certificate_sha256': hashlib.sha256(base_path.read_bytes()).hexdigest(),
                'source_hashes': sources,
                'trust_boundary': 'Existing three-pole proof plus explicit logarithm and geometric remainder bounds; not Lean formalized.',
                'remaining': 'Xi two-sided envelopes and comparison inequalities at all shifts m>=3 remain unproved. RH is not proved.'}


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
    print('global slope lower:', arb(result['constants']['global_slope_lower']))


if __name__ == '__main__':
    main()
