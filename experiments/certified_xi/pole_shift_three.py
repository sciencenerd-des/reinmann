"""Five-pole all-rank certificate at fixed shift three, not an RH proof.

The first four reciprocal poles control dual determinants of sizes 1..4;
the fifth pole is retained explicitly so the geometric error reaches the
finite coefficient bridge. The rank-three ratio is normalized as in the
existing dual-grid certificate.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx

from dual_rank_budget import dual_grid
from laboratory import endpoints, load_coefficients
from pole_boundary import certify_circle, evaluate, isolate_real_zero
from pole_shift_two import determinant_error_terms


def tail_bounds(rank, models, rates):
    if rank < 1:
        raise ValueError('positive rank required')
    errors = [sum((coefficient*ratio**rank for coefficient, ratio in terms), arb(0))
              for _, _, terms in models]
    if not all(error < 1 for error in errors):
        return False, errors, None, None
    w2, w3, w4 = [model[0] for model in models[1:]]
    q = rates[3]/rates[2]
    ratio_upper = ((rank+3)/arb(3)*w2*w4/w3**2*q**rank
                   *(1+errors[1])*(1+errors[3])/(1-errors[2])**2)
    next_factor = (rank+4)/arb(rank+3)*q
    return ratio_upper < 1 and next_factor < 1, errors, ratio_upper, next_factor


def run(path: Path) -> dict:
    with ctx.workprec(768):
        mu, _ = load_coefficients(path)
        if len(mu) != 201:
            raise ValueError('five-pole certificate requires coefficients 0..200')
        coefficients = [acb((-1)**n*mu[n]/mu[0]) for n in range(len(mu))]
        coefficients[0] = acb(1)
        radius, outer = arb(1150), arb(2300)
        s = arb('0.5')+outer.sqrt()
        majorant = s*(s-1)/2*arb.pi()**(-s/2)*(s/2).gamma()*s.zeta()/mu[0]
        tail = majorant/arb(2)**len(coefficients)
        if not radius/outer < arb(len(coefficients))/(len(coefficients)+1):
            raise ArithmeticError('derivative-tail monotonicity unresolved')
        derivative_tail = len(coefficients)*tail/radius
        lower, circle = certify_circle(coefficients, 1150, tail,
                                       expected=5, segments=512)
        derivative_coefficients = [(j+1)*coefficients[j+1]
                                   for j in range(len(coefficients)-1)]
        roots, amplitudes, root_records = [], [], []
        for lo, hi in ((199, 201), (441, 443), (624, 627),
                       (924, 927), (1083, 1087)):
            root, record = isolate_real_zero(coefficients, tail, lo, hi,
                                             width=Fraction(1, 10**18))
            derivative = (evaluate(derivative_coefficients, acb(root)).real
                          +arb(0, derivative_tail.upper()))
            if derivative.contains(0):
                raise ArithmeticError('simple pole derivative unresolved')
            amplitude = -1/(root*derivative)
            roots.append(root)
            amplitudes.append(amplitude)
            record.update(derivative=endpoints(derivative),
                          amplitude=endpoints(amplitude))
            root_records.append(record)
        if not all(0 < roots[j] < roots[j+1] for j in range(4)) or not roots[-1] < radius:
            raise ArithmeticError('real-pole ordering unresolved')
        if not all((-1)**j*amplitudes[j] > 0 for j in range(5)):
            raise ArithmeticError('alternating pole amplitudes unresolved')
        rates = [1/root for root in roots]
        remainder = (1/(lower-tail)
                     +sum((abs(amplitude)/(radius/root-1)
                           for amplitude, root in zip(amplitudes, roots)), arb(0)))
        models = [determinant_error_terms(m, amplitudes, rates, remainder, radius)
                  for m in (1, 2, 3, 4)]
        threshold, tail_record = None, None
        for rank in range(4, 197):
            passed, errors, ratio_upper, next_factor = tail_bounds(rank, models, rates)
            if passed:
                threshold = rank
                tail_record = {
                    'start_rank': rank,
                    'relative_determinant_errors': [endpoints(error) for error in errors],
                    'normalized_shift_three_ratio_upper': str(ratio_upper.upper().fmpq()),
                    'successive_upper_ratio': endpoints(next_factor),
                }
                break
        if threshold is None:
            raise ArithmeticError('five-pole tail does not overlap finite bridge')

        with ctx.workprec(2048):
            ratios = dual_grid(mu, max_rank=threshold-1, max_shift=3)
            bridge = []
            for rank in range(1, threshold):
                value = ratios[rank, 3]
                if not 0 < value < 1:
                    raise ArithmeticError('finite shift-three ratio unresolved')
                bridge.append({'rank': rank, 'normalized_ratio': endpoints(value)})

        return {
            'schema_version': 1,
            'status': 'analytic_numerical_all_ranks_shift_three_not_all_shifts',
            'input_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'source_hashes': {
                name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                for name in ('pole_shift_three.py', 'pole_shift_two.py', 'pole_boundary.py',
                             'dual_rank_budget.py', 'laboratory.py', 'coefficients.py')
            },
            'positive_majorant_radius': 2300,
            'positive_majorant': endpoints(majorant),
            'function_tail': endpoints(tail),
            'derivative_tail': endpoints(derivative_tail),
            'circle': circle,
            'poles': root_records,
            'remainder_constant': endpoints(remainder),
            'determinant_models': [
                {'size': size, 'leading_weight': endpoints(weight),
                 'leading_rate': endpoints(rate),
                 'error_terms': [
                     {'coefficient_upper': str(coefficient.upper().fmpq()),
                      'geometric_ratio_upper': str(ratio.upper().fmpq())}
                     for coefficient, ratio in terms]}
                for size, (weight, rate, terms) in enumerate(models, start=1)
            ],
            'tail': tail_record,
            'finite_bridge': bridge,
            'claim': 'For every integer r>=1, D_r(3)>0 and 0<t_r(3)<1.',
            'trust_boundary': 'Written five-pole, determinant and Cauchy proof with FLINT balls; not Lean formalized.',
            'remaining': 'No uniform all-shift interior budget or RH theorem.',
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    result = run(args.coefficients)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], 'tail begins at rank', result['tail']['start_rank'])


if __name__ == '__main__':
    main()
