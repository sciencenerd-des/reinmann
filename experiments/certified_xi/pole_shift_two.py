"""Three-pole, all-rank SHIFT-TWO certificate; no all-shift RH claim.

Residual determinant bounds preserve vanishing repeated rank-one columns.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
from itertools import combinations, permutations
import json
import math
from pathlib import Path
from flint import arb, acb, ctx
from pole_boundary import evaluate, certify_circle, isolate_real_zero
from laboratory import load_coefficients, endpoints
from dual_rank_budget import dual_grid


def pole_weight(amplitudes, rates, subset):
    size = len(subset)
    value = arb((-1)**(size*(size-1)//2))
    for i in subset:
        value *= amplitudes[i]
    for i, j in combinations(subset, 2):
        value *= (rates[i]-rates[j])**2/(rates[i]*rates[j])
    return value


def determinant_error_terms(size, amplitudes, rates, remainder, radius):
    if type(size) is not int or not 1 <= size <= len(rates) or len(rates) != len(amplitudes):
        raise ValueError('valid determinant size and equal pole arrays required')
    if not remainder > 0 or not radius > 0 or not all(x > 0 for x in rates):
        raise ValueError('positive remainder constant, radius and pole rates required')
    leading_set = tuple(range(size))
    leading = pole_weight(amplitudes, rates, leading_set)
    scale = math.prod(rates[i] for i in leading_set)
    if not leading > 0:
        raise ArithmeticError('positive leading determinant weight unresolved')
    terms = []
    for subset in combinations(range(len(rates)), size):
        if subset == leading_set:
            continue
        coefficient = abs(pole_weight(amplitudes, rates, subset))/leading
        ratio = math.prod(rates[i] for i in subset)/scale
        terms.append((coefficient, ratio))
    for k in range(1, size+1):
        for error_columns in combinations(range(size), k):
            pole_columns = [j for j in range(size) if j not in error_columns]
            # Repeated pole labels give proportional columns and exactly zero.
            for labels in permutations(range(len(rates)), len(pole_columns)):
                assigned = dict(zip(pole_columns, labels))
                coefficient = arb(0)
                for row_order in permutations(range(size)):
                    product = remainder**k
                    for col in range(size):
                        row = row_order[col]
                        if col in assigned:
                            label = assigned[col]
                            product *= abs(amplitudes[label])*rates[label]**(row-col)
                        else:
                            product *= radius**(col-row)
                    coefficient += product
                ratio = math.prod(rates[label] for label in labels)/radius**k/scale
                terms.append((coefficient/leading, ratio))
    if not all(c >= 0 and 0 < q < 1 for c, q in terms):
        raise ArithmeticError('decreasing normalized determinant error unresolved')
    return leading, scale, terms


def run(path):
    with ctx.workprec(768):
        mu, _ = load_coefficients(path)
        if len(mu) != 121:
            raise ValueError('certificate requires coefficients 0..120')
        coefficients = [acb((-1)**n*mu[n]/mu[0]) for n in range(len(mu))]
        coefficients[0] = acb(1)
        radius, outer = arb(800), arb(1600)
        s = arb('0.5')+outer.sqrt()
        majorant = s*(s-1)/2*arb.pi()**(-s/2)*(s/2).gamma()*s.zeta()/mu[0]
        tail = majorant/arb(2)**121
        derivative_tail = 121*tail/radius
        lower, circle = certify_circle(coefficients, 800, tail, expected=3, segments=512)
        derivative_coefficients = [(j+1)*coefficients[j+1] for j in range(120)]
        roots, amplitudes, root_records = [], [], []
        for lo, hi in ((199,201), (441,443), (624,627)):
            root, record = isolate_real_zero(coefficients, tail, lo, hi, width=Fraction(1,10**16))
            derivative = evaluate(derivative_coefficients, acb(root)).real+arb(0, derivative_tail.upper())
            if derivative.contains(0):
                raise ArithmeticError('simple pole derivative unresolved')
            amplitude = -1/(root*derivative)
            roots.append(root)
            amplitudes.append(amplitude)
            record.update(derivative=endpoints(derivative), amplitude=endpoints(amplitude))
            root_records.append(record)
        if not 0 < roots[0] < roots[1] < roots[2] < radius:
            raise ArithmeticError('pole ordering unresolved')
        if not amplitudes[0] > 0 or not amplitudes[1] < 0 or not amplitudes[2] > 0:
            raise ArithmeticError('alternating pole amplitudes unresolved')
        rates = [1/root for root in roots]
        remainder = 1/(lower-tail)+sum((abs(a)/(radius/root-1) for a,root in zip(amplitudes, roots)), arb(0))
        models = [determinant_error_terms(m, amplitudes, rates, remainder, radius) for m in (1,2,3)]
        threshold = None
        for r in range(3, 119):
            errors = [sum((c*q**r for c,q in terms), arb(0)) for _,_,terms in models]
            upper = 8*(r+2)*models[0][0]*models[2][0]/models[1][0]**2*(rates[2]/rates[1])**r
            decay = arb(r+3)/(r+2)*rates[2]/rates[1]
            if errors[0] < arb('0.5') and errors[1] < arb('0.5') and errors[2] < 1 and upper < 1 and decay < 1:
                threshold = r
                tail_record = {'start_rank': r, 'relative_determinant_errors': [endpoints(e) for e in errors],
                               'normalized_shift_two_ratio_upper': str(upper.upper().fmpq()),
                               'successive_upper_ratio': endpoints(decay)}
                break
        if threshold is None:
            raise ArithmeticError('tail does not overlap available coefficient bridge')
        with ctx.workprec(2048):
            grid = dual_grid(mu, max_rank=threshold-1, max_shift=2)
            bridge = []
            for r in range(1, threshold):
                t = grid[r,2]
                if not 0 < t < 1:
                    raise ArithmeticError('strict shift-two finite bridge unresolved')
                bridge.append({'rank': r, 'normalized_ratio': endpoints(t)})
        return {'schema_version': 1, 'status': 'analytic_numerical_all_ranks_shift_two_not_all_shifts',
                'input_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ('pole_shift_two.py','pole_boundary.py','dual_rank_budget.py','laboratory.py')},
                'positive_majorant_radius': 1600, 'positive_majorant': endpoints(majorant),
                'function_tail': endpoints(tail), 'derivative_tail': endpoints(derivative_tail),
                'circle': circle, 'poles': root_records, 'remainder_constant': endpoints(remainder),
                'determinant_models': [{'size': i+1, 'leading_weight': endpoints(w), 'leading_rate': endpoints(rate),
                                       'error_terms': [{'coefficient_upper': str(c.upper().fmpq()),
                                                        'geometric_ratio_upper': str(q.upper().fmpq())} for c,q in terms]}
                                      for i,(w,rate,terms) in enumerate(models)],
                'tail': tail_record, 'finite_bridge': bridge,
                'claim': 'For every integer r>=1, D_r(2)>0 and 0<t_r(2)<1.',
                'trust_boundary': 'Written pole-removal, determinant expansion and Cauchy proof with FLINT bounds; not Lean formalized.',
                'remaining': 'All other interior shifts and the uniform all-rank budget remain unproved; no RH theorem.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coefficients', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.coefficients)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], 'tail starts', result['tail']['start_rank'])


if __name__ == '__main__':
    main()
