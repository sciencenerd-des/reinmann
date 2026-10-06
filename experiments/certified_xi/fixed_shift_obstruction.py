"""Non-Xi deformation preserving finite data and fixed-shift all-rank bounds.

This is an obstruction to extrapolating the certificates, not a counterexample
for Xi or RH. The deformation does not preserve Xi's full theta identity.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from flint import arb, ctx
from laboratory import interval, endpoints, load_coefficients
from pole_shift_two import determinant_error_terms
from dual_rank_budget import dual_grid


def deformation_tail(pole_data, scale=3200, degree=122, start=45):
    if type(degree) is not int or degree < 122 or degree % 4 != 2:
        raise ValueError('integer degree>=122 congruent to 2 modulo 4 required')
    if type(start) is not int or start < 3:
        raise ValueError('integer tail start>=3 required')
    radius = arb(pole_data['circle']['radius'])
    L = arb(str(Fraction(scale)))
    if not L > radius:
        raise ValueError('deformation zeros must lie outside the certified disk')
    roots = [arb(row['lo']).union(arb(row['hi'])) for row in pole_data['poles']]
    if len(roots) != 3:
        raise ValueError('three certified poles required')
    amplitudes = [interval(row['amplitude'])/(1+(root/L)**degree)
                  for row,root in zip(pole_data['poles'], roots)]
    rates = [1/root for root in roots]
    lower = arb(pole_data['circle']['polynomial_modulus_lower'])-interval(pole_data['function_tail'])
    factor_lower = 1-(radius/L)**degree
    if not lower > 0 or not factor_lower > 0:
        raise ArithmeticError('deformed contour separation unresolved')
    remainder = 1/(lower*factor_lower)+sum((abs(a)/(radius/root-1)
                                          for a,root in zip(amplitudes, roots)), arb(0))
    models = [determinant_error_terms(m, amplitudes, rates, remainder, radius) for m in (1,2,3)]
    errors = [sum((c*q**start for c,q in terms), arb(0)) for _,_,terms in models]
    t1 = 8*(start+1)*models[1][0]/models[0][0]**2*(rates[1]/rates[0])**start
    t2 = 8*(start+2)*models[0][0]*models[2][0]/models[1][0]**2*(rates[2]/rates[1])**start
    decay1 = arb(start+2)/(start+1)*rates[1]/rates[0]
    decay2 = arb(start+3)/(start+2)*rates[2]/rates[1]
    passed = errors[0] < arb('0.5') and errors[1] < arb('0.5') and errors[2] < 1
    passed = passed and t1 < 1 and t2 < 1 and decay1 < 1 and decay2 < 1
    return {'status': 'deformed_fixed_shift_tail_bounds_pass' if passed else 'unresolved',
            'scale': str(Fraction(scale)), 'degree': degree, 'start_rank': start,
            'added_exact_nonreal_zero': 'i*scale',
            'preserved_coefficient_indices': [0, degree-1],
            'relative_determinant_errors': [endpoints(e) for e in errors],
            'shift_one_ratio_upper': str(t1.upper().fmpq()),
            'shift_two_ratio_upper': str(t2.upper().fmpq()),
            'successive_ratios': [endpoints(decay1), endpoints(decay2)],
            'contour_factor_lower': str(factor_lower.lower().fmpq()),
            'remainder_constant': endpoints(remainder)}


def run(pole_path, coefficient_path):
    with ctx.workprec(2048):
        data = json.loads(pole_path.read_text())
        if data.get('status') != 'analytic_numerical_all_ranks_shift_two_not_all_shifts':
            raise ValueError('certified shift-two source required')
        digest = hashlib.sha256(coefficient_path.read_bytes()).hexdigest()
        if digest != data['input_sha256']:
            raise ValueError('coefficient provenance mismatch')
        for name, expected in data['source_hashes'].items():
            if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() != expected:
                raise ValueError('source pole certificate is stale')
        result = deformation_tail(data)
        if result['status'] != 'deformed_fixed_shift_tail_bounds_pass':
            raise ArithmeticError('deformed infinite tail unresolved')
        mu, _ = load_coefficients(coefficient_path)
        grid = dual_grid(mu, max_rank=44, max_shift=2)
        bridge = []
        for r in range(1,45):
            for m in (1,2):
                if not 0 < grid[r,m] < 1:
                    raise ArithmeticError('inherited finite bridge unresolved')
                bridge.append({'rank': r, 'shift': m, 'ratio': endpoints(grid[r,m])})
        return {'schema_version': 1,
                'status': 'non_Xi_counterexample_to_fixed_shift_inference_not_RH_counterexample',
                'definition': 'E_tilde(z)=E(z)*(1+(z/3200)^122), F_tilde(z)=F(z)*(1+(z/3200)^122)',
                'tail': result, 'inherited_bridge': bridge,
                'source_pole_sha256': hashlib.sha256(pole_path.read_bytes()).hexdigest(),
                'coefficient_sha256': digest,
                'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ('fixed_shift_obstruction.py','pole_shift_two.py','dual_rank_budget.py','laboratory.py')},
                'preserved': 'Positive coefficients, first 122 Taylor coefficients, three certified interior zeros, and 0<t_r(1),t_r(2)<1 at every rank.',
                'not_preserved': 'The full Xi theta identity, zeta identity, and arithmetic origin. This is not Xi and is not an RH counterexample.',
                'conclusion': 'These fixed-shift all-rank certificates and the finite coefficient prefix do not alone force all folded zeros to be positive real.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--poles', type=Path, required=True)
    parser.add_argument('--coefficients', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.poles, args.coefficients)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])
    print('tail begins', result['tail']['start_rank'], 'bridge cells', len(result['inherited_bridge']))


if __name__ == '__main__':
    main()
