"""Coefficientwise common-remainder jets and sharper curvature transfer.

See RH_COEFFICIENTWISE_CURVATURE_2026_09_20.md for the continuum proof.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

from flint import arb, arb_series, ctx
from cubic_gaussian_tail import fourth_order_constants, uniform_cubic_tail
from gaussian_jet_bound import gaussian_polynomials


def coefficientwise_constants(threshold_u):
    u, a, _, k3, k5, coefficients, raw, conditions = fourth_order_constants(threshold_u)
    l, b, c = coefficients
    d = k5-27*b**3-12*b*c
    eps, T = (u/a).sqrt(), 1/(a*u).sqrt()
    hermite = gaussian_polynomials(T, 4)
    ce = arb_series([sum((hermite[i]*raw[k-i]/(math.factorial(i)*math.factorial(k-i))
                         for i in range(k+1)), arb(0)) for k in range(5)], prec=5)
    mt = gaussian_polynomials(arb_series([T, 1], prec=5), 9)
    p = l*mt[1]+b*mt[3]
    q2 = c*mt[4]+l*l*mt[2]/2+l*b*mt[4]+b*b*mt[6]/2
    q3 = ((d+l*c)*mt[5]+b*c*mt[7]+l**3*mt[3]/6
          +l*l*b*mt[5]/2+l*b*b*mt[7]/2+b**3*mt[9]/6+3*mt[1])
    rest = q2+q3*eps+ce*eps**2
    w = p*eps+q2*eps**2+q3*eps**3+ce*eps**4
    if not w[0] < 1:
        raise ArithmeticError('coefficientwise logarithm constant unresolved')
    result = ce+p*(q3+ce*eps)+rest**2/2+p*p*rest
    result += p*eps*rest**2+eps**2*rest**3/3
    result += (p+q2*eps+q3*eps**2+ce*eps**3)**4/(4*(1-w))
    bounds = [result[k] for k in range(5)]
    if not all(value > 0 for value in bounds):
        raise ArithmeticError('positive coefficientwise majorant unresolved')
    return u, a, bounds, k3, k5, coefficients, conditions


def uniform_coefficientwise_tail(threshold_u=6):
    with ctx.workprec(512):
        legacy = uniform_cubic_tail(threshold_u)
        u, a, C, k3, k5, (l, b, c), _ = coefficientwise_constants(threshold_u)
        T2 = 1/(a*u)
        second, fourth = 6*c+3*l*b+18*b*b, c+arb('4.5')*b*b
        AH = arb(9)/(4*u)
        AL = 9*(4+7/u+1/u**2)/(8*u)
        AM = (arb(45)/4*(8+24/u+14/u**2+1/u**3)/(16*u)+arb(9)/(16*u**3)
              +arb(81)/2*(4+6/u+1/u**2)**2/(32*u)
              +54*(4+6/u+1/u**2)/(32*u**2)+arb(243)/(128*a*u**3))
        H = 1+AH+2*second+6*b/u+12*fourth*T2+(6*k3+20*k5*T2+2*C[2]*u)/a
        K = 2+AL+24*fourth/u+6*k3+60*k5*T2+6*C[3]*(u/a).sqrt()
        M = 6+AM+120*k5/u+24*C[4]
        h = 4*u/(1+2*u)
        deficit = h-(H+3)/a
        Lmax, Mmax = 2+K/a, 4+M/a
        if not deficit > 0:
            raise ArithmeticError('positive uniform reference deficit unresolved')
        q_sensitivity = Mmax/deficit**2+2*Lmax**2/deficit**3
        l_sensitivity = 2*Lmax/deficit**2
        reference = q_sensitivity*(H+3)+l_sensitivity*K+M/deficit+6+4/h
        margin_factor = (2+1/u)**4/4
        reference_budget = margin_factor*reference*u*u/a
        true_budget = arb(legacy['upper_bounds']['true_additional_relative_budget'])
        conditions = {key: value for key, value in legacy['conditions'].items()
                      if key not in ('negative_log_q', 'first_log_q_derivative',
                                     'second_log_q_derivative', 'strict_negative_margin')}
        conditions.update({
            'log_q_clearance': H/a < arb('0.1'),
            'reference_deficit': deficit > arb('0.5'),
            # Preserve the earlier true-transfer hypotheses and constants.
            'first_log_q_derivative': K/a < 1,
            'second_log_q_derivative': M/a < 1,
            'strict_negative_margin': reference_budget+true_budget < 1,
        })
        constants = {'anchor_threshold': a, 'H_error_constant': H,
                     'L_error_constant': K, 'M_error_constant': M,
                     'q_sensitivity_constant': q_sensitivity,
                     'L_sensitivity_constant': l_sensitivity,
                     'M_sensitivity_constant': 1/deficit,
                     'reference_relative_budget': reference_budget,
                     'true_additional_relative_budget': true_budget,
                     'combined_relative_budget': reference_budget+true_budget}
        sources = dict(legacy['source_hashes'])
        sources['coefficientwise_curvature.py'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        return {'schema_version': 1, 'u_threshold': str(Fraction(threshold_u)),
                'status': 'uniform_coefficientwise_tail_pass' if all(conditions.values()) else 'unresolved',
                'conditions': conditions,
                'upper_bounds': {key: str(value.upper().fmpq()) for key, value in constants.items()},
                'scaled_deficit_lower': str(deficit.lower().fmpq()),
                'log_jet_coefficient_bounds': [str(value.upper().fmpq()) for value in C],
                'derivative_bound': '|E_a^(j)(y)|<=j!*C_j*(u/a)^2/(a*u)^(j/2), j=0,...,4, |y-a|<=1',
                'scope': 'Every real anchor with W(2a/pi)/2>=u_threshold; requires the accompanying written analytic proof.',
                'source_hashes': sources,
                'remaining': 'Lower-anchor bridge and uniform all-shift interior rank budget; RH is not proved.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--threshold-u', default='6')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = uniform_coefficientwise_tail(args.threshold_u)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])
    print('combined relative budget:', arb(result['upper_bounds']['combined_relative_budget']))


if __name__ == '__main__':
    main()
