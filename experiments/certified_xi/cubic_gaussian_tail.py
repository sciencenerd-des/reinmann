"""Third-order Gaussian cancellation and a fourth-order common remainder.

Written uniform proof: RH_CUBIC_GAUSSIAN_TAIL_2026_09_20.md.
This supplies a curvature tail, not an all-rank or RH theorem.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

from flint import arb, ctx, fmpq_mpoly_ctx
from common_remainder import derivative_bound
from gaussian_jet_bound import gaussian_polynomials
from gaussian_tail_bound import gaussian_absolute_moments
from high_order_saddle import stirling_row
from laboratory import interval


def cubic_identity():
    ring = fmpq_mpoly_ctx.get(('t', 'l', 'b', 'c', 'd', 'g'))
    t, l, b, c, d, g = ring.gens()
    moments = [ring.constant(1), t]
    for k in range(1, 9):
        moments.append(t*moments[k]+k*moments[k-1])
    p1 = l*moments[1]+b*moments[3]
    p2 = c*moments[4]+l*l*moments[2]/2+l*b*moments[4]+b*b*moments[6]/2
    p3 = ((d+l*c)*moments[5]+b*c*moments[7]+l**3*moments[3]/6
          +l*l*b*moments[5]/2+l*b*b*moments[7]/2+b**3*moments[9]/6+g*moments[1])
    expected = ((3*l*l*b+36*l*b*b+12*l*c+135*b**3+96*b*c+15*d+g)*t
                +(18*l*b*b+4*l*c+144*b**3+84*b*c+10*d)*t**3
                +(27*b**3+12*b*c+d)*t**5)
    if p3-p1*p2+p1**3/3 != expected:
        raise ArithmeticError('exact cubic logarithm cancellation failed')
    return {'degree_seven_and_nine_cancel': True,
            'cubic_log_polynomial': str(expected),
            'fourth_derivative_at_zero': '0'}


def add(*polys):
    result = {}
    for poly in polys:
        for degree, coefficient in poly.items():
            result[degree] = result.get(degree, arb(0))+coefficient
    return result


def scale(poly, coefficient):
    return {k: coefficient*v for k, v in poly.items()}


def multiply(first, second):
    result = {}
    for i, ci in first.items():
        for j, cj in second.items():
            result[i+j] = result.get(i+j, arb(0))+ci*cj
    return result


def power(poly, exponent):
    result = {0: arb(1)}
    for _ in range(exponent):
        result = multiply(result, poly)
    return result


def fourth_order_constants(threshold_u):
    U = Fraction(threshold_u)
    if U < 6:
        raise ValueError('Lambert coordinate threshold at least 6 required')
    u = arb(str(U))
    a = arb.pi()*u*(2*u).exp()
    eps, window = (u/a).sqrt(), (32*u).sqrt()
    T, h = 1/(a*u).sqrt(), (8/a).sqrt()
    l = arb('2.25')+1/(2*u)
    b = (4+6/u+1/u**2)/24
    c = (8+24/u+14/u**2+1/u**3)/192
    phase = {j: sum((arb(s)*arb(2)**(k-j)*u**(k-j)
                    for k, s in enumerate(stirling_row(j))), arb(0))/math.factorial(j)
             for j in range(5, 17)}
    d = phase[5]
    f1, f2, f3 = {1: l, 3: b}, {4: c}, {5: d}
    f = add(f1, scale(f2, eps), scale(f3, eps**2))
    r6 = {j: phase[j]*eps**(j-6) for j in range(6, 17)}
    B = sum((v*window**k for k, v in f.items()), arb(0))*eps
    R = sum((v*window**k for k, v in r6.items()), arb(0))*eps**4
    amplitude = 3*(h.exp()/(4*u)+(2*h).exp()*(eps*h.exp()*window).exp()/2)
    central = scale(add(r6, {2: amplitude}), (B+R).exp())
    # gamma*s*(exp(V)-1), with |gamma|<=3*epsilon^3.
    central = add(central, scale(multiply({1: arb(3)}, add(f, scale(r6, eps**3))), (B+R).exp()))
    central = add(central, scale(power(f, 4), B.exp()/24))
    central = add(central, multiply(f1, f3), scale(power(f2, 2), arb('0.5')),
                  scale(multiply(f2, f3), eps), scale(power(f3, 2), eps**2/2))
    rest = add(f2, scale(f3, eps))
    central = add(central, scale(multiply(power(f1, 2), rest), arb('0.5')),
                  scale(multiply(f1, power(rest, 2)), eps/2), scale(power(rest, 3), eps**2/6))
    moments = gaussian_absolute_moments(24)
    raw = []
    for k in range(5):
        value = sum((v*moments[n+k] for n, v in central.items()), arb(0))
        tail_sum = sum((arb(math.factorial(n)//math.factorial(n-j))*2**(j+1)*window**(n-2*j-1)
                        for n in range(k, k+10) for j in range(n+1)), arb(0))
        tail = 2*arb.pi()**2*(-12*u).exp()*tail_sum
        raw.append((T*window).exp()*(value+tail))
    hermite = gaussian_polynomials(T, 4)
    Ce = sum((hermite[i]*raw[k-i]/(math.factorial(i)*math.factorial(k-i))
              for k in range(5) for i in range(k+1)), arb(0))
    mt = gaussian_polynomials(1+T, 9)
    p = l*mt[1]+b*mt[3]
    q2 = c*mt[4]+l*l*mt[2]/2+l*b*mt[4]+b*b*mt[6]/2
    q3 = ((d+l*c)*mt[5]+b*c*mt[7]+l**3*mt[3]/6
          +l*l*b*mt[5]/2+l*b*b*mt[7]/2+b**3*mt[9]/6+3*mt[1])
    w = p*eps+q2*eps**2+q3*eps**3+Ce*eps**4
    if not w < 1:
        raise ArithmeticError('fourth-order logarithm jet unresolved')
    rest_norm = q2+q3*eps+Ce*eps**2
    C = Ce+p*(q3+Ce*eps)+rest_norm**2/2+p*p*rest_norm
    C += p*eps*rest_norm**2+eps**2*rest_norm**3/3
    C += (p+q2*eps+q3*eps**2+Ce*eps**3)**4/(4*(1-w))
    k3 = 18*l*b*b+4*l*c+144*b**3+84*b*c+10*d
    k5 = 27*b**3+12*b*c+d
    nonconstant = (eps*(l+b)+eps**2*(c+(l+b)**2/2)
                   +eps**3*(d+(l+b)*c+(l+b)**3/6+3))
    conditions = {'positive_amplitude': arb('1.5')*eps**2 < arb('0.5'),
                  'tail_tangent': T < window/2,
                  'gaussian_polynomial_coefficients': nonconstant < 1,
                  'logarithm_jet': w < 1}
    return u, a, C, k3, k5, (l, b, c), raw, conditions


def uniform_cubic_tail(threshold_u=7):
    with ctx.workprec(512):
        u, a, C, k3, k5, coefficients, raw, conditions = fourth_order_constants(threshold_u)
        l, b, c = coefficients
        T2 = 1/(a*u)
        second = 6*c+3*l*b+18*b*b
        fourth = c+arb('4.5')*b*b
        A_H = arb(9)/(4*u)
        A_L = 9*(4+7/u+1/u**2)/(8*u)
        A_M = (arb(45)/4*(8+24/u+14/u**2+1/u**3)/(16*u)+arb(9)/(16*u**3)
               +arb(81)/2*(4+6/u+1/u**2)**2/(32*u)
               +54*(4+6/u+1/u**2)/(32*u**2)+arb(243)/(128*a*u**3))
        H = 1+A_H+2*second+6*b/u+12*fourth*T2
        H += (6*k3+20*k5*T2+2*C*u)/a
        K = 2+A_L+24*fourth/u+6*k3+60*k5*T2+6*C*(u/a).sqrt()
        M = 6+A_M+120*k5/u+24*C
        reference = 532*(3*H+10)+40*K+2*M+100
        margin_factor = (2+1/u)**4/4
        reference_budget = margin_factor*reference*u*u/a
        base = derivative_bound(10**6)
        tau = interval(base['saddle_bound']['constants']['gaussian_tail_exponent'])
        u0 = (arb(2)*10**6/arb.pi()).lambertw()/2
        errors = [arb(row['absolute_upper'])*(u/u0)**16
                  *(arb(10**6)/a)**(arb(7)+arb(row['order'])/2)
                  for row in base['derivatives'][2:]]
        e2, e3, e4 = errors
        true_budget = margin_factor*u*u*(4500*a*e2+108*a*a*e3+3*a**3*e4)
        conditions.update({
            'denominator_perturbation': arb(9)/(8*a) < arb(1)/1000,
            'true_remainder_power_decay': tau >= arb(7)/16 and tau <= arb('0.5'),
            'negative_log_q': H/a < arb(1)/3,
            'first_log_q_derivative': K/a < 1,
            'second_log_q_derivative': M/a < 1,
            'true_deficit_clearance': a*e2 < arb(1)/12,
            'true_first_derivative': a*a*e3 < 1,
            'true_second_derivative': a**3*e4 < 1,
            'strict_negative_margin': reference_budget+true_budget < 1,
        })
        constants = {'anchor_threshold': a, 'fourth_order_log_jet_constant': C,
                     'odd_cubic_coefficient_bound': k3, 'odd_quintic_coefficient_bound': k5,
                     'H_error_constant': H, 'L_error_constant': K, 'M_error_constant': M,
                     'reference_relative_budget': reference_budget,
                     'true_additional_relative_budget': true_budget,
                     'combined_relative_budget': reference_budget+true_budget}
        return {
            'schema_version': 1, 'u_threshold': str(Fraction(threshold_u)),
            'status': 'uniform_cubic_tail_majorants_pass' if all(conditions.values()) else 'unresolved',
            'exact_identity': cubic_identity(), 'conditions': conditions,
            'upper_bounds': {key: str(value.upper().fmpq()) for key, value in constants.items()},
            'raw_derivative_error_constants': [str(v.upper().fmpq()) for v in raw],
            'derivative_bound': '|E_a^(j)(y)|<=j!*C*(u/a)^2/(a*u)^(j/2), j=0,...,4, |y-a|<=1',
            'scope': 'Every real anchor with W(2a/pi)/2>=u_threshold, subject to the accompanying written analytic proof.',
            'remaining': 'Lower-anchor bridge and uniform interior all-rank budget; RH is not proved.',
            'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                              for name in ('cubic_gaussian_tail.py', 'gaussian_jet_bound.py', 'gaussian_tail_bound.py',
                                           'common_remainder.py', 'high_order_saddle.py',
                                           'decaying_theta.py', 'laboratory.py', 'coefficients.py')},
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--threshold-u', default='7')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = uniform_cubic_tail(args.threshold_u)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])
    print('combined relative budget:', arb(result['upper_bounds']['combined_relative_budget']))


if __name__ == '__main__':
    main()
