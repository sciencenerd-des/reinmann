"""Absorb the linear phase exactly before bounding the common remainder.

Proof: RH_SHIFTED_GAUSSIAN_CURVATURE_2026_09_20.md. No all-rank RH claim.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

from flint import arb, arb_series, ctx
from common_remainder import derivative_bound
from cubic_gaussian_tail import add, multiply, power, scale, cubic_identity
from gaussian_jet_bound import gaussian_polynomials
from gaussian_tail_bound import gaussian_absolute_moments
from high_order_saddle import stirling_row
from laboratory import interval


def shifted_constants(threshold):
    X = Fraction(threshold)
    if X < 10**6:
        raise ValueError('anchor threshold at least 1000000 required')
    a = arb(str(X))
    u = (2*a/arb.pi()).lambertw()/2
    eps, window = (u/a).sqrt(), (32*u).sqrt()
    h = (8/a).sqrt()
    l = arb('2.25')+1/(2*u)
    tilt_factor = l+1/u
    T = eps*tilt_factor  # |t+lambda|, including the real neighboring tilt.
    b = (4+6/u+1/u**2)/24
    c = (8+24/u+14/u**2+1/u**3)/192
    phase = {j: sum((arb(s)*arb(2)**(k-j)*u**(k-j)
                    for k, s in enumerate(stirling_row(j))), arb(0))/math.factorial(j)
             for j in range(5, 17)}
    d = phase[5]
    # The linear phase is in exp((t+lambda)*s), not in the perturbation.
    f1, f2, f3 = {3: b}, {4: c}, {5: d}
    f = add(f1, scale(f2, eps), scale(f3, eps**2))
    r6 = {j: phase[j]*eps**(j-6) for j in range(6, 17)}
    B = eps*sum((v*window**k for k, v in f.items()), arb(0))
    R = eps**4*sum((v*window**k for k, v in r6.items()), arb(0))
    amplitude = 3*(h.exp()/(4*u)+(2*h).exp()*(eps*h.exp()*window).exp()/2)
    central = scale(add(r6, {2: amplitude}), (B+R).exp())
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
    ce = arb_series([sum((hermite[i]*raw[k-i]/(math.factorial(i)*math.factorial(k-i))
                         for i in range(k+1)), arb(0)) for k in range(5)], prec=5)
    mt = gaussian_polynomials(arb_series([T, 1], prec=5), 9)
    p = b*mt[3]
    q2 = c*mt[4]+b*b*mt[6]/2
    q3 = d*mt[5]+b*c*mt[7]+b**3*mt[9]/6+3*mt[1]
    rest = q2+q3*eps+ce*eps**2
    w = p*eps+q2*eps**2+q3*eps**3+ce*eps**4
    if not w[0] < 1:
        raise ArithmeticError('shifted logarithm constant unresolved')
    majorant = ce+p*(q3+ce*eps)+rest**2/2+p*p*rest
    majorant += p*eps*rest**2+eps**2*rest**3/3
    majorant += (p+q2*eps+q3*eps**2+ce*eps**3)**4/(4*(1-w))
    bounds = [majorant[k] for k in range(5)]
    if not all(value > 0 for value in bounds):
        raise ArithmeticError('positive shifted jet majorant unresolved')
    k3 = 144*b**3+84*b*c+10*d
    k5 = 27*b**3+12*b*c+d
    nonconstant = eps*b+eps**2*(c+b*b/2)+eps**3*(d+b*c+b**3/6+3)
    conditions = {'lambert_domain': u > 5,
                  'positive_amplitude': arb('1.5')*eps**2 < arb('0.5'),
                  'tail_tangent': T < window/2,
                  'gaussian_polynomial_coefficients': nonconstant < 1,
                  'logarithm_constant': w[0] < 1}
    return u, a, bounds, k3, k5, b, c, tilt_factor, conditions


def uniform_shifted_curvature(threshold=10**6):
    with ctx.workprec(512):
        u, a, C, k3, k5, b, c, vtilt, conditions = shifted_constants(threshold)
        eps2 = u/a
        T2 = eps2*vtilt**2
        second, fourth = 6*c+18*b*b, c+arb('4.5')*b*b
        AH = arb(9)/(4*u)
        AL = 9*(4+7/u+1/u**2)/(8*u)
        AM = (arb(45)/4*(8+24/u+14/u**2+1/u**3)/(16*u)+arb(9)/(16*u**3)
              +arb(81)/2*(4+6/u+1/u**2)**2/(32*u)
              +54*(4+6/u+1/u**2)/(32*u**2)+arb(243)/(128*a*u**3))
        H = 1+AH+6*b*vtilt+2*second+12*fourth*T2
        H += eps2*(6*k3*vtilt+20*k5*eps2*vtilt**3+2*C[2])
        K = 2+AL+24*fourth*vtilt+6*k3+60*k5*T2+6*C[3]*eps2.sqrt()
        M = 6+AM+120*k5*vtilt+24*C[4]
        h = 4*u/(1+2*u)
        deficit = h-(H+3)/a
        if not deficit > 0:
            raise ArithmeticError('positive reference deficit unresolved')
        Lmax, Mmax = 2+K/a, 4+M/a
        q_sensitivity = Mmax/deficit**2+2*Lmax**2/deficit**3
        l_sensitivity = 2*Lmax/deficit**2
        reference = q_sensitivity*(H+3)+l_sensitivity*K+M/deficit+6+4/h
        margin_factor = (2+1/u)**4/4
        reference_budget = margin_factor*reference*u*u/a
        # This bound is valid for every anchor >=10^6. Its endpoint here is
        # the exact rational threshold, not a rounded Lambert coordinate.
        base = derivative_bound(10**6)
        tau = interval(base['saddle_bound']['constants']['gaussian_tail_exponent'])
        u0 = (arb(2)*10**6/arb.pi()).lambertw()/2
        e2, e3, e4 = [arb(row['absolute_upper'])*(u/u0)**16
                      *(arb(10**6)/a)**(arb(7)+arb(row['order'])/2)
                      for row in base['derivatives'][2:]]
        true_budget = margin_factor*u*u*(4500*a*e2+108*a*a*e3+3*a**3*e4)
        conditions.update({
            'denominator_perturbation': arb(9)/(8*a) < arb(1)/1000,
            'log_q_clearance': H/a < arb('0.1'),
            'reference_deficit': deficit > arb('0.5'),
            'first_log_q_derivative': K/a < 1,
            'second_log_q_derivative': M/a < 1,
            'true_remainder_power_decay': tau >= arb(7)/16 and tau <= arb('0.5'),
            'true_deficit_clearance': a*e2 < arb(1)/12,
            'true_first_derivative': a*a*e3 < 1,
            'true_second_derivative': a**3*e4 < 1,
            'strict_negative_margin': reference_budget+true_budget < 1,
        })
        constants = {'H_error_constant': H, 'L_error_constant': K, 'M_error_constant': M,
                     'reference_relative_budget': reference_budget,
                     'true_additional_relative_budget': true_budget,
                     'combined_relative_budget': reference_budget+true_budget}
        return {'schema_version': 1, 'anchor_threshold': str(Fraction(threshold)),
                'status': 'uniform_shifted_curvature_pass' if all(conditions.values()) else 'unresolved',
                'conditions': conditions, 'exact_cubic_identity': cubic_identity(),
                'upper_bounds': {key: str(value.upper().fmpq()) for key, value in constants.items()},
                'scaled_deficit_lower': str(deficit.lower().fmpq()),
                'log_jet_coefficient_bounds': [str(value.upper().fmpq()) for value in C],
                'derivative_bound': '|E_a^(j)(y)|<=j!*C_j*(u/a)^2/(a*u)^(j/2), j=0,...,4, |y-a|<=1; linear phase absorbed exactly',
                'scope': 'Every real anchor a>=anchor_threshold, for the unchanged frozen degree-16 reference and the true theta integral, subject to the written analytic proof.',
                'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ('shifted_gaussian_curvature.py', 'cubic_gaussian_tail.py',
                                               'gaussian_jet_bound.py', 'gaussian_tail_bound.py',
                                               'common_remainder.py', 'high_order_saddle.py',
                                               'decaying_theta.py', 'laboratory.py', 'coefficients.py')},
                'remaining': 'Parameters below 10^6 and the uniform interior all-rank budget; RH is not proved.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--threshold', default='1000000')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = uniform_shifted_curvature(args.threshold)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])
    print('combined relative budget:', arb(result['upper_bounds']['combined_relative_budget']))


if __name__ == '__main__':
    main()
