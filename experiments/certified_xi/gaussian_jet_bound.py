"""Uniform real-derivative bounds for the common Gaussian log remainder.

The finite Taylor-jet norm preserves the common integral before taking
absolute values. Analytic justification: RH_GAUSSIAN_JET_TAIL_2026_09_20.md.
Passing constants certify a tail only, never the lower bridge or all ranks.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

from flint import arb, ctx
from common_remainder import derivative_bound
from gaussian_tail_bound import gaussian_absolute_moments
from high_order_saddle import stirling_row
from laboratory import interval


def gaussian_polynomials(t, order):
    """Positive-coefficient tilted moments / absolute Hermite majorants."""
    values = [arb(1), t]
    for k in range(1, order):
        values.append(t*values[k]+k*values[k-1])
    return values[:order+1]


def jet_constants(threshold_u):
    """Constants uniform for u>=U and real tilt |t|<=1/sqrt(a*u)."""
    U = Fraction(threshold_u)
    if U < 6:
        raise ValueError('Lambert coordinate threshold at least 6 required')
    u = arb(str(U))
    a = arb.pi()*u*(2*u).exp()
    eps = (u/a).sqrt()
    window = (32*u).sqrt()
    h = (8/a).sqrt()
    tilt = 1/(a*u).sqrt()
    eta = tilt*window
    lam = arb('2.25')+1/(2*u)
    cubic = (4+6/u+1/u**2)/24
    quartic = (8+24/u+14/u**2+1/u**3)/192
    phase = {}
    for j in range(5, 17):
        phase[j] = sum((arb(s)*arb(2)**(k-j)*u**(k-j)
                        for k, s in enumerate(stirling_row(j))), arb(0))/math.factorial(j)
    B1 = eps*(lam*window+cubic*window**3)
    B2 = quartic*eps**2*window**4
    R = sum((d*eps**(j-2)*window**j for j, d in phase.items()), arb(0))
    amplitude = 3*h.exp()*(eps*h.exp()*window).exp()
    moments = gaussian_absolute_moments(20)
    polynomial = {1: lam, 3: cubic, 4: quartic*eps}
    raw = []
    for k in range(5):
        phase_integral = sum((d*eps**(j-5)*moments[j+k]
                              for j, d in phase.items()), arb(0))
        cube = sum((ci*cj*cl*moments[i+j+l+k]
                    for i, ci in polynomial.items()
                    for j, cj in polynomial.items()
                    for l, cl in polynomial.items()), arb(0))
        central = (B1+B2+R).exp()*(amplitude*moments[k+1]+phase_integral)
        central += (B1+B2).exp()*cube/6
        central += quartic*(lam*moments[k+5]+cubic*moments[k+7])
        central += quartic**2*eps*moments[k+8]/2
        # All coefficients of W are <=1 (checked below). Both infinite
        # Gaussian tails are included, with the real exponential tilt.
        tail_sum = sum((arb(math.factorial(n)//math.factorial(n-j))*2**(j+1)
                        *window**(n-2*j-1)
                        for n in range(k, k+7) for j in range(n+1)), arb(0))
        tail = 2*arb.pi()**arb('1.5')*(-13*u).exp()*tail_sum
        raw.append(eta.exp()*(central+tail))
    hermite = gaussian_polynomials(tilt, 4)
    normalized = sum((hermite[i]*raw[k-i]/(math.factorial(i)*math.factorial(k-i))
                      for k in range(5) for i in range(k+1)), arb(0))
    moments_t = gaussian_polynomials(1+tilt, 6)
    p = lam*moments_t[1]+cubic*moments_t[3]
    s = (quartic*moments_t[4]+lam**2*moments_t[2]/2
         +lam*cubic*moments_t[4]+cubic**2*moments_t[6]/2)
    w = p*eps+s*eps**2+normalized*eps**3
    if not w < 1:
        raise ArithmeticError('Taylor-jet logarithm unresolved')
    log_error = normalized+p*(s+normalized*eps)
    log_error += eps*(s+normalized*eps)**2/2
    log_error += (p+s*eps+normalized*eps**2)**3/(3*(1-w))
    # A sufficient bound on each nonconstant coefficient of W.
    w_coefficients = (lam*eps+cubic*eps+quartic*eps**2
                      +lam**2*eps**2/2+lam*cubic*eps**2+cubic**2*eps**2/2)
    conditions = {'positive_amplitude': arb('1.5')*eps**2 < arb('0.5'),
                  'tail_tangent': tilt < window/2,
                  'gaussian_polynomial_coefficients': w_coefficients < 1,
                  'logarithm_jet': w < 1}
    return u, a, log_error, raw, conditions


def uniform_jet_tail(threshold_u=14):
    with ctx.workprec(512):
        u, a, C, raw, conditions = jet_constants(threshold_u)
        # No u^6 loss for the elementary A -> 2a(1+2u) replacements.
        H = 10104+2*C*(u/a).sqrt()
        L = 4574+6*C
        M = 10100/a.sqrt()+24*C/u.sqrt()
        Kq = 3*H+10
        reference = (532*Kq+40*L+100)/a.sqrt()+2*M
        # N(a)>=4/[(2+1/U)^4*a^2*u^2] for every u>=U.
        margin_factor = (2+1/u)**4/4
        reference_budget = margin_factor*reference*u**2/a.sqrt()
        base = derivative_bound(10**6)
        tau = interval(base['saddle_bound']['constants']['gaussian_tail_exponent'])
        u0 = (arb(2)*10**6/arb.pi()).lambertw()/2
        errors = [arb(row['absolute_upper'])*(u/u0)**16
                  *(arb(10**6)/a)**(arb(7)+arb(row['order'])/2)
                  for row in base['derivatives'][2:]]
        e2, e3, e4 = errors
        true_budget = margin_factor*u**2*(4500*a*e2+108*a**2*e3+3*a**3*e4)
        conditions.update({
            'true_remainder_power_decay': tau >= arb(7)/16 and tau <= arb('0.5'),
            'negative_log_q': H/a < arb(1)/3,
            'first_log_q_derivative': L/a < 1,
            'second_log_q_derivative': M/a.sqrt() < 1,
            'true_deficit_clearance': a*e2 < arb(1)/12,
            'true_first_derivative': a**2*e3 < 1,
            'true_second_derivative': a**3*e4 < 1,
            'half_negative_margin': reference_budget+true_budget < arb('0.5'),
        })
        constants = {'anchor_threshold': a, 'log_jet_error_constant': C,
                     'H_error_constant': H, 'L_error_constant': L,
                     'M_error_constant': M,
                     'reference_relative_budget': reference_budget,
                     'true_additional_relative_budget': true_budget,
                     'combined_relative_budget': reference_budget+true_budget}
        return {
            'schema_version': 1, 'u_threshold': str(Fraction(threshold_u)),
            'status': 'uniform_jet_tail_majorants_pass' if all(conditions.values()) else 'unresolved',
            'conditions': conditions,
            'upper_bounds': {key: str(value.upper().fmpq()) for key, value in constants.items()},
            'raw_derivative_error_constants': [str(v.upper().fmpq()) for v in raw],
            'derivative_bound': '|E_a^(j)(y)|<=j!*C*(u/a)^(3/2)/(a*u)^(j/2), j=0,...,4, |y-a|<=1',
            'scope': 'Every real anchor with W(2a/pi)/2>=u_threshold, subject to the accompanying written analytic proof.',
            'remaining': 'Lower-anchor bridge and uniform interior all-rank budget; RH is not proved.',
            'source_hashes': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                              for name in ('gaussian_jet_bound.py', 'gaussian_tail_bound.py',
                                           'common_remainder.py', 'high_order_saddle.py',
                                           'decaying_theta.py', 'laboratory.py', 'coefficients.py')},
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--threshold-u', default='14')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = uniform_jet_tail(args.threshold_u)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])
    print('combined relative budget:', arb(result['upper_bounds']['combined_relative_budget']))


if __name__ == '__main__':
    main()
