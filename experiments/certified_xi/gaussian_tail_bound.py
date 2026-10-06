"""Computable uniform majorants for the frozen Gaussian curvature expansion.

Each endpoint quantity bounds a decreasing function on the full u>=U tail.
See RH_EFFECTIVE_GAUSSIAN_TAIL_2026_09_19.md for the analytic justification.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from flint import arb, ctx
from high_order_saddle import stirling_row


def gaussian_absolute_moments(order):
    if type(order) is not int or order < 1:
        raise ValueError('positive integer moment order required')
    moments = [arb(1), (2/arb.pi()).sqrt()]
    for j in range(2, order+1):
        moments.append((j-1)*moments[j-2])
    return moments


def integrated_central_bound(u, a, B1, B2, R, eta):
    """Integrate absolute polynomial errors against the Gaussian density."""
    moments = gaussian_absolute_moments(16)
    phase = arb(0)
    for j in range(5, 17):
        coefficient = arb(5+sum(stirling_row(j))*2**j)
        coefficient /= math.factorial(j)*arb(2)**(arb(j)/2)
        phase += coefficient*moments[j]*u**(arb(j)/2-7)*a**(arb(5-j)/2)
    # Cubing a positive-coefficient polynomial keeps every absolute term.
    polynomial = {1: arb(4), 3: arb(3), 4: 3*(u/a).sqrt()}
    cube = arb(0)
    for i, ci in polynomial.items():
        for j, cj in polynomial.items():
            for k, ck in polynomial.items():
                cube += ci*cj*ck*moments[i+j+k]
    amplitude = 12*(16*u/a.sqrt()).exp()*moments[1]/u**arb('4.5')
    central = (B1+B2+R).exp()*(amplitude+phase)
    central += (B1+B2).exp()*cube/(6*u**arb('4.5'))
    central += 3*(4*moments[5]+3*moments[7])/u**arb('4.5')
    central += 9*moments[8]/(2*u**4*a.sqrt())
    return eta.exp()*central


def uniform_tail(threshold_u=80, *, integrated_errors=False, disk_divisor=32):
    U, divisor = Fraction(threshold_u), Fraction(disk_divisor)
    if divisor < 1:
        raise ValueError('complex disk divisor at least one required')
    if U < 20:
        raise ValueError('Lambert coordinate threshold at least 20 required')
    with ctx.workprec(512):
        u = arb(str(U))
        a = arb.pi()*u*(2*u).exp()
        root = a.sqrt()
        d = arb(str(divisor))
        if not root > 2*d:
            raise ValueError('complex disk must contain the neighboring-parameter disks')
        cauchy = 2*d
        ratio = u/root
        phase = sum((arb(5 + sum(stirling_row(j))*2**j)*4**j/math.factorial(j)
                     * ratio**(j-5) for j in range(5, 17)), arb(0))
        B1, B2 = 600*u**2/root, 3072*u**3/a
        R = phase*u**4/a**arb('1.5')
        eta = 8/d
        central = eta.exp()*((B1+B2+R).exp()*(1000/u**4+phase/u**2)
                   +(B1+B2).exp()*(600+3072*ratio)**3/6
                   +600*3072/u+arb(3072)**2/(2*root))
        if integrated_errors:
            central = integrated_central_bound(u, a, B1, B2, R, eta)
        tails = 2*eta.exp()*10**6*arb(32)**arb('2.5')*arb.pi()**arb('1.5')
        tails *= (-13*u).exp()/u**2
        error = arb('0.5').exp()*(central+tails)
        p, s, e = 16*(u/a).sqrt(), 508*u/a, error*u**6/a**arb('1.5')
        w = p+s+e
        if not w < arb('0.5'):
            raise ArithmeticError('Gaussian logarithm zero exclusion unresolved')
        log_error = error*(1+p+s+e/2)+8128/u**arb('4.5')
        log_error += arb(508)**2/(2*u**4*root)
        cubic = (16+508*(u/a).sqrt()+error*u**arb('5.5')/a)**3
        log_error += cubic/(3*(1-w)*u**arb('4.5'))
        KH = 100+10**8+10000+2*cauchy**2*log_error/root
        KL = 100+10**8+4224+6*cauchy**3*log_error
        KM = (100+10**8)/root+24*cauchy**4*log_error
        Kq = 3*KH+10
        curvature = (532*Kq+40*KL+100/u**6)/root+2*KM
        true_extra = arb(10)**60*u**10/a**arb('5.5')
        budget = 81*(curvature+true_extra)*u**8/root
        conditions = {
            'amplitude_exponent': 16*u/root < 1,
            'amplitude_denominator': 2*u/a < arb('0.5'),
            'window_exponential': 4/root < arb('0.5'),
            'gaussian_tail_coefficients': 16*(u/a).sqrt()+15*u/a < 1,
            'logarithm_disk': w < arb('0.5'),
            'negative_log_q': KH*u**6/a < arb(1)/3,
            'first_log_q_derivative': KL*u**6/a < 1,
            'second_log_q_derivative': KM*u**6/root < 1,
            'true_deficit_clearance': arb(10)**48*u**16/a**7 < arb(1)/12,
            'true_first_derivative': arb(10)**51*u**16/a**arb('6.5') < 1,
            'true_second_derivative': arb(10)**54*u**16/a**6 < 1,
            'half_negative_margin': budget < arb('0.5'),
        }
        constants = {'anchor_threshold': a, 'phase_constant': phase,
                     'central_error_constant': central, 'gaussian_tail_constant': tails,
                     'analytic_log_error_constant': log_error,
                     'H_error_constant': KH, 'L_error_constant': KL,
                     'M_error_constant': KM, 'reference_curvature_error_constant': curvature,
                     'true_curvature_additional_constant': true_extra,
                     'relative_margin_budget': budget}
        return {'u_threshold': str(U),
                'disk_divisor': str(divisor),
                'error_method': 'gaussian_absolute_moments' if integrated_errors else 'window_supremum',
                'status': 'uniform_tail_majorants_pass' if all(conditions.values()) else 'unresolved',
                'conditions': conditions,
                'upper_bounds': {key: str(value.upper().fmpq()) for key, value in constants.items()},
                'scope': 'Every real anchor a with W(2a/pi)/2>=u_threshold; subject to the accompanying analytic proof, not a sampled sign scan.',
                'remaining': 'Lower anchors and the interior all-rank budget; RH is not proved.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--threshold-u', default='80')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--integrated-errors', action='store_true')
    parser.add_argument('--disk-divisor', default='32')
    args = parser.parse_args()
    result = uniform_tail(args.threshold_u, integrated_errors=args.integrated_errors, disk_divisor=args.disk_divisor)
    result['source_hash'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['u_threshold'], result['status'])
    print('relative margin budget:', arb(result['upper_bounds']['relative_margin_budget']))


if __name__ == '__main__':
    main()
