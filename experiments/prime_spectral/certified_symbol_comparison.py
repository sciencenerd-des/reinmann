"""Certify an oscillatory Weil-symbol tail, and measure its actual dimension cost.

Sampling proposes cutoffs only. Every accepted frequency panel is enclosed in
Arb; an increasing analytic envelope covers the infinite remainder. A dip is
checked using the actual digamma symbol, not a sampled lower envelope.
"""
import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import time

import numpy as np
from flint import arb, ctx
from certified_weil import endpoints
from compact_window_certificate import symbol
from full_ground_fourier import sha256
from weil_matrix import prime_powers

OUT = Path('research/prime_spectral/verification_2026_10_13_calibration')


def envelope(t, powers):
    return ((t/(2*arb.pi())).log()-1/t
            -sum((2*arb(p).log()/arb(q).sqrt()*(t*arb(q).log()).cos()
                  for q, p in powers), arb(0)))


def analytic_global(t, powers):
    return ((t/(2*arb.pi())).log()-1/t
            -sum((2*arb(p).log()/arb(q).sqrt() for q, p in powers), arb(0)))


def refined_bounds(a, cutoff, beta, count, order, powers):
    """The existing polynomial-tail bounds with a separately certified beta."""
    mass = sum((2*arb(p).log()/arb(q).sqrt() for q, p in powers), arb(0))
    zmax = arb(1)+(cutoff+2)/arb(2)
    h = 17+2*zmax+arb.pi().log()+mass*(arb(3)/8*(2*a)).cosh()+abs(beta)
    quadrature = 4*cutoff*(2*a*(3*a/4).exp()*h)*arb(2)**(1-2*order)/arb.pi()
    r = (2*a).sqrt()*(a*cutoff)**count/math.factorial(count)
    p = (2*a).sqrt()*(a/2).exp()
    rp = p*(a/2)**count/math.factorial(count)
    coupling = cutoff*h/arb.pi()*(2*a).sqrt()*r+4*p*rp
    tail = cutoff*h/arb.pi()*r*r+4*rp*rp
    return quadrature, coupling, tail, h


def cost(a, cutoff, beta, powers):
    target = arb('1e-10')
    def passes(n):
        _, coupling, tail, _ = refined_bounds(a, cutoff, beta, n, 160, powers)
        return coupling+tail < target
    hi = 2
    while hi < 131072 and not passes(hi):
        hi *= 2
    if not passes(hi):
        raise ArithmeticError('dimension search cap exhausted')
    lo = hi//2
    while hi-lo > 2:
        mid = ((hi+lo)//4)*2
        if passes(mid):
            hi = mid
        else:
            lo = mid
    quadrature, coupling, tail, h = refined_bounds(a, cutoff, beta, hi, 160, powers)
    if not passes(hi) or hi > 2 and passes(hi-2):
        raise ArithmeticError('dimension search did not locate the even threshold')
    return {'polynomial_count': hi, 'dimension_per_parity': hi//2,
            'coupling': endpoints(coupling), 'tail': endpoints(tail),
            'quadrature_order160_error': endpoints(quadrature),
            'complex_ellipse_bound': endpoints(h), 'coupling_plus_tail_target': '1e-10',
            'scope': 'Analytic norm-bound cost only, not assembly, block positivity or a full-window certificate.'}


def certify_panels(powers, start, stop, beta):
    panels, evaluations = [], 0
    def visit(lo, hi, depth=0):
        nonlocal evaluations
        x = arb(str((lo+hi)/2), str((hi-lo)/2))
        value = envelope(x, powers)
        evaluations += 1
        if value >= beta:
            panels.append({'lo': str(lo), 'hi': str(hi), 'lower_enclosure': endpoints(value)})
            return
        if depth >= 28:
            raise ArithmeticError(f'uncertified panel [{lo},{hi}], possibly an actual dip')
        mid = (lo+hi)/2
        visit(lo, mid, depth+1)
        visit(mid, hi, depth+1)
    lo = Fraction(start)
    while lo < stop:
        hi = min(lo+8, Fraction(stop))
        visit(lo, hi)
        lo = hi
    return panels, evaluations


def pilot(powers, stop, beta):
    # Not a certificate; every proposed final interval is checked below.
    t = np.arange(4, stop+.005, .005)
    values = np.log(t/(2*np.pi))-1/t
    for q, p in powers:
        values -= 2*math.log(p)/math.sqrt(q)*np.cos(t*math.log(q))
    bad = np.flatnonzero(values < float(beta))
    start = math.ceil(float(t[bad[-1]]))+1 if len(bad) else 4
    later = t >= 1024
    index = np.flatnonzero(later)[np.argmin(values[later])]
    last = float(t[bad[-1]]) if len(bad) else None
    return start, str(round(float(t[index]), 3)), str(round(last, 3)) if last else None


def run():
    OUT.mkdir(parents=True, exist_ok=True)
    results = []
    with ctx.workprec(192):
        for C in ['exp(2)', '19/2']:
            c = arb(2).exp() if C == 'exp(2)' else arb(C)
            a = c.log()/2
            pp = [(q, p) for q, p in prime_powers(int(c.ceil().fmpq())) if arb(q) < c]
            mass = sum((2*arb(p).log()/arb(q).sqrt() for q, p in pp), arb(0))
            for beta_text in ['31/100', '1/2']:
                begun = time.monotonic()
                beta = arb(beta_text)
                stop = int((2*arb.pi()*(mass+beta).exp()+2).upper().ceil().fmpq())
                if not analytic_global(arb(stop), pp) >= beta:
                    raise ArithmeticError('global envelope takeover failed')
                start, dip, last = pilot(pp, stop, beta)
                # Actual-symbol counterexamples certify why small cutoffs fail.
                dip_value = symbol(arb(dip), pp)
                if not dip_value < 0:
                    raise ArithmeticError('selected negative actual-symbol dip did not certify')
                late = symbol(arb(last), pp) if last else None
                panels, evaluations = certify_panels(pp, start, stop, beta)
                record = {'C': C, 'active_prime_powers': pp, 'beta': beta_text,
                          'certified_tail_start': start, 'analytic_takeover': stop,
                          'analytic_takeover_lower': endpoints(analytic_global(arb(stop), pp)),
                          'prime_comb_mass': endpoints(mass),
                          'comb_derivative_bound': endpoints(sum((2*arb(p).log()*arb(q).log()/arb(q).sqrt() for q, p in pp), arb(0))),
                          'negative_actual_symbol_point': dip,
                          'negative_actual_symbol': endpoints(dip_value),
                          'late_dip_point': last, 'late_actual_symbol': endpoints(late) if late is not None else None,
                          'late_dip_below_beta_certified': bool(late < beta) if late is not None else False,
                          'panels': panels, 'evaluations': evaluations,
                          'comparison_cost': cost(a, start, beta, pp),
                          'seconds': time.monotonic()-begun}
                results.append(record)
                print(C, beta_text, 'tail start', start, 'panels', len(panels),
                      'dimension', record['comparison_cost']['polynomial_count'], flush=True)
                (OUT/'symbol_comparison.json').write_text(json.dumps({'status': 'partial_results', 'windows': results}, indent=2)+'\n')
    result = {'status': 'certified_oscillatory_symbol_tails_and_actual_dips', 'windows': results,
              'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                  ['certified_symbol_comparison.py', 'compact_window_certificate.py', 'weil_matrix.py']},
              'analytic_dependencies': 'The Binet lower bound Re psi(1/4+it/2)-log pi >= log(t/(2pi))-1/t for t>=4; polynomial approximation and Bernstein ellipse bounds from the existing compact-window comparison.',
              'scope': 'Uniform symbol-tail lower bounds, explicit counterexamples to smaller-cutoff floors, and analytic dimension costs. No full-window positivity, projector, or Liu verification.'}
    (OUT/'symbol_comparison.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    run()
