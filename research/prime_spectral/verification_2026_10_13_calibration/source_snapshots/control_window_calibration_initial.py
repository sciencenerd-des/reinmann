"""Closed geometric forms and rational negative trials for calibration controls.

Positive sections are evidence only. Searching across dilated finite spaces
does not bracket the minimum negative support of the full form.
"""
import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import time

from flint import acb, arb, ctx
from certified_weil import correlation_ball, endpoints
from character_zero_atlas import CharacterControl, OUT
from davenport_heilbronn_control import log_derivative_coefficients
from dh_weil_certificate import geometric_entry, negative_ldl_witness
from full_ground_fourier import sha256


def arch_tail(length, alpha, terms):
    first = 2*arb(terms)+2*alpha
    return 2*(-first*length).exp()/(length*first**2*(1-(-2*length).exp()))


def arch_cell(m, n, length, alpha, terms):
    """No-pole gamma contribution with gamma argument alpha+i*t/2."""
    omega, eta = 2*arb.pi()*m/length, 2*arb.pi()*n/length
    if m == n:
        argument = acb(alpha, -omega/2)
        value = (-arb.pi().log()+argument.digamma().real
                 +argument.polygamma(1).real/(2*length))
        for k in range(terms):
            decay = 2*arb(k)+2*alpha
            value -= 2/length*(-decay*length).exp()*(decay**2-omega**2)/(decay**2+omega**2)**2
    else:
        difference = arb.pi()*(m-n)
        value = -(acb(alpha, -omega/2).digamma().imag
                  -acb(alpha, -eta/2).digamma().imag)/(2*difference)
        for k in range(terms):
            decay = 2*arb(k)+2*alpha
            value -= (-decay*length).exp()/difference*(omega/(decay**2+omega**2)-eta/(decay**2+eta**2))
    return value+arb(0, arch_tail(length, alpha, terms).upper())


def pole_cell(m, n, length):
    omega, eta = 2*arb.pi()*m/length, 2*arb.pi()*n/length
    if m == n:
        return 4/length*((length/2).cosh()-1)*(arb(1)/4-omega**2)/(arb(1)/4+omega**2)**2
    return (2*(length/2).cosh()-2)/(arb.pi()*(m-n))*(omega/(arb(1)/4+omega**2)-eta/(arb(1)/4+eta**2))


def representation_coefficients(d, count):
    result = [arb(0)]*(count+1)
    for n in range(1, count+1):
        representations = 0
        for y in range(-math.isqrt(n//d), math.isqrt(n//d)+1):
            square = n-d*y*y
            x = math.isqrt(square)
            if x*x == square:
                representations += 1 if x == 0 else 2
        result[n] = arb(representations)/2
    return result


def matrices(kind, parameter, label, C, modes, terms):
    c = Fraction(C)
    top = -(-c.numerator//c.denominator)
    length = arb(str(c)).log()
    if kind == 'character':
        control = CharacterControl(parameter, label)
        period = control.parameters()[2]
        a = [arb(0)]+[period[n % parameter] for n in range(1, top+1)]
    elif kind == 'epstein':
        a = representation_coefficients(parameter, top)
    else:
        raise ValueError('unknown control kind')
    coef = log_derivative_coefficients(a)
    def cell(m, n):
        odd = arch_cell(m, n, length, arb(3)/4, terms)
        if kind == 'character':
            value = odd+arb(parameter).log()*(m == n)
        else:
            value = (odd+arch_cell(m, n, length, arb(1)/4, terms)
                     +pole_cell(m, n, length)+arb(4*parameter).log()*(m == n))
        for j in range(2, top):
            value -= coef[j]/arb(j).sqrt()*correlation_ball(m, n, acb(arb(j).log()), length).real
        return value
    b = [arb(0)]+[n*cell(n, 0) for n in range(1, modes+1)]
    E = [[arb(0) for _ in range(modes+1)] for _ in range(modes+1)]
    O = [[arb(0) for _ in range(modes)] for _ in range(modes)]
    E[0][0] = cell(0, 0)
    for n in range(1, modes+1):
        E[0][n] = E[n][0] = arb(2).sqrt()*b[n]/n
        d, e = cell(n, n), cell(n, -n)
        E[n][n], O[n-1][n-1] = d+e, d-e
        for m in range(1, n):
            E[m][n] = E[n][m] = 2*(n*b[n]-m*b[m])/(n*n-m*m)
            O[m-1][n-1] = O[n-1][m-1] = 2*(m*b[n]-n*b[m])/(n*n-m*m)
    return E, O, cell


def trial(kind, parameter, label, C, modes=80, bits=1024, checks=False):
    start = time.monotonic()
    with ctx.workprec(bits):
        length = arb(str(Fraction(C))).log()
        terms = max(32, math.ceil((bits*math.log(2)+20)/(2*float(length.lower()))))
        E, O, cell = matrices(kind, parameter, label, C, modes, terms)
        comparisons = []
        if checks and kind == 'character':
            top = -(-Fraction(C).numerator//Fraction(C).denominator)
            period = CharacterControl(parameter, label).parameters()[2]
            coef = log_derivative_coefficients([arb(0)]+[period[n % parameter] for n in range(1, top+1)])
            for m, n in [(0, 0), (7, 0), (7, 7), (7, -7)]:
                direct = geometric_entry(m, n, length, coef, top)+(arb(parameter)/5).log()*(m == n)
                closed = cell(m, n)
                if not direct.overlaps(closed):
                    raise ArithmeticError('closed odd-gamma entry disagrees with independent integral')
                comparisons.append({'indices': [m, n], 'direct': endpoints(direct), 'closed': endpoints(closed)})
        sectors = []
        for parity, A in [('even', E), ('odd', O)]:
            try:
                result = negative_ldl_witness(A)
            except ArithmeticError as e:
                result = {'unresolved': str(e)}
            result.update(parity=parity, dimension=len(A),
                          matrix=[[endpoints(x) for x in row] for row in A])
            sectors.append(result)
        status = ('negative_full_form_trial' if any('normalized_full_form' in s for s in sectors)
                  else 'positive_finite_sections_only' if all(s.get('positive_finite_section') for s in sectors)
                  else 'unresolved')
        result = {'status': status, 'kind': kind, 'parameter': parameter, 'Conrey_label': label,
                  'C': str(C), 'modes': modes, 'bits': bits, 'archimedean_tail_terms': terms,
                  'sectors': sectors, 'entry_checks': comparisons,
                  'seconds': time.monotonic()-start,
                  'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                      ['control_window_calibration.py', 'character_zero_atlas.py',
                       'davenport_heilbronn_control.py', 'dh_weil_certificate.py']},
                  'scope': 'A rational negative trial certifies the full form is not positive. Positive finite sections give no lower bound on the first negative full support.'}
    folder = OUT/f'{kind}{parameter}_label{label}_windows'
    folder.mkdir(parents=True, exist_ok=True)
    path = folder/f'C{str(C).replace("/", "_")}_N{modes}_{bits}bits.json'
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(kind, parameter, label, 'C', C, 'N', modes, status, 'seconds', result['seconds'], flush=True)
    return result, path


def search(kind, parameter, label, low, high, steps=9, modes=80, bits=1024):
    low, high = Fraction(low), Fraction(high)
    records = []
    for c in [low, high]:
        d, p = trial(kind, parameter, label, str(c), modes, bits, checks=(c == high))
        records.append({'C': str(c), 'status': d['status'], 'file': str(p), 'sha256': sha256(p)})
    if records[0]['status'] != 'positive_finite_sections_only' or records[1]['status'] != 'negative_full_form_trial':
        result = {'status': 'proposed_endpoints_do_not_straddle_this_finite_family', 'records': records}
    else:
        for _ in range(steps):
            mid = (low+high)/2
            d, p = trial(kind, parameter, label, str(mid), modes, bits)
            records.append({'C': str(mid), 'status': d['status'], 'file': str(p), 'sha256': sha256(p)})
            if d['status'] == 'negative_full_form_trial':
                high = mid
            elif d['status'] == 'positive_finite_sections_only':
                low = mid
            else:
                break
        result = {'status': 'finite_family_search_with_certified_negative_endpoint',
                  'positive_finite_evidence_C': str(low), 'negative_certificate_C': str(high),
                  'records': records}
    result.update(kind=kind, parameter=parameter, Conrey_label=label, modes=modes, bits=bits,
                  scope='Finite-family search only; no monotonicity or minimum-full-support bracket.')
    folder = OUT/f'{kind}{parameter}_label{label}_windows'
    (folder/f'search_N{modes}_{bits}bits.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--kind', choices=['character', 'epstein'], default='character')
    p.add_argument('--parameter', type=int, required=True)
    p.add_argument('--label', type=int, default=0)
    p.add_argument('--C', nargs='+')
    p.add_argument('--search', nargs=2)
    p.add_argument('--modes', type=int, default=80)
    p.add_argument('--bits', type=int, default=1024)
    p.add_argument('--steps', type=int, default=9)
    args = p.parse_args()
    if not 1 <= args.modes <= 256 or not 512 <= args.bits <= 4096:
        p.error('bounded mode count and precision required')
    if args.search:
        search(args.kind, args.parameter, args.label, *args.search, args.steps, args.modes, args.bits)
    elif args.C:
        for c in args.C:
            trial(args.kind, args.parameter, args.label, c, args.modes, args.bits, checks=True)
    else:
        p.error('supply --C values or --search endpoints')
