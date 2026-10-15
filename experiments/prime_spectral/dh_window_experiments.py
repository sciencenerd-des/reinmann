"""Exact-rational support search and arithmetic ablations of the DH form."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time

from flint import arb, ctx
from certified_weil import endpoints
from davenport_heilbronn_control import dirichlet_coefficients, log_derivative_coefficients
from dh_weil_certificate import geometric_entry, negative_ldl_witness
from full_ground_fourier import sha256
from weil_matrix import prime_powers

OUT = Path('research/prime_spectral/verification_2026_10_12_sector')


def assemble(C, modes, modification='original'):
    c = Fraction(C)
    if not 2 <= c <= 100 or not 1 <= modes <= 128:
        raise ValueError('bounded rational window and mode count required')
    top = -(-c.numerator//c.denominator)
    L = arb(str(c)).log()
    coef = log_derivative_coefficients(dirichlet_coefficients(top))
    pp = {q for q, _ in prime_powers(top)}
    if modification == 'absolute':
        # Interval abs encloses |c_n| even for an exact zero whose computed
        # enclosure has small radius; no coefficient sign oracle is needed.
        coef = [abs(x) for x in coef]
    elif modification == 'prime-powers':
        coef = [x if j in pp else arb(0) for j, x in enumerate(coef)]
    elif modification != 'original':
        raise ValueError('unknown arithmetic modification')
    diagonal = [geometric_entry(0, 0, L, coef, top)]
    b, opposite = [arb(0)], []
    for n in range(1, modes+1):
        b.append(n*geometric_entry(n, 0, L, coef, top))
        diagonal.append(geometric_entry(n, n, L, coef, top))
        opposite.append(geometric_entry(n, -n, L, coef, top))
    even = [[arb(0) for _ in range(modes+1)] for _ in range(modes+1)]
    odd = [[arb(0) for _ in range(modes)] for _ in range(modes)]
    even[0][0] = diagonal[0]
    for n in range(1, modes+1):
        even[0][n] = even[n][0] = arb(2).sqrt()*b[n]/n
        even[n][n] = diagonal[n]+opposite[n-1]
        odd[n-1][n-1] = diagonal[n]-opposite[n-1]
        for m in range(1, n):
            even[m][n] = even[n][m] = 2*(n*b[n]-m*b[m])/(n*n-m*m)
            odd[m-1][n-1] = odd[n-1][m-1] = 2*(m*b[n]-n*b[m])/(n*n-m*m)
    return even, odd


def certify(C, modes, modification='original'):
    start = time.monotonic()
    with ctx.workprec(768):
        E, O = assemble(C, modes, modification)
        sectors = []
        for parity, A in [('even', E), ('odd', O)]:
            try:
                s = negative_ldl_witness(A)
            except ArithmeticError as e:
                s = {'unresolved': str(e)}
            s.update(parity=parity, matrix=[[endpoints(x) for x in row] for row in A])
            sectors.append(s)
        negative = any('normalized_full_form' in s for s in sectors)
        positive = all(s.get('positive_finite_section', False) for s in sectors)
        result = {'status': 'negative_full_form_trial' if negative else
                  'positive_finite_sections_only' if positive else 'unresolved',
                  'C': str(Fraction(C)), 'modes': modes, 'modification': modification,
                  'bits': 768, 'seconds': time.monotonic()-start, 'sectors': sectors,
                  'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                      ['dh_window_experiments.py', 'dh_weil_certificate.py',
                       'certified_weil.py', 'davenport_heilbronn_control.py']},
                  'scope': 'Negative trials disprove positivity of this full form. Positive finite sections are evidence only. Modified forms are arithmetic ablations, not asserted L-functions.'}
    name = f'dh_{modification}_C{str(Fraction(C)).replace("/", "_")}_N{modes}.json'
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT/name).write_text(json.dumps(result, indent=2)+'\n')
    print(C, modification, result['status'], 'seconds', result['seconds'], flush=True)
    for s in sectors:
        if 'normalized_full_form' in s:
            print('negative', s['parity'], s['normalized_full_form'], flush=True)
    return result, OUT/name


def bisect(modes=80, steps=8):
    low, high = Fraction(13), Fraction(31)
    records = []
    for C in [low, high]:
        d, p = certify(C, modes)
        records.append({'C': str(C), 'status': d['status'], 'file': str(p), 'sha256': sha256(p)})
    if records[0]['status'] != 'positive_finite_sections_only' or records[1]['status'] != 'negative_full_form_trial':
        raise ArithmeticError('finite-family starting bracket failed')
    for _ in range(steps):
        mid = (low+high)/2
        d, p = certify(mid, modes)
        records.append({'C': str(mid), 'status': d['status'], 'file': str(p), 'sha256': sha256(p)})
        if d['status'] == 'negative_full_form_trial':
            high = mid
        elif d['status'] == 'positive_finite_sections_only':
            low = mid
        else:
            break
        (OUT/f'dh_window_search_N{modes}.json').write_text(json.dumps({
            'status': 'finite_family_search_not_full_threshold_bracket',
            'positive_finite_evidence_C': str(low), 'negative_certificate_C': str(high),
            'modes': modes, 'records': records,
            'scope': 'The lower endpoint is not a lower bound for the first full negative support. The finite rescaled trial spaces are not nested across C, so no monotonicity of their inertia is asserted.'}, indent=2)+'\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('action', choices=['bisect', 'ablations'])
    p.add_argument('--modes', type=int, default=80)
    p.add_argument('--steps', type=int, default=8)
    a = p.parse_args()
    if a.action == 'bisect':
        bisect(a.modes, a.steps)
    else:
        for modification in ['original', 'absolute', 'prime-powers']:
            certify('31', a.modes, modification)
