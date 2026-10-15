"""Two additional conductor controls, with certified zeros and negative trials.

These are normalized real, root-number-one combinations of a primitive odd
character and its conjugate. No claim of a smallest negative full support.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
from flint import acb, acb_series, arb, ctx, dirichlet_char
from certified_weil import endpoints
from davenport_heilbronn_control import log_derivative_coefficients
from dh_weil_certificate import geometric_entry, negative_ldl_witness
from full_ground_fourier import sha256

OUT = Path('research/prime_spectral/verification_2026_10_12_sector')


def datum(q):
    label = {13: 2, 17: 3}[q]
    chi = dirichlet_char(q, label)
    if chi.parity() != 1 or not chi.is_primitive():
        raise ArithmeticError('primitive odd character required')
    tau = sum((chi(n)*(acb(0, 2)*arb.pi()*n/q).exp() for n in range(1, q)), acb(0))
    epsilon = tau/acb(0, arb(q).sqrt())
    k = epsilon.imag/(1+epsilon.real)
    period = [chi(n).real+k*chi(n).imag for n in range(q)]
    period[0], period[1] = arb(0), arb(1)
    return label, epsilon, k, period


def jet(s, q, period, degree=1):
    old = ctx.cap
    try:
        ctx.cap = degree+1
        z = acb_series([s, 1])
        return sum((period[n]*z.zeta(arb(n)/q) for n in range(1, q)),
                   acb_series([0]))*(-z*arb(q).log()).exp()
    finally:
        ctx.cap = old


def root(q):
    with ctx.workprec(192):
        _, _, _, period = datum(q)
        for j in range(1, 501):
            s = acb('9/10', arb(j)/2)
            for _ in range(20):
                f = jet(s, q, period)
                if f[1].contains(0):
                    break
                w = s-f[0]/f[1]
                if not w.is_finite() or not -2 < w.real < 4 or not 0 < w.imag < 255:
                    break
                change = abs(w-s)
                s = acb(w.real.mid(), w.imag.mid())
                if change < arb('1e-25'):
                    if s.real > arb('50001/100000'):
                        with ctx.workprec(512):
                            _, _, _, high_period = datum(q)
                            for _ in range(12):
                                f = jet(s, q, high_period)
                                w = s-f[0]/f[1]
                                s = acb(w.real.mid(), w.imag.mid())
                            radius = arb('1e-20')
                            rectangle = acb(arb(s.real.mid(), radius), arb(s.imag.mid(), radius))
                            f = jet(s, q, high_period)
                            d = acb(f[1].real.mid(), f[1].imag.mid())
                            lhs = abs(f[0])+radius*abs(jet(rectangle, q, high_period)[1]-d)
                            rhs = radius*abs(d)
                            if not lhs < rhs or not s.real-radius > arb('1/2'):
                                raise ArithmeticError('analogue Rouche gate failed')
                            return {'real': endpoints(s.real), 'imag': endpoints(s.imag),
                                'radius': '1e-20', 'rouche_left': endpoints(lhs),
                                'rouche_right': endpoints(rhs),
                                'offset': endpoints(arb(s.real.mid(), radius)-arb('1/2')),
                                'height': endpoints(arb(s.imag.mid(), radius)),
                                'scope': 'One certified simple off-line zero, not a complete or steepest-zero atlas.'}
                    break
            if j % 50 == 0:
                print('conductor', q, 'root seeds', j, flush=True)
    raise ArithmeticError('no off-line root found in bounded selector search')


def assemble(q, C, modes=80):
    c = Fraction(C)
    top = -(-c.numerator//c.denominator)
    _, _, _, period = datum(q)
    a = [arb(0)]+[period[n % q] for n in range(1, top+1)]
    coef = log_derivative_coefficients(a)
    length = arb(str(c)).log()
    def cell(m, n):
        return geometric_entry(m, n, length, coef, top)+(arb(q)/5).log()*(m == n)
    diagonal, opposite, b = [cell(0, 0)], [], [arb(0)]
    for n in range(1, modes+1):
        b.append(n*cell(n, 0))
        diagonal.append(cell(n, n))
        opposite.append(cell(n, -n))
    E = [[arb(0) for _ in range(modes+1)] for _ in range(modes+1)]
    O = [[arb(0) for _ in range(modes)] for _ in range(modes)]
    E[0][0] = diagonal[0]
    for n in range(1, modes+1):
        E[0][n] = E[n][0] = arb(2).sqrt()*b[n]/n
        E[n][n], O[n-1][n-1] = diagonal[n]+opposite[n-1], diagonal[n]-opposite[n-1]
        for m in range(1, n):
            E[m][n] = E[n][m] = 2*(n*b[n]-m*b[m])/(n*n-m*m)
            O[m-1][n-1] = O[n-1][m-1] = 2*(m*b[n]-n*b[m])/(n*n-m*m)
    return E, O


def trial(q, C):
    with ctx.workprec(768):
        E, O = assemble(q, C)
        sectors = []
        for parity, A in [('even', E), ('odd', O)]:
            try:
                s = negative_ldl_witness(A)
            except ArithmeticError as e:
                s = {'unresolved': str(e)}
            s.update(parity=parity, matrix=[[endpoints(x) for x in row] for row in A])
            sectors.append(s)
        status = ('negative_full_form_trial' if any('normalized_full_form' in s for s in sectors)
                  else 'positive_finite_sections_only' if all(s.get('positive_finite_section') for s in sectors)
                  else 'unresolved')
        result = {'status': status, 'conductor': q, 'C': str(C), 'modes': 80, 'sectors': sectors}
    path = OUT/f'analogue_q{q}_C{str(C).replace("/", "_")}.json'
    path.write_text(json.dumps(result, indent=2)+'\n')
    print('conductor', q, 'C', C, status, flush=True)
    return result, path


def run(q):
    OUT.mkdir(parents=True, exist_ok=True)
    zero = root(q)
    with ctx.workprec(512):
        label, epsilon, k, period = datum(q)
        checks = []
        for s in [acb('.7', '12'), acb('.3', '40'), acb('1.3', '23')]:
            def completed(z):
                return (z*(arb(q)/arb.pi()).log()/2).exp()*((z+1)/2).gamma()*jet(z, q, period)[0]
            defect = completed(s)-completed(1-s)
            if not defect.contains(0):
                raise ArithmeticError('analogue functional-equation check failed')
            checks.append({'real': endpoints(s.real), 'imag': endpoints(s.imag),
                           'defect_real': endpoints(defect.real), 'defect_imag': endpoints(defect.imag)})
        payload = {'conductor': q, 'Conrey_character_label': label,
            'root_number': {'real': endpoints(epsilon.real), 'imag': endpoints(epsilon.imag)},
            'kappa': endpoints(k), 'zero': zero, 'functional_equation_checks': checks,
            'normalization': 'H=(1-i*kappa)L(chi)/2+(1+i*kappa)L(conj chi)/2; kappa=Im epsilon/(1+Re epsilon); odd gamma, root number +1',
            'records': [], 'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                ['dh_analogue_controls.py', 'dh_weil_certificate.py', 'davenport_heilbronn_control.py']}}
    low, high = Fraction(2), None
    for C in map(Fraction, [2, 4, 8, 16, 32, 64]):
        d, p = trial(q, C)
        payload['records'].append({'C': str(C), 'status': d['status'], 'file': str(p), 'sha256': sha256(p)})
        if d['status'] == 'negative_full_form_trial':
            high = C
            break
        if d['status'] != 'positive_finite_sections_only':
            break
        low = C
    if high is not None:
        for _ in range(8):
            mid = (low+high)/2
            d, p = trial(q, mid)
            payload['records'].append({'C': str(mid), 'status': d['status'], 'file': str(p), 'sha256': sha256(p)})
            if d['status'] == 'negative_full_form_trial':
                high = mid
            elif d['status'] == 'positive_finite_sections_only':
                low = mid
            else:
                break
        payload.update(positive_finite_evidence_C=str(low), negative_certificate_C=str(high))
    payload['scope'] = 'Certified off-line zero and full negative trials for a different conductor. Positive finite evidence is not a lower bound for the first full negative support. No asymptotic exchange law is fitted from these upper bounds.'
    (OUT/f'analogue_q{q}_summary.json').write_text(json.dumps(payload, indent=2)+'\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--conductor', type=int, choices=[13, 17], required=True)
    run(p.parse_args().conductor)
