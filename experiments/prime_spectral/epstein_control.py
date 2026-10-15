"""Independent x^2+5y^2 negative control, including its distinct gamma/poles."""
from fractions import Fraction
import json
import math
from pathlib import Path
from flint import acb, acb_series, arb, ctx, dirichlet_char
from certified_weil import endpoints, entry
from dh_weil_certificate import geometric_entry, negative_ldl_witness
from full_ground_fourier import sha256

OUT = Path('research/prime_spectral/verification_2026_10_12_sector')
CHARS = [dirichlet_char(20, 19), dirichlet_char(4, 3), dirichlet_char(5, 4)]


def jet(s, degree=1):
    old = ctx.cap
    try:
        ctx.cap = degree+1
        z = acb_series([s, 1])
        def L(q, chi):
            return sum((chi(n)*z.zeta(arb(n)/q) for n in range(1, q)),
                       acb_series([0]))*(-z*arb(q).log()).exp()
        # E(s,Q)/2 = (zeta(s)L(s,chi_-20)+L(s,chi_-4)L(s,chi_5))/2.
        return (z.zeta()*L(20, CHARS[0])+L(4, CHARS[1])*L(5, CHARS[2]))/2
    finally:
        ctx.cap = old


def certify_zero():
    with ctx.workprec(512):
        s = acb('.932969697', '15.668249531')
        for _ in range(12):
            f = jet(s)
            w = s-f[0]/f[1]
            s = acb(w.real.mid(), w.imag.mid())
        r = arb('1e-20')
        f = jet(s)
        d = acb(f[1].real.mid(), f[1].imag.mid())
        rect = acb(arb(s.real.mid(), r), arb(s.imag.mid(), r))
        left, right = abs(f[0])+r*abs(jet(rect)[1]-d), r*abs(d)
        if not left < right or not s.real-r > arb('1/2'):
            raise ArithmeticError('Epstein Rouche gate failed')
        checks = []
        for point in [acb('.7', '12'), acb('.3', '40')]:
            def completed(z):
                return (z*(arb(5).sqrt()/arb.pi()).log()).exp()*z.gamma()*jet(z)[0]
            defect = completed(point)-completed(1-point)
            if not defect.contains(0):
                raise ArithmeticError('Epstein functional equation check failed')
            checks.append({'defect_real': endpoints(defect.real), 'defect_imag': endpoints(defect.imag)})
        return {'real': endpoints(s.real), 'imag': endpoints(s.imag), 'radius': '1e-20',
            'offset': endpoints(arb(s.real.mid(), r)-arb('1/2')),
            'height': endpoints(arb(s.imag.mid(), r)),
            'rouche_left': endpoints(left), 'rouche_right': endpoints(right),
            'functional_equation_checks': checks}


def coefficients(count):
    a = [arb(0)]*(count+1)
    for n in range(1, count+1):
        representations = 0
        for y in range(-math.isqrt(n//5), math.isqrt(n//5)+1):
            square = n-5*y*y
            x = math.isqrt(square)
            if x*x == square:
                representations += 1 if x == 0 else 2
        a[n] = arb(representations)/2
    return a


def trial(C, modes=80):
    from davenport_heilbronn_control import log_derivative_coefficients
    c = Fraction(C)
    top = -(-c.numerator//c.denominator)
    with ctx.workprec(768):
        coef = log_derivative_coefficients(coefficients(top))
        length = arb(str(c)).log()
        def cell(m, n):
            # Duplication: 2 psi(1/2+it) = psi(1/4+it/2)
            # + psi(3/4+it/2) + 2 log 2. Epstein has one pole pair.
            return (geometric_entry(m, n, length, coef, top)
                    +entry(m, n, length, [], arb(str(c)))+arb(4).log()*(m == n))
        b, diagonal, opposite = [arb(0)], [cell(0, 0)], []
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
        result = {'status': status, 'C': str(C), 'modes': modes, 'bits': 768, 'sectors': sectors,
            'gamma_normalization': '(sqrt(5)/pi)^s Gamma(s) E(s,Q)/2; simple poles at 0 and 1',
            'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                ['epstein_control.py', 'dh_weil_certificate.py', 'certified_weil.py']}}
    path = OUT/f'epstein5_C{str(C).replace("/", "_")}.json'
    path.write_text(json.dumps(result, indent=2)+'\n')
    print('Epstein', C, status, flush=True)
    return result, path


def run():
    OUT.mkdir(parents=True, exist_ok=True)
    zero = certify_zero()
    payload = {'datum': 'Epstein x^2+5y^2', 'zero': zero, 'records': []}
    low, high = Fraction(2), None
    for C in map(Fraction, [2, 4, 8, 16, 32, 64]):
        d, p = trial(C)
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
            d, p = trial(mid)
            payload['records'].append({'C': str(mid), 'status': d['status'], 'file': str(p), 'sha256': sha256(p)})
            if d['status'] == 'negative_full_form_trial':
                high = mid
            elif d['status'] == 'positive_finite_sections_only':
                low = mid
            else:
                break
        payload.update(positive_finite_evidence_C=str(low), negative_certificate_C=str(high))
    payload['scope'] = 'Off-line zero and negative full-form trials are certificates conditional on the written explicit-formula normalization. Positive finite evidence is not a lower bound for the first full negative support.'
    payload['source_sha256'] = {n: sha256(Path(__file__).with_name(n)) for n in
        ['epstein_control.py', 'dh_weil_certificate.py', 'certified_weil.py']}
    (OUT/'epstein5_summary.json').write_text(json.dumps(payload, indent=2)+'\n')


if __name__ == '__main__':
    run()
