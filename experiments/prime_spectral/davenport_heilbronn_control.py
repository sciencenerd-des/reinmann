"""Arithmetic negative control for Euler-specific Weil hypotheses.

These are coefficients of -H'/H in its half-plane of absolute convergence,
not Taylor/Jensen coefficients and not a zeta prime-power substitution.
"""
import json
from pathlib import Path

from flint import arb, ctx

from certified_weil import endpoints
from full_ground_fourier import sha256
from weil_matrix import prime_powers

OUT = Path('research/prime_spectral/verification_2026_10_12_cluster')
SOURCE = 'https://www.mathnet.ru/eng/present13282'


def kappa():
    return ((10-2*arb(5).sqrt()).sqrt()-2)/(arb(5).sqrt()-1)


def dirichlet_coefficients(count, dh=True):
    if type(count) is not int or count < 1:
        raise ValueError('positive coefficient count required')
    k = kappa()
    period = [arb(0), arb(1), k, -k, arb(-1)]
    return [arb(0)] + [period[n % 5] if dh else arb(1) for n in range(1, count+1)]


def log_derivative_coefficients(a):
    """c*a = (a_n log n)_n, using a_1=1, for -H'/H=sum c_n n^-s."""
    if len(a) < 2 or not (a[1]-1).is_zero():
        raise ValueError('normalized Dirichlet series a_1=1 required')
    c = [arb(0) for _ in a]
    for n in range(2, len(a)):
        c[n] = a[n]*arb(n).log()-sum((c[d]*a[n//d] for d in range(2, n) if n % d == 0), arb(0))
    return c


def generate(count=64):
    with ctx.workprec(512):
        k = kappa()
        a = dirichlet_coefficients(count)
        c = log_derivative_coefficients(a)
        zeta = log_derivative_coefficients(dirichlet_coefficients(count, dh=False))
        prime_support = {q for q, _ in prime_powers(count)}
        first_negative = next(n for n in range(2, count+1) if c[n] < 0)
        first_mixed = next(n for n in range(2, count+1) if n not in prime_support and not c[n].contains(0))
        if first_negative != 3 or first_mixed != 6 or not c[6] > 0:
            raise ArithmeticError('Davenport--Heilbronn coefficient obstruction unresolved')
        if not c[6].overlaps((1+k*k)*arb(6).log()):
            raise ArithmeticError('mixed-prime closed form disagrees')
        for n in range(2, count+1):
            expected = next((arb(p).log() for q, p in prime_powers(count) if q == n), arb(0))
            if not zeta[n].overlaps(expected):
                raise ArithmeticError('zeta control failed')
        return {'status': 'certified_log_derivative_arithmetic_negative_control',
                'bits': 512, 'count': count, 'definition_source': SOURCE,
                'kappa': endpoints(k), 'first_negative_coefficient': first_negative,
                'first_non_prime_power_nonzero_coefficient': first_mixed,
                'c6_closed_form': '(1+kappa^2)*log(6)',
                'coefficients': {str(n): endpoints(c[n]) for n in range(2, count+1)},
                'zeta_control': 'all 63 coefficients enclose the von Mangoldt values',
                'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                                 ('davenport_heilbronn_control.py', 'certified_weil.py', 'weil_matrix.py')},
                'scope': 'Euler prime-power support and coefficient nonnegativity fail. No Toeplitz-minor scan or first negative Weil window has been computed.'}


if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT/'dh_arithmetic_control.json').write_text(json.dumps(generate(), indent=2)+'\n')
