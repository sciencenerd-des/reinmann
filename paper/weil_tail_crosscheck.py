"""Independent cross-check for the infinite-rank Weil tail paper.

This script shares no code with experiments/prime_spectral.  It rebuilds the
Weil matrix from the closed formulas derived in the paper (Sections 2-3),
using mpmath only, and checks:

  1. closed entries against direct numerical quadrature of the defining
     Weil distributions (pole, archimedean principal value, primes);
  2. the paired omitted-mode identity (Lemma 4.1) against a direct
     matrix-vector product;
  3. the rank-8 even ground vector, its boundary sum and signed moments,
     against the saved certificate intervals;
  4. the omitted-mode forcing ||R_{n>64}||, summed directly to a large
     index plus the analytic tail of Theorem 4.3, against the certified
     bound 9.491e-12;
  5. the constants B, B_64, 2*pi*B_arch, 2P and the coercivity thresholds,
     using mpmath interval arithmetic.

Items 1-4 are high-precision floating checks, not proofs.  Item 5 uses
outward interval arithmetic.
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp
from mpmath import iv

mp.mp.dps = 80
ROOT = Path(__file__).resolve().parents[1]
CERT = ROOT / 'research/prime_spectral/weil_rank_tail_cell_17_19_8_degree64.json'
TAYLOR = ROOT / 'research/prime_spectral/weil_support_taylor_17_19_8_degree64.json'


def prime_powers(limit):
    out = []
    for p in range(2, int(limit) + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            a = p
            while a <= limit:
                out.append((a, p))
                a *= p
    return out


class Weil:
    """Closed Weil entries at support length L=log C (Proposition 3.4)."""

    def __init__(self, C, terms=60):
        self.L = mp.log(C)
        # Active prime powers p^a < C; a power equal to C contributes zero.
        self.powers = [(a, p) for a, p in prime_powers(mp.floor(C)) if a < C]
        self.terms = terms

    def w(self, n):
        return 2 * mp.pi * n / self.L

    def b(self, n):
        """Displacement b_n = n*A_(n,0) (Proposition 3.3)."""
        if n == 0:
            return mp.mpf(0)
        if n < 0:
            return -self.b(-n)
        L, w = self.L, self.w(n)
        D = mp.cosh(L / 2) - 1
        val = 2 * D / mp.pi * w / (mp.mpf(1) / 4 + w**2)
        val += mp.im(mp.digamma(mp.mpf(1) / 4 + 1j * mp.pi * n / L)) / (2 * mp.pi)
        val -= mp.nsum(lambda k: mp.exp(-(2 * k + mp.mpf(1) / 2) * L) * w
                       / ((2 * k + mp.mpf(1) / 2)**2 + w**2), [0, mp.inf]) / mp.pi
        val += sum(mp.log(p) / mp.sqrt(a) * mp.sin(w * mp.log(a)) for a, p in self.powers) / mp.pi
        return val

    def diag(self, n):
        L, w = self.L, self.w(n)
        D = mp.cosh(L / 2) - 1
        pole = 4 / L * D * (mp.mpf(1) / 4 - w**2) / (mp.mpf(1) / 4 + w**2)**2
        z = mp.mpf(1) / 4 + 1j * w / 2
        arch = mp.log(mp.pi) - mp.re(mp.digamma(z)) - mp.re(mp.psi(1, z)) / (2 * L)
        arch += mp.nsum(lambda k: 2 / L * mp.exp(-(2 * k + mp.mpf(1) / 2) * L)
                        * ((2 * k + mp.mpf(1) / 2)**2 - w**2)
                        / ((2 * k + mp.mpf(1) / 2)**2 + w**2)**2, [0, mp.inf])
        primes = sum(mp.log(p) / mp.sqrt(a) * 2 * (1 - mp.log(a) / L) * mp.cos(w * mp.log(a))
                     for a, p in self.powers)
        return pole - arch - primes

    def entry(self, m, n):
        if m == n:
            return self.diag(n)
        return (self.b(m) - self.b(n)) / (m - n)

    # ---- direct quadrature of the defining distributions (check 1) ----
    def q(self, m, n, y):
        if m == n:
            return 2 * (1 - y / self.L) * mp.cos(self.w(n) * y)
        return (mp.sin(self.w(m) * y) - mp.sin(self.w(n) * y)) / (mp.pi * (n - m))

    def entry_quadrature(self, m, n):
        L = self.L
        f = lambda y: self.q(m, n, y)
        pole = mp.quad(lambda y: f(y) * 2 * mp.cosh(y / 2), [0, L])
        F0 = f(mp.mpf(0))
        # W_R^#: (1/2)(log 4pi + gamma) F(0) + PV integral, F supported on [0,L].
        arch = (mp.log(4 * mp.pi) + mp.euler) / 2 * F0
        arch += mp.quad(lambda y: (mp.exp(y / 2) * f(y) - F0) / (2 * mp.sinh(y)), [0, L])
        arch -= F0 * mp.log(mp.coth(L / 2)) / 2
        primes = sum(mp.log(p) / mp.sqrt(a) * f(mp.log(a)) for a, p in self.powers)
        return pole - arch - primes

    def even_block(self, K):
        A = mp.matrix(K + 1, K + 1)
        r2 = mp.sqrt(2)
        for i in range(K + 1):
            for j in range(K + 1):
                if i == 0 and j == 0:
                    A[i, j] = self.entry(0, 0)
                elif i == 0 or j == 0:
                    A[i, j] = r2 * self.entry(i, j)
                else:
                    A[i, j] = self.entry(i, j) + self.entry(i, -j)
        return A


def ground(W, K):
    E, Q = mp.eigsy(W.even_block(K))
    k = min(range(K + 1), key=lambda i: E[i])
    u = [Q[i, k] for i in range(K + 1)]
    if u[0] < 0:
        u = [-x for x in u]
    return E[k], sorted(E)[1], u


def tail_forcing_direct(W, u, K, J, N):
    """sqrt(sum_{J<n<=N} R_n^2) and the Theorem 4.3 bound beyond N."""
    bK = [W.b(i) for i in range(K + 1)]
    S = u[0] + mp.sqrt(2) * sum(u[1:])
    total = mp.mpf(0)
    old = mp.mp.dps
    mp.mp.dps = 30
    for n in range(J + 1, N + 1):
        bn = W.b(n)
        R = mp.sqrt(2) * bn * S / n
        R += 2 * bn / n * sum(u[i] * i * i / (n * n - i * i) for i in range(1, K + 1))
        R -= 2 * sum(i * bK[i] * u[i] / (n * n - i * i) for i in range(1, K + 1))
        total += R * R
    mp.mp.dps = old
    return mp.sqrt(total)


def frac(s):
    return Fraction(s)


def check_constants():
    lo, hi = iv.log(17), iv.log(19)
    pi = iv.pi
    # exp(Lmin/2)=sqrt(17), exp(Lmax/2)=sqrt(19): exact forms avoid iv.cosh.
    r17, r19 = iv.sqrt(17), iv.sqrt(19)
    E = (1 / r17) / (1 - iv.mpf(1) / 289)
    P = sum((iv.log(p) / iv.sqrt(a) for a, p in prime_powers(17)), iv.mpf(0))
    Dmax = (r19 + 1 / r19) / 2 - 1
    imag = pi / 2 + hi / pi                      # min(2, Lmax/pi) = Lmax/pi here
    B = 2 * Dmax / pi + imag / (2 * pi) + E / pi + P / pi
    B0 = iv.mpf(1) / 4 + P / pi
    B1 = hi * (Dmax + (1 + E) / 2) / pi**2
    Barch = imag / (2 * pi) + E / pi
    neg_pole = (r19 - 1 / r19) - hi

    def beta(n, even):
        n = iv.mpf(n)
        v = (iv.log(n / hi) - hi / (pi * n) - 1 / (4 * n)
             - hi * (1 + E) / (2 * pi**2 * n * n) - 2 * pi * Barch - 2 * P)
        return v if even else v - neg_pole

    return {'P': P, 'E': E, 'B': B, 'B_64': B0 + B1 / 64, 'offdiag_norm': 2 * pi * B,
            'arch_offdiag_norm': 2 * pi * Barch, 'neg_pole': neg_pole,
            'beta_even(18612929)': beta(18612929, True), 'beta_even(18612928)': beta(18612928, True),
            'beta_full(60879750)': beta(60879750, False), 'beta_full(60879749)': beta(60879749, False)}


def main(N=int(sys.argv[1]) if len(sys.argv) > 1 else 20000):
    K, J = 8, 64
    ok = True
    print('== 5. constants (interval arithmetic) ==')
    iv.dps = 40
    for k, v in check_constants().items():
        print(f'  {k:24s} [{mp.nstr(v.a, 12)}, {mp.nstr(v.b, 12)}]')
    c = check_constants()
    ok &= c['beta_even(18612929)'].a > 1 and c['beta_full(60879750)'].a > 1
    ok &= c['B'].b < 3.157010 and c['B_64'].b < 2.115418 and c['offdiag_norm'].b < 19.836078

    W = Weil(17)
    print('== 1. closed entries vs quadrature of the Weil distributions (C=17) ==')
    mp.mp.dps = 30
    worst = 0
    for m, n in [(0, 0), (3, 3), (8, 8), (1, 0), (5, -2), (8, -8), (7, 6)]:
        d = abs(W.entry(m, n) - W.entry_quadrature(m, n))
        worst = max(worst, d)
        print(f'  ({m:2d},{n:2d}) closed={mp.nstr(W.entry(m, n), 15):>22s}  |diff|={mp.nstr(d, 3)}')
    ok &= worst < mp.mpf('1e-20')
    mp.mp.dps = 80

    cert = json.loads(CERT.read_text())
    taylor = json.loads(TAYLOR.read_text())
    centre = (Fraction(taylor['log_support_center']['lo']) + Fraction(taylor['log_support_center']['hi'])) / 2
    for C in (17, 18, 19):
        W = Weil(C)
        lam, lam2, u = ground(W, K)
        S = u[0] + mp.sqrt(2) * sum(u[1:])
        m = [sum(u[i] * mp.mpf(i)**(2 * r) for i in range(1, K + 1)) for r in (1, 2)]
        nu = [sum(u[i] * W.b(i) * mp.mpf(i)**(2 * r + 1) for i in range(1, K + 1)) for r in (0, 1)]
        print(f'== 3. C={C}: lambda_0={mp.nstr(lam, 6)}  gap={mp.nstr(lam2 - lam, 6)} ==')
        print(f'  S={mp.nstr(S, 6)}  m1={mp.nstr(m[0], 6)}  m2={mp.nstr(m[1], 6)}'
              f'  nu0={mp.nstr(nu[0], 6)}  nu1={mp.nstr(nu[1], 6)}')
        if centre is not None:
            x = Fraction(str(mp.nstr(W.L, 50))) - centre
            # The nearest subcell (C=17 and C=19 are the closed cell endpoints).
            cell = min(cert['cells'], key=lambda c: abs(x - frac(c['center_offset'])))
            for _ in (0,):
                o, h = frac(cell['center_offset']), frac(cell['half_width'])
                if abs(x - o) <= h + Fraction(1, 10**30):
                    b = cell['signed_boundary_interval']
                    inside = frac(b['lo']) <= Fraction(str(mp.nstr(S, 40))) <= frac(b['hi'])
                    m1 = cell['signed_even_moment_intervals'][0]
                    inside &= frac(m1['lo']) <= Fraction(str(mp.nstr(m[0], 40))) <= frac(m1['hi'])
                    n0 = cell['signed_arithmetic_moment_intervals'][0]
                    inside &= frac(n0['lo']) <= Fraction(str(mp.nstr(nu[0], 40))) <= frac(n0['hi'])
                    print(f'  subcell {cell["index"]}: S, m1, nu0 inside certified intervals: {inside}')
                    ok &= inside
                    break

        # 2. paired identity vs direct product, at a few omitted indices
        cfull = {0: u[0]}
        for i in range(1, K + 1):
            cfull[i] = cfull[-i] = u[i] / mp.sqrt(2)
        for n in (9, 65, 1000):
            direct = mp.sqrt(2) * sum(W.entry(n, j) * cfull[j] for j in cfull)
            bn = W.b(n)
            paired = (mp.sqrt(2) * bn * S / n
                      + 2 * bn / n * sum(u[i] * i * i / (n * n - i * i) for i in range(1, K + 1))
                      - 2 * sum(i * W.b(i) * u[i] / (n * n - i * i) for i in range(1, K + 1)))
            ok &= abs(direct - paired) < mp.mpf('1e-60')
        print('  2. paired omitted-mode identity matches direct product at n=9,65,1000')

        # 4. direct omitted-mode sum and analytic remainder beyond N
        head = tail_forcing_direct(W, u, K, J, N)
        # Theorem 4.3 beyond N with signed moments to order R=4.
        R = 4
        Bt = mp.mpf('3.157010')  # outward upper bound for B, checked in item 5
        bK = [W.b(i) for i in range(K + 1)]
        mom = [sum(u[i] * mp.mpf(i)**(2 * r) for i in range(1, K + 1)) for r in range(1, R + 1)]
        nus = [sum(u[i] * bK[i] * mp.mpf(i)**(2 * r + 1) for i in range(1, K + 1)) for r in range(R)]
        M = sum(abs(u[i]) * mp.mpf(i)**(2 * R + 2) for i in range(1, K + 1))
        V = sum(abs(u[i] * bK[i]) * mp.mpf(i)**(2 * R + 1) for i in range(1, K + 1))
        g = 1 / (1 - mp.mpf(K * K) / (N * N))
        H = lambda p: mp.mpf(N)**(mp.mpf(1) / 2 - p) / mp.sqrt(2 * p - 1)
        rest = mp.sqrt(2) * Bt * abs(S) * H(1)
        rest += 2 * Bt * sum(abs(x) * H(2 * r + 1) for r, x in enumerate(mom, 1))
        rest += 2 * sum(abs(x) * H(2 * r + 2) for r, x in enumerate(nus))
        rest += 2 * g * (Bt * M * H(2 * R + 3) + V * H(2 * R + 2))
        total = head + rest
        print(f'  4. direct ||R_(64<n<={N})|| = {mp.nstr(head, 6)};  bound beyond N <= {mp.nstr(rest, 3)};'
              f'  total <= {mp.nstr(total, 6)}  (certified < 9.491e-12)')
        ok &= total < mp.mpf('9.491e-12')
    print('ALL CHECKS PASSED' if ok else 'CHECK FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
