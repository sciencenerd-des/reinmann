"""DH-first diagnostic for exact Legendre coefficients of a window shift source.

No window positivity certificate is produced. All high-mode sums are finite.
The predicted 1/N coefficient uses classical fixed-interior Legendre asymptotics.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.special import eval_legendre
from flint import ctx
from davenport_heilbronn_control import dirichlet_coefficients, log_derivative_coefficients

ROOT = Path(__file__).resolve().parents[2]


def arithmetic(C, dh):
    stop = math.ceil(C)
    if dh:
        with ctx.workprec(256):
            c = log_derivative_coefficients(dirichlet_coefficients(stop))
            return [(n, float(c[n].mid()) / math.sqrt(n)) for n in range(2, stop)
                    if n < C and not c[n].contains(0)]
    result = []
    for n in range(2, stop):
        if n >= C:
            continue
        p = next((p for p in range(2, n + 1) if n % p == 0), None)
        k = n
        while k % p == 0:
            k //= p
        if k == 1:
            result.append((n, math.log(p) / math.sqrt(n)))
    return result


def probe(C, dh, max_degree=65536):
    L = math.log(C)
    aw = arithmetic(C, dh)
    x = np.array([2 * math.log(n) / L - 1 for n, _ in aw])
    w = np.array([a for _, a in aw])
    prev, curr = np.ones(len(x)), x.copy()
    coeff = np.zeros(max_degree + 1)
    for k in range(1, max_degree + 1):
        nxt = ((2 * k + 1) * x * curr - k * prev) / (k + 1)
        coeff[k] = (1 + (-1)**k) * np.dot(w, prev - nxt) / (2 * math.sqrt(2 * k + 1))
        prev, curr = curr, nxt
    # Merge coincident jumps. This is essential at C=4, where the n=2
    # contribution to S(1/sqrt(L)) is constant and has no high-mode tail.
    jumps = []
    for n, a in aw:
        for pos, jump in [(math.log(n), a), (L - math.log(n), -a)]:
            found = next((j for j in jumps if abs(j[0] - pos) < 1e-12), None)
            if found is None:
                jumps.append([pos, jump])
            else:
                found[1] += jump
    K = sum(j*j * math.sqrt(max(0, 1 - (2*t/L - 1)**2)) for t, j in jumps) / (2*math.pi)
    bands = []
    for N in [128, 512, 2048, 8192, 32768]:
        if 2 * N > max_degree:
            continue
        energy = float(np.dot(coeff[N+1:2*N+1], coeff[N+1:2*N+1]))
        bands.append(dict(N=N, finite_band_energy=energy, predicted=K/(2*N), ratio=2*N*energy/K))
    # Independent real-space quadrature checks the exact coefficient formula.
    errors = []
    points = sorted({0.0, L, *[t for t, _ in jumps]})
    for k in [2, 4, 8, 16]:
        def integrand(t):
            g = sum(a*((t >= math.log(n)) + (t <= L-math.log(n))) for n, a in aw)
            return math.sqrt(2*k+1)/L * eval_legendre(k, 2*t/L-1) * g
        direct = sum(quad(integrand, a, b, epsabs=1e-12, epsrel=1e-12)[0]
                     for a, b in zip(points[:-1], points[1:]) if b > a)
        errors.append(abs(direct - coeff[k]))
    assert max(errors) < 1e-10
    assert float(np.max(np.abs(coeff[1::2]))) == 0
    return dict(control='DH' if dh else 'zeta', C=C, cutoff_terms=len(aw),
                sum_absolute_comb_weights=2*sum(abs(a) for _, a in aw),
                sum_squared_weights=sum(a*a for _, a in aw), jump_tail_constant=K,
                max_quadrature_difference=max(errors), finite_band_checks=bands)


def main(output):
    rows = [probe(C, dh) for dh in [True, False] for C in [4., math.exp(2), 9.5, 19.]]
    result = dict(status='floating_finite_band_diagnostic_not_certificate', rows=rows,
                  input='constant normalized low vector; actual DH log-derivative coefficients before zeta',
                  scope='Shared approximation lemma, not an RH discriminator. No infinite tail, Schur complement or positivity bound is certified.',
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path(output).write_text(json.dumps(result, indent=2)+'\n')
    for r in rows:
        print(r['control'], r['C'], 'K', r['jump_tail_constant'],
              'last finite-band ratio', r['finite_band_checks'][-1]['ratio'])


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', required=True)
    main(p.parse_args().output)
