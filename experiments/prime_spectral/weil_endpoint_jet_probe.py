"""DH-first finite-band probe after exact removal of endpoint jump profiles.

The input is the normalized linear Legendre vector. The corrected shift source
is continuous piecewise linear; only finite coefficient bands are computed.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.special import eval_legendre
from weil_endpoint_jump_probe import arithmetic


def probe(C, dh):
    L = math.log(C)
    aw = arithmetic(C, dh)
    x = np.array([2*math.log(n)/L-1 for n, _ in aw])
    w = np.array([a for _, a in aw])
    top = 65536
    polynomials = np.empty((top+3, len(x)))
    polynomials[0], polynomials[1] = 1, x
    for k in range(1, top+2):
        polynomials[k+1] = ((2*k+1)*x*polynomials[k]-k*polynomials[k-1])/(k+1)
    coeff = np.zeros(top+1)
    for k in range(2, top+1):
        integral = ((polynomials[k-2]-polynomials[k])/(2*k-1)
                    -(polynomials[k]-polynomials[k+2])/(2*k+3))/(2*k+1)
        coeff[k] = math.sqrt(3*(2*k+1))*(1-(-1)**k)*np.dot(w, integral)/2
    jumps = []
    # These are jumps of d/dt of g(t)=sqrt(L)*corrected_source(L*(t+1)/2).
    for n, a in aw:
        t = 2*math.log(n)/L-1
        for pos, jump in [(t, math.sqrt(3)*a), (-t, -math.sqrt(3)*a)]:
            found = next((j for j in jumps if abs(j[0]-pos) < 1e-12), None)
            if found is None:
                jumps.append([pos, jump])
            else:
                found[1] += jump
    K3 = sum(j*j*max(0, 1-t*t)**1.5 for t, j in jumps)/(6*math.pi)
    bands = []
    for N in [128, 512, 2048, 8192, 32768]:
        energy = float(np.dot(coeff[N+1:2*N+1], coeff[N+1:2*N+1]))
        predicted = 7*K3/(8*N**3)
        bands.append(dict(N=N, finite_band_energy=energy, predicted=predicted,
                          ratio=energy/predicted))
    points = sorted({-1., 1., *[t for t, _ in jumps]})
    errors = []
    for k in [3, 5, 9, 17]:
        def integrand(t):
            g = math.sqrt(3)*sum(a*((t-v)*(t>=v)+(t+v)*(t<=-v))
                                 for v, a in zip(x, w))
            return math.sqrt(2*k+1)/2*g*eval_legendre(k, t)
        direct = sum(quad(integrand, a, b, epsabs=1e-12, epsrel=1e-12)[0]
                     for a, b in zip(points[:-1], points[1:]) if b > a)
        errors.append(abs(direct-coeff[k]))
    assert max(errors) < 1e-10
    assert np.max(np.abs(coeff[2::2])) == 0
    return dict(control='DH' if dh else 'zeta', C=C, corrected_tail_constant=K3,
                max_quadrature_difference=max(errors), finite_band_checks=bands)


def main(output):
    rows = [probe(C, dh) for dh in [True, False] for C in [4., math.exp(2), 9.5, 19.]]
    result = dict(status='floating_finite_band_diagnostic_not_certificate', rows=rows,
                  input='Normalized linear vector; two endpoint jump profiles subtracted exactly.',
                  scope='No full Schur energy, infinite tail bound or window positivity is certified.',
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  arithmetic_source_sha256=hashlib.sha256(
                      Path(__file__).with_name('weil_endpoint_jump_probe.py').read_bytes()).hexdigest())
    Path(output).write_text(json.dumps(result, indent=2)+'\n')
    for r in rows:
        print(r['control'], r['C'], 'K3', r['corrected_tail_constant'],
              'last finite-band ratio', r['finite_band_checks'][-1]['ratio'])


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', required=True)
    main(p.parse_args().output)
