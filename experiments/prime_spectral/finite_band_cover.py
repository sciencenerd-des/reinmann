"""Arb proposals for finite-width boxes using the proved height-32 budgets.

The existing height-14.1 rectangle supplies the lower part. This script plans
only the additional upper box. A plan is not a Lean nonvanishing certificate.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import time

import flint
from flint import acb, acb_series, arb, ctx
from xi_lean_constant_cover import ar, regular_model, ceil_sqrt, l1
from xi_evaluator_comparison import gamma_stirling

GAMMA_ERROR = Q(4, 10**14)
ZETA_ERROR = Q(1, 5000)


def coefficients(x, y, degree):
    s = acb_series([acb(ar(x), ar(y)), 1])
    gamma = gamma_stirling(s + 2, 12, 7)
    zeta = regular_model(s)
    pi = (-s * arb.pi().log() / 2).exp()
    xi = pi * gamma * zeta
    reference = (1 + s / 2).gamma() * pi * (s - 1) * s.zeta()
    result = []
    for k in range(degree + 1):
        assert abs(xi[k] - reference[k]) < ar(Q(1, 10**9))
        centre = tuple(Q(round(float(t.mid()) * 2**50), 2**50)
                       for t in (xi[k].real, xi[k].imag))
        error = arb(0)
        for j in range(k + 1):
            inner = sum((ar(GAMMA_ERROR) * l1(zeta[k-j-i]) +
                         l1(gamma[i]) * ar(ZETA_ERROR) + ar(GAMMA_ERROR * ZETA_ERROR)
                         for i in range(k-j+1)), arb(0))
            error += l1(pi[j]) * inner
        delta = l1(xi[k] - acb(ar(centre[0]), ar(centre[1])))
        needed = (error + delta) * ar(Q(11, 10)) + ar(Q(1, 2**60))
        epsilon = Q(1, 2**80)
        while not needed < ar(epsilon):
            epsilon *= 2
        result.append((centre, epsilon))
    return result


def run(output, rank, degree, bits, max_nodes):
    ctx.prec, ctx.cap = bits, degree + 1
    x0, height = (Q(7, 8), Q(19)) if rank == 58 else (Q(29, 40), Q(32))
    initial = (x0, Q(1), Q(141, 10), height)
    tiles = []
    attempts = 0
    start = time.monotonic()

    def visit(box):
        nonlocal attempts
        attempts += 1
        if attempts > max_nodes:
            raise RuntimeError('Incomplete cover: node budget exhausted')
        x0, x1, y0, y1 = box
        x, y = (x0+x1)/2, (y0+y1)/2
        r = ceil_sqrt(((x1-x0)/2)**2 + ((y1-y0)/2)**2)
        accepted = False
        if r < 1:
            coeffs = coefficients(x, y, degree)
            v, e0 = coeffs[0]
            square = v[0]**2 + v[1]**2
            scaled = square * 2**140
            lower = Q(math.isqrt(scaled.numerator // scaled.denominator), 2**70)
            assert lower**2 <= square
            derivative = sum(Q(k)*(abs(vk[0])+abs(vk[1])+ek)*r**(k-1)
                             for k, (vk, ek) in enumerate(coeffs) if k)
            derivative += 1000*r**degree*(r/(1-r)**2 + Q(degree+1)/(1-r))
            derivative = Q(-(-derivative.numerator*2**30//derivative.denominator), 2**30)
            margin = lower-e0-derivative*r
            accepted = margin > lower/10
        if accepted:
            index = len(tiles)
            tiles.append({'index': index, 'box': [str(q) for q in box],
                          'centre': [str(x), str(y)], 'radius': str(r), 'degree': degree,
                          'centre_value': [str(q) for q in v], 'centre_norm_lower': str(lower),
                          'coefficient_centres': [[str(q) for q in vk] for vk, _ in coeffs],
                          'coefficient_error_radii': [str(e) for _, e in coeffs],
                          'derivative_bound': str(derivative), 'predicted_margin': str(margin),
                          'predicted_margin_decimal': float(margin)})
            return {'tile': index}
        axis = 'x' if x1-x0 >= y1-y0 else 'y'
        lo = (x0, x, y0, y1) if axis == 'x' else (x0, x1, y0, y)
        hi = (x, x1, y0, y1) if axis == 'x' else (x0, x1, y, y1)
        return {'split': axis, 'at': str(x if axis == 'x' else y),
                'lower': visit(lo), 'upper': visit(hi)}

    tree = visit(initial)
    result = {'status': 'external_Arb_cover_plan', 'rank': rank,
              'quarter': [str(q) for q in initial], 'degree': degree, 'bits': bits,
              'M': 1000, 'Gamma_error': str(GAMMA_ERROR), 'zeta_error': str(ZETA_ERROR),
              'zeta_model_endpoint': 27, 'log_scale': 32, 'log_terms': 160,
              'budget_theorems': 'FiniteBandBounds: height 32; no extrapolated constants',
              'python_flint_version': flint.__version__, 'tile_count': len(tiles),
              'attempts': attempts, 'seconds': time.monotonic()-start,
              'tiles': tiles, 'coverage_tree': tree, 'zero_free_rectangle_certified': False,
              'RH_proved': False, 'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('x') as stream:
        stream.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('tiles', 'coverage_tree')}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int, choices=(58, 97), required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--degree', type=int, choices=(8, 12, 16), default=16)
    parser.add_argument('--bits', type=int, default=128)
    parser.add_argument('--max-nodes', type=int, default=20000)
    args = parser.parse_args()
    run(args.output, args.rank, args.degree, args.bits, args.max_nodes)
