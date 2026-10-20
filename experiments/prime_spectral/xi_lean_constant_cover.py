"""Plan rational Xi balls with the actual Lean Cauchy constant and factor budgets.

External Arb planning only. The regular factors avoid both low-height poles.
Each output radius and margin test is rational; coefficient proposals still
need Lean soundness proofs. The binary cell tree supplies a coverage recipe.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import time

from flint import acb, acb_series, arb, ctx
import xi_evaluator_comparison as old


def ar(q):
    return arb(str(q))


def regular_model(s, endpoint=27):
    terms = sum(((-s * arb(n).log()).exp() for n in range(1, endpoint)), acb_series([0]))
    power = (-s * arb(endpoint).log()).exp()
    correction = acb_series([0])
    for k in range(1, 7):
        rising = acb_series([1])
        for j in range(2 * k - 1):
            rising *= s + j
        correction += arb.bernoulli(2 * k) / math.factorial(2 * k) * rising * power / endpoint ** (2 * k - 1)
    return (s - 1) * (terms + power / 2 + correction) + endpoint * power


def l1(z):
    return abs(z.real) + abs(z.imag)


def ceil_sqrt(q, bits=20):
    scaled = q * 2 ** (2 * bits)
    n = math.isqrt(scaled.numerator // scaled.denominator)
    if Q(n * n) < scaled:
        n += 1
    return Q(n, 2 ** bits)


def coefficients(x, y, degree):
    s = acb_series([acb(ar(x), ar(y)), 1])
    gamma = old.gamma_stirling(s + 2, 12, 7)
    zeta = regular_model(s)
    pi = (-s * arb.pi().log() / 2).exp()
    xi = pi * gamma * zeta
    reference = (1 + s / 2).gamma() * pi * (1 + (s - 1) * s.zeta(deflate=True))
    assert all(xi[k].overlaps(reference[k]) or abs(xi[k] - reference[k]) < ar(Q(1, 10**10))
               for k in range(degree + 1))
    result = []
    for k in range(degree + 1):
        centre = tuple(Q(round(float(t.mid()) * 2**30), 2**30)
                       for t in (xi[k].real, xi[k].imag))
        error = arb(0)
        # L1 centre bounds match CertifiedTaylorModel, rather than using
        # optimistic Euclidean operator norms for its arithmetic.
        for j in range(k + 1):
            inner = arb(0)
            for i in range(k - j + 1):
                inner += ar(Q(4, 10**14)) * l1(zeta[k - j - i])
                inner += l1(gamma[i]) * ar(Q(6, 10**8))
                inner += ar(Q(4, 10**14) * Q(6, 10**8))
            error += l1(pi[j]) * inner
        delta = l1(xi[k] - acb(ar(centre[0]), ar(centre[1])))
        # Reserve for finite scalar/log certificate and outward-rounding cost.
        needed = (error + delta) * ar(Q(11, 10)) + ar(Q(1, 10**10))
        epsilon = Q(1, 10**7)
        while not needed < ar(epsilon):
            epsilon *= 2
        result.append((centre, epsilon))
    return result


def run(output, degree, bits, max_nodes):
    ctx.prec, ctx.cap = bits, degree + 1
    start = time.monotonic()
    tiles = []
    attempts = 0

    def visit(box):
        nonlocal attempts
        attempts += 1
        if attempts > max_nodes:
            raise RuntimeError('Node limit: no complete cover may be claimed')
        x0, x1, y0, y1 = box
        x, y = (x0 + x1) / 2, (y0 + y1) / 2
        r = ceil_sqrt(((x1 - x0) / 2) ** 2 + ((y1 - y0) / 2) ** 2)
        accepted = False
        if r < 1:
            coeffs = coefficients(x, y, degree)
            v, e0 = coeffs[0]
            square = v[0] ** 2 + v[1] ** 2
            n = math.isqrt((square * 2**80).numerator // (square * 2**80).denominator)
            value_lower = Q(n, 2**40)
            assert value_lower**2 <= square
            derivative = sum(Q(k) * (abs(vk[0]) + abs(vk[1]) + ek) * r ** (k - 1)
                             for k, (vk, ek) in enumerate(coeffs) if k)
            derivative += 1000 * r**degree * (r / (1 - r)**2 + Q(degree + 1) / (1 - r))
            margin = value_lower - e0 - derivative * r
            accepted = margin > value_lower / 10
        if accepted:
            index = len(tiles)
            tiles.append({'index': index, 'box': [str(q) for q in box],
                          'centre': [str(x), str(y)], 'radius': str(r), 'degree': degree,
                          'centre_value': [str(q) for q in v], 'centre_norm_lower': str(value_lower),
                          'coefficient_centres': [[str(q) for q in v] for v, _ in coeffs],
                          'coefficient_error_radii': [str(e) for _, e in coeffs],
                          'derivative_bound': str(derivative), 'predicted_margin': str(margin),
                          'predicted_margin_decimal': float(margin)})
            return {'tile': index}
        if x1 - x0 >= y1 - y0:
            return {'split': 'x', 'at': str(x),
                    'lower': visit((x0, x, y0, y1)), 'upper': visit((x, x1, y0, y1))}
        return {'split': 'y', 'at': str(y),
                'lower': visit((x0, x1, y0, y)), 'upper': visit((x0, x1, y, y1))}

    tree = visit((Q(1, 2), Q(1), Q(0), Q(141, 10)))
    top = [t for t in tiles if Q(t['box'][3]) == Q(141, 10)]
    result = {'status': 'external_Arb_cover_plan', 'quarter': ['1/2', '1', '0', '141/10'],
              'bits': bits, 'degree': degree, 'M': 1000,
              'Gamma_factor': 'Gamma(1+s/2)', 'Gamma_error': '4e-14',
              'zeta_factor': 'analytic extension of (s-1)*zeta(s)',
              'zeta_model_endpoint': 27, 'zeta_error': '6e-8',
              'uniform_budget_proof_status': 'compiled: UniformXiRemainders.gamma_coefficient_error_le and zeta_coefficient_error_le',
              'tile_count': len(tiles), 'attempts': attempts, 'seconds': time.monotonic() - start,
              'top_edge_tiles': len(top),
              'top_edge_radius_min': min((t['radius'] for t in top), key=Q),
              'top_edge_radius_max': max((t['radius'] for t in top), key=Q),
              'tiles': tiles, 'coverage_tree': tree,
              'zero_free_rectangle_certified': False, 'RH_proved': False,
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('tiles', 'coverage_tree')}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--degree', type=int, choices=(8, 12, 16), default=8)
    parser.add_argument('--bits', type=int, default=96)
    parser.add_argument('--max-nodes', type=int, default=20000)
    args = parser.parse_args()
    run(args.output, args.degree, args.bits, args.max_nodes)
