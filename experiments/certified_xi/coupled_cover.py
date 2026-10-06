"""Finite theta curvature cover using a coupled mean-value enclosure of G."""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from time import perf_counter
from flint import arb, ctx
from continuous_cover import moment_box, verify_partition
from laboratory import endpoints, sign


def quantities(lo, hi, cache):
    """Enclose q and the first three derivatives of log(q) on a cell."""
    moments = [moment_box(lo+j, hi+j, cache, max_order=3) for j in (-1, 0, 1)]
    kp = [v[1]/v[0] for v in moments]
    kpp = [v[2]/v[0]-(v[1]/v[0])**2 for v in moments]
    kppp = [v[3]/v[0]-3*v[1]*v[2]/v[0]**2+2*(v[1]/v[0])**3 for v in moments]
    t = arb(str(lo)).union(arb(str(hi)))
    q = 2*t*(2*t-1)/((2*t+2)*(2*t+1))*moments[0][0]*moments[2][0]/moments[1][0]**2
    lp = 1/t+2/(2*t-1)-2/(2*t+2)-2/(2*t+1)+kp[0]+kp[2]-2*kp[1]
    lpp = -1/t**2-4/(2*t-1)**2+4/(2*t+2)**2+4/(2*t+1)**2+kpp[0]+kpp[2]-2*kpp[1]
    lppp = 2/t**3+16/(2*t-1)**3-16/(2*t+2)**3-16/(2*t+1)**3+kppp[0]+kppp[2]-2*kppp[1]
    return t, q, lp, lpp, lppp


def numerator(t, q, lp, lpp):
    return q*(1-q)*lpp+q*lp**2+(1-q)**2/(t+1)**2


def numerator_derivative(t, q, lp, lpp, lppp):
    # Differentiate the entire numerator before enclosing its variation.
    d = 1-q
    return (q*d*lppp+q*lp*(3-2*q)*lpp+q*lp**3
            -2*q*d*lp/(t+1)**2-2*d**2/(t+1)**3)


def curvature_box(lo, hi, cache):
    if not 1 <= lo <= hi <= 8:
        raise ValueError('cover domain must lie in [1,8]')
    row = {'lo': str(lo), 'hi': str(hi), 'status': 'unresolved'}
    t, q, lp, lpp, lppp = quantities(lo, hi, cache)
    if not q > 0 or not q < 1 or not (1-q)**2 > 0:
        return dict(row, reason='q or squared deficit denominator')
    mid = (lo+hi)/2
    tm, qm, lpm, lppm, _ = quantities(mid, mid, cache)
    center = numerator(tm, qm, lpm, lppm)
    derivative = numerator_derivative(t, q, lp, lpp, lppp)
    radius = arb(str((hi-lo)/2))*abs(derivative).upper()
    g = center+arb(0, radius.upper())
    return dict(row, status=sign(g), G=endpoints(g),
                log_epsilon_second=endpoints(-g/(1-q)**2),
                midpoint_G=endpoints(center), derivative_G=endpoints(derivative),
                variation_radius=str(radius.upper().fmpq()))


def run(lo='1', hi='2', max_depth=16, max_cells=2000):
    lo, hi = Fraction(lo), Fraction(hi)
    if not 1 <= lo < hi <= 8 or not 0 <= max_depth <= 20 or not 1 <= max_cells <= 20000:
        raise ValueError('invalid cover domain or budget')
    ctx.prec = 256
    started = perf_counter()
    pending, cells, cache = [(lo, hi, 0)], [], {}
    while pending:
        a, b, depth = pending.pop()
        row = curvature_box(a, b, cache)
        if row['status'] == 'unresolved' and depth < max_depth and len(cells)+len(pending)+2 <= max_cells:
            mid = (a+b)/2
            pending.extend(((mid, b, depth+1), (a, mid, depth+1)))
        else:
            cells.append(row)
    cells.sort(key=lambda v: Fraction(v['lo']))
    verify_partition(cells, lo, hi)
    sources = [Path(__file__), Path(__file__).with_name('continuous_cover.py'),
               Path(__file__).with_name('continuous_theta.py'), Path(__file__).with_name('laboratory.py')]
    return {'schema_version': 1,
            'status': 'certified_finite_interval' if all(v['status']=='positive' for v in cells) else 'incomplete_cover',
            'method': 'coupled_G_derivative_mean_value', 'domain': [str(lo), str(hi)],
            'bits': 256, 'max_depth': max_depth, 'max_cells': max_cells,
            'theta_terms': 12, 'left_log_cutoff': 64, 'upper_u_cutoff': 4,
            'source_hashes': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
            'endpoint_parameters': len(cache), 'elapsed_seconds': perf_counter()-started, 'cells': cells,
            'trust_boundary': 'FLINT ball arithmetic, theta identity, tails, monotone split and mean-value theorem; not a Lean certificate',
            'scope': 'Finite declared interval only; unbounded theta estimate and higher-rank induction remain open.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lo', default='1')
    parser.add_argument('--hi', default='2')
    parser.add_argument('--max-depth', type=int, default=16)
    parser.add_argument('--max-cells', type=int, default=2000)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.lo, args.hi, args.max_depth, args.max_cells)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], len(result['cells']), 'cells', result['endpoint_parameters'],
          'endpoint parameters', round(result['elapsed_seconds'], 2), 'seconds')


if __name__ == '__main__':
    main()
