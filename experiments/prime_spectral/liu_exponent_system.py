"""Exact scalar ledger for Liu 2610.12234v2; no new analytic estimate.

Moment parameters other than the published inputs are formal hypotheses.
The full direct majorant is retained even when count constraints are deleted.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
import json
from math import comb
from pathlib import Path
import subprocess

import sympy as sp

XI_INTERVAL = (F(38858, 100000), F(38859, 100000))
ALPHA = F(5, 6)


def boundary(ell):
    return F(11, 12)-ell/4


def geometry(xi):
    kappa = (18*xi**2-57*xi+20)/(6*(36*xi**2-78*xi+25))
    ell = (5-6*xi)/(9+18*xi)
    b = 8*(3*xi-1)*(12*xi**2-40*xi+15)/(9*(2*xi+1)*(24*xi**2-20*xi+5))
    lx, ly = (1-b-ell)/2, (1+b-ell)/2
    return dict(kappa=kappa, ell=ell, b=b, lx=lx, ly=ly,
                h=1-lx+ell, B=(18*xi+7)/(18*xi+9))


def count_closed(delta, x, kappa, alpha=ALPHA):
    """Liu (29.1)-(29.3); formal alpha variation requires alpha>=delta."""
    if not 0 <= delta <= alpha or not 0 <= x <= F(1, 2) or kappa <= 0:
        raise ValueError('invalid count domain; do not extrapolate past alpha')
    c = F(2, 3)/kappa
    D, P = 3-(1+c)*x, (2-c*x)*(1-x)
    J = (alpha-delta)*D+delta*P
    if D <= 0 or P <= 0 or J <= 0:
        raise ValueError('positive count denominators required')
    t = 1+delta*P/(2*J)
    r = ((2-c*x)*t+(c/2-1)*x)/D
    return {'R': 1-delta+(alpha-delta)*delta*P/(2*J),
            't': t, 'r': r, 'm': t-r, 'J': J}


def direct_components(lx, ly, ell):
    M, b = lx+ly, ly-lx
    k = max(F(0), (1+3*ell-2*M)/4, M+ell-1, (3*ell-1)/2)
    gram = max(F(0), b/12, b-ly/2)
    low = lx/2+gram+k/2
    return {'reflection_k': k, 'gram': gram, 'L_low': low,
            'B_low': low+F(5, 6)-lx/3-ell/6}


def nonprincipal(lx, ly, ell, B, delta, x, d, R, z0=F(17, 50)):
    """Liu (18.4), including free total averaging length."""
    a, h = (1+delta)/2, 1-lx+ell
    return a-B+h*(z0-F(1, 6))-a*ly-ell/2+delta*x*ell+d*(R+delta/2-z0)


@dataclass(frozen=True)
class MomentInputs:
    """Length/range costs in the supplied moments, not proved new inputs."""
    alpha: F = ALPHA
    inverse_prime_cost: F = F(2)
    inverse_second_range: F = F(3)
    inverse_second_length_cost: F = F(2)
    inverse_second_prime_cost: F = F(8)
    plain_length_cost: F = F(2)
    plain_prime_cost: F = F(9, 2)  # 6*kappa at kappa=3/4

    def __post_init__(self):
        if not 0 < self.alpha <= 1 or any(getattr(self, n) <= 0 for n in (
                'inverse_prime_cost', 'inverse_second_range',
                'inverse_second_length_cost', 'inverse_second_prime_cost',
                'plain_length_cost', 'plain_prime_cost')):
            raise ValueError('positive costs and 0<alpha<=1 required')


def detector_count_at_t(t, delta, x, inputs=MomentInputs(), prime_support=F(1)):
    """Exact sup_r min(moment exponents) on m=t-r, using affine cells.

    The length face m=t-r is worst for the supplied monotonically improving
    short moments. Altered inputs are a scalar sensitivity model only.
    Analytic support margins and discretization losses are suppressed.
    """
    if not 1 <= t <= F(3, 2) or not 0 <= delta <= 1 or not 0 <= x <= F(1, 2):
        raise ValueError('invalid detector/class parameters')
    if prime_support < 0:
        raise ValueError('nonnegative prime support required')
    if inputs.plain_prime_cost < x*inputs.plain_length_cost:
        raise ValueError('short count not monotone in m; length-face reduction unavailable')
    # A line is (intercept, slope) in the inverse detector length r.
    zM = [(F(1)/inputs.inverse_prime_cost, -F(1)/inputs.inverse_prime_cost),
          (inputs.inverse_second_range/inputs.inverse_second_prime_cost,
           -inputs.inverse_second_length_cost/inputs.inverse_second_prime_cost),
          (prime_support, F(0))]
    zS = [((1-inputs.plain_length_cost*t)/inputs.plain_prime_cost,
           inputs.plain_length_cost/inputs.plain_prime_cost), (prime_support, F(0))]
    def at(line, r):
        return line[0]+line[1]*r
    def crossing(a, b):
        return None if a[1] == b[1] else (b[0]-a[0])/(a[1]-b[1])
    left, right = t-F(1, 2), t
    breaks = {left, right, F(1)}
    for lines in (zM, zS):
        for i, a in enumerate(lines):
            q = crossing(a, (F(0), F(0)))
            if q is not None:
                breaks.add(q)
            for b in lines[i+1:]:
                q = crossing(a, b)
                if q is not None:
                    breaks.add(q)
    breaks = sorted(q for q in breaks if left <= q <= right)
    best = None
    for a, b in zip(breaks[:-1], breaks[1:]):
        mid = (a+b)/2
        amp = ((F(1), -delta) if mid <= 1 else
               (1-inputs.alpha, inputs.alpha-delta))
        lines = [amp]
        zm = min(zM, key=lambda v: at(v, mid))
        if at(zm, mid) >= 0:
            lines.append((1-2*delta*x*zm[0], -delta-2*delta*x*zm[1]))
        zs = min(zS, key=lambda v: at(v, mid))
        # The unselected ordinary fourth moment remains available without
        # its selected-prime length restriction (Liu 28.1).
        lines.append((1-2*delta*t, 2*delta))
        if at(zs, mid) >= 0:
            lines.append((1-2*delta*t-2*delta*x*zs[0],
                          2*delta-2*delta*x*zs[1]))
        candidates = {a, b}
        for i, u in enumerate(lines):
            for v in lines[i+1:]:
                q = crossing(u, v)
                if q is not None and a <= q <= b:
                    candidates.add(q)
        for r in candidates:
            value = min(at(line, r) for line in lines)
            if best is None or value > best['R']:
                best = dict(R=value, r=r, m=t-r, t=t)
    if best is None:
        raise ArithmeticError('empty detector subdivision')
    return best


def isolate_decreasing_root(coefficients, interval=XI_INTERVAL, bits=170):
    lo, hi = interval
    def polynomial(x):
        result = F(0)
        for c in coefficients:
            result = result*x+c
        return result
    if not polynomial(lo) > 0 > polynomial(hi):
        raise ValueError('decreasing sign bracket required')
    for _ in range(bits):
        mid = (lo+hi)/2
        if polynomial(mid) > 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


def bernstein_positive(expr, variable, interval=XI_INTERVAL):
    """Exact positive numerator/denominator Bernstein coefficient bound."""
    num, den = map(sp.Poly, sp.fraction(sp.cancel(expr)), (variable, variable))
    if den.eval(sp.Rational(sum(interval)/2)) < 0:
        num, den = -num, -den
    z = sp.Symbol('z')
    lo, hi = map(sp.Rational, interval)
    def coefficients(poly):
        degree = poly.degree()
        shifted = sp.Poly(poly.as_expr().subs(variable, lo+(hi-lo)*z), z)
        powers = [shifted.nth(i) for i in range(degree+1)]
        return [sum(powers[j]*F(comb(i, j), comb(degree, j)) for j in range(i+1))
                for i in range(degree+1)]
    n, d = coefficients(num), coefficients(den)
    if min(n) <= 0 or min(d) <= 0:
        raise ArithmeticError('positive Bernstein certificate failed')
    return str(min(n)/max(d))


def symbolic_certificates():
    xi, delta, y, M, ell, b, kappa, alpha = sp.symbols('xi delta y M ell b kappa alpha')
    q = sp.Rational
    # Independent derivation of the direct LP dual from the full maximum.
    L0 = q(5, 6)+M/12-ell/6
    A = L0+(1+3*ell-2*M)/8
    LK = L0+(M+ell-1)/2
    weights = (q(17, 30), q(2, 5), q(1, 30))
    assert sum(weights) == 1
    assert sp.expand(sum(w*v for w, v in zip(weights, (L0, A, LK)))-q(13, 15)) == 0
    # Balanced simplified formula fails beyond ell=1/5 unless positive parts
    # in Liu (22.6) are retained.
    assert direct_components(F(7, 20), F(9, 20), F(1, 5))['B_low'] == F(13, 15)
    c = q(2, 3)/kappa
    D, P = 3-(1+c)*(q(1, 2)-y), (2-c*(q(1, 2)-y))*(q(1, 2)+y)
    J = (alpha-delta)*D+delta*P
    h, C0 = (1+b+3*ell)/2, -q(1, 4)+b/6+5*ell/4
    R = 1-delta+(alpha-delta)*delta*P/(2*J)
    E = C0+(q(1, 2)+ell)*delta+ell*(q(1, 2)-y)*delta-h*(1-R)
    Q = -2*C0*J+(b+2*ell*y)*delta*J-h*(alpha-delta)*delta*P
    assert sp.cancel(Q+2*J*E) == 0
    assert sp.factor(sp.diff(R, alpha)-delta**2*P**2/(2*J**2)) == 0
    # Derive A(y), B(y), C(y), discriminant directly; do not trust a grid.
    poly = sp.Poly(sp.expand(Q), delta)
    Ap, Bp, Cp = (sp.Poly(poly.nth(i), y) for i in (2, 1, 0))
    discr = sp.Poly(sp.expand(4*poly.nth(2)*poly.nth(0)-poly.nth(1)**2), y)
    geo = geometry(xi)
    substitution = {b: geo['b'], ell: geo['ell'], kappa: geo['kappa'], alpha: q(5, 6)}
    assert sp.cancel(discr.nth(0).subs(substitution)) == 0
    positive = {f'A{i}': Ap.nth(i) for i in range(4)}
    positive.update({f'd{i}': discr.nth(i) for i in range(1, 5)})
    bounds = {name: bernstein_positive(expr.subs(substitution), xi)
              for name, expr in positive.items()}
    gb, gl, gh, gx, gy, gB, gk = (geo[n] for n in ('b', 'ell', 'h', 'lx', 'ly', 'B', 'kappa'))
    gc, gC0 = q(2, 3)/gk, -q(1, 4)+gb/6+5*gl/4
    mI = lambda d: -((225*gl+50-75*gb)*d+78*gl-49*gb-73)/300
    reserves = dict([
        ('D0', 36*xi**2-78*xi+25), ('kappa_derivative', sp.diff(gk, xi)),
        ('B_derivative', sp.diff(gB, xi)),
        ('kappa_derivative_minus_1000_B_derivative', sp.diff(gk-1000*gB, xi)),
        ('kappa_minus_13_over18', gk-q(13, 18)), ('four_fifths_minus_kappa', q(4, 5)-gk),
        ('negative_p_derivative', -(3564*xi**2-4320*xi+171)),
        ('b', gb), ('ell', gl), ('one_fifth_minus_ell', q(1, 5)-gl),
        ('lx_minus_b_minus_ell', gx-gb-gl), ('ly_minus_ell', gy-gl),
        ('ly_minus_ell_minus_11b_over6', gy-gl-q(11, 6)*gb),
        ('one_minus_h', 1-gh), ('five_ell_minus_h', 5*gl-gh),
        ('B_minus_43_over50', gB-q(43, 50)), ('B_minus_437_over500', gB-q(437, 500)),
        ('seven_eighths_minus_B', q(7, 8)-gB),
        ('lowest_class_saving', -gC0-(q(1, 2)+3*gl/2)/50),
        ('small_norm_saving_with_previous_gap', gy/2-13*gh/75-q(1, 50)-(q(7, 8)-gB)),
        ('intermediate_saving_at_1_over50', mI(q(1, 50))),
        ('intermediate_saving_at_19_over25', mI(q(19, 25))),
        ('c', gc), ('one_minus_c', 1-gc),
        ('inverse_prime_support_margin', q(1, 5)-(4-gc)/(20-4*gc)),
        ('plain_prime_support_margin', q(1, 5)-gc/12),
        ('J_margin_at_19_over25', (q(5, 6)-q(19, 25))*(5-gc)/2+q(19, 25)*(1-gc/4)-q(3, 5)),
        ('D_margin_at_51_over100', 3-(1+gc)*q(51, 100)-2),
        ('P_margin_at_51_over100', (2-gc*q(51, 100))*q(49, 100)-q(3, 4))])
    assert len(reserves) == 29
    bounds.update({name: bernstein_positive(expr, xi) for name, expr in reserves.items()})
    assert all(F(bounds[name]) > F(1, 25000) for name in reserves)
    # Root uniqueness and fixed-point elimination, with no floating roots.
    p = 1188*xi**3-2160*xi**2+171*xi+190
    assert bernstein_positive(-sp.diff(p, xi), xi)
    assert sp.cancel(geo['kappa']-(2*geo['B']-1)+p/(18*(2*xi+1)*(36*xi**2-78*xi+25))) == 0
    assert sp.cancel(geo['B']-boundary(geo['ell'])) == 0
    lhs = (216*kappa-18)*delta**2-(468*kappa-57)*delta+150*kappa-20
    assert sp.cancel(lhs.subs({kappa: geo['kappa'], delta: xi})) == 0
    Rgeo = R.subs({y: 0, delta: xi, **substitution})
    assert sp.cancel(Rgeo-q(2, 3)) == 0
    # The rational Q certificate covers the fixed-kappa algebraic endpoint
    # too: its xi lies in the same interval and kappa(xi)=3/4.
    oldxi = (49-sp.sqrt(921))/48
    assert sp.simplify(geometry(oldxi)['kappa']-q(3, 4)) == 0
    assert sp.simplify(geometry(oldxi)['B']-(1507-2*sp.sqrt(921))/1653) == 0
    original = {b: q(1, 8), ell: q(1, 6), kappa: q(3, 4), alpha: q(5, 6)}
    original_A = sp.Poly(Ap.as_expr().subs(original), y)
    original_discr = sp.Poly(discr.as_expr().subs(original), y)
    assert all(v > 0 for v in original_A.all_coeffs()+original_discr.all_coeffs())
    assert boundary(F(1, 6)) == F(7, 8)
    return {'direct_floor': '13/15', 'direct_dual_weights': list(map(str, weights)),
            'direct_dual_identity_verified': True,
            'uniform_endpoint_discriminant_constant_is_zero': True,
            'endpoint_and_reserve_positive_Bernstein_bounds': bounds,
            'uniform_reserve_inequalities_verified': len(reserves),
            'fixed_point_polynomial': str(p), 'fixed_point_elimination_verified': True,
            'original_seven_eighths_uniform_central_endpoint_verified': True,
            'count_at_critical_class': '2/3',
            'scope': 'Exact scalar identities/positivity only; Liu analytic estimates and Lean formalization not replayed.'}


def bootstrap_intervals(steps=8):
    """Interval ledger for F(2*B_previous-1), never a circular moment call."""
    previous = (F(7, 8), F(7, 8))
    rows = []
    for step in range(steps):
        kl, ku = (2*previous[0]-1, 2*previous[1]-1)
        def root(kappa):
            return isolate_decreasing_root([216*kappa-18, -(468*kappa-57),
                                            150*kappa-20])
        lower, upper = root(kl)[0], root(ku)[1]
        current = (geometry(lower)['B'], geometry(upper)['B'])
        assert current[1] < previous[0]
        rows.append({'step': step+1, 'previous_B_interval': list(map(str, previous)),
                     'moment_kappa_interval_from_previous_bound': [str(kl), str(ku)],
                     'new_B_interval': list(map(str, current)),
                     'new_B_decimal': str(sp.N(sp.Rational(sum(current)/2), 32))})
        previous = current
    return rows


def raw_polynomial(delta, x, detector_length, prime_length=F(0), copies=1):
    """Length/amplitude before L2 normalization; not a transport theorem."""
    n = copies*detector_length+prime_length
    v = copies*detector_length*(1+delta)/2+prime_length*(F(1, 2)+delta*x)
    if n <= 0 or not 0 <= x <= F(1, 2) or prime_length < 0 or type(copies) is not int or copies < 1:
        raise ValueError('positive raw polynomial length required')
    return dict(N_exponent=n, V_exponent=v, sigma=v/n)


def ordinary_gm_template(n, v, height_exponent=F(1)):
    """GM Theorem 1.1 powers in base U; height is an explicit formal input."""
    return max(2*n-2*v, F(18, 5)*n-4*v, height_exponent+F(12, 5)*n-4*v)


def generate():
    certificates = symbolic_certificates()
    lo, hi = isolate_decreasing_root([1188, -2160, 171, 190])
    geo = geometry((lo+hi)/2)
    count = count_closed((lo+hi)/2, F(1, 2), geo['kappa'])
    # Exact minimax independent of the closed formula, near the critical
    # algebraic class, using a rational interior representative.
    delta, kappa = F(388583354266, 10**12), F(749914038840, 10**12)
    closed = count_closed(delta, F(1, 2), kappa)
    inputs = MomentInputs(plain_prime_cost=6*kappa)
    minimax = detector_count_at_t(closed['t'], delta, F(1, 2), inputs)
    assert minimax['R'] == closed['R']
    sensitivity = []
    for name, params in [
        ('published', inputs),
        ('formal_alpha_four_fifths', MomentInputs(alpha=F(4, 5), plain_prime_cost=6*kappa)),
        ('formal_alpha_three_quarters', MomentInputs(alpha=F(3, 4), plain_prime_cost=6*kappa)),
        ('formal_inverse_prime_cost_three_halves', MomentInputs(inverse_prime_cost=F(3, 2), plain_prime_cost=6*kappa)),
        ('formal_plain_prime_cost_five_kappa', MomentInputs(plain_prime_cost=5*kappa))]:
        candidates = [detector_count_at_t(1+F(j, 400), delta, F(1, 2), params) for j in range(201)]
        candidates.append(detector_count_at_t(closed['t'], delta, F(1, 2), params))
        formal_t = count_closed(delta, F(1, 2), params.plain_prime_cost/6, params.alpha)['t']
        candidates.append(detector_count_at_t(formal_t, delta, F(1, 2), params))
        best = min(candidates, key=lambda r: r['R'])
        sensitivity.append(dict(name=name, inputs={k: str(v) for k, v in vars(params).items()},
                                sampled_detector_optimum={k: str(v) for k, v in best.items()},
                                scope='Exact fixed-t minimax; sampled t choices only; no new arithmetic input proved.'))
    # Ordinary Montgomery conjecture is NOT automatically a Hecke-family
    # theorem. Quantities here are only a normalization/transport ledger.
    r, m = count['r'], count['m']
    zM, zS = (1-r)/2, (1-2*m)/(6*geo['kappa'])
    sigma = (1+(lo+hi)/2)/2
    normalization = {'critical_sigma_interval': [str((1+lo)/2), str((1+hi)/2)],
        'inverse_raw_length_exponent': str(r+zM),
        'short_squared_raw_length_exponent': str(2*m+zS),
        'unselected_long_length_exponent': str(count['t']),
        'critical_sigma_below_seven_tenths': (1+hi)/2 < F(7, 10),
        'ordinary_GM_transport_to_Hecke_family_proved': False,
        'CGL_fixed_modulus_and_N_ge_qT_two_thirds_transferred': False,
        'Montgomery_conjecture_is_density_hypothesis_for_this_family': False}
    transport_rows = []
    for name, raw in [('inverse_with_primes', raw_polynomial((lo+hi)/2, F(1, 2), r, zM)),
                      ('short_squared_with_primes', raw_polynomial((lo+hi)/2, F(1, 2), m, zS, 2)),
                      ('unselected_long', raw_polynomial((lo+hi)/2, F(1, 2), count['t']))]:
        n, v = raw['N_exponent'], raw['V_exponent']
        transport_rows.append({'name': name, **{k: str(v) for k, v in raw.items()},
            'GM_template_exponent_if_height_U': str(ordinary_gm_template(n, v)),
            'Montgomery_template_exponent': str(2*n-2*v),
            'transfer_to_Liu_family_proved': False})
    normalization['ordinary_template_ledger_not_a_family_bound'] = transport_rows
    # A count-free exact primal/dual certificate, stronger than choosing a
    # conjectural count function: delete ALL count inequalities.
    primal = direct_components(F(7, 20), F(9, 20), F(1, 5))
    assert primal['B_low'] == F(13, 15)
    assert F(7, 20) > F(1, 5) and F(9, 20) > F(1, 5)
    return {'status': 'exact_scalar_reconstruction_and_count_only_barrier_not_zero_free_theorem',
        'certificates': certificates,
        'regression_values': {'original': '7/8',
            'fixed_kappa': str((1507-2*sp.sqrt(921))/1653),
            'fixed_kappa_decimal': str(sp.N((1507-2*sp.sqrt(921))/1653, 35)),
            'variable_moment_B_interval': [str(geometry(lo)['B']), str(geometry(hi)['B'])],
            'variable_moment_B_decimal': str(sp.N(sp.Rational(geo['B']), 35)),
            'xi_interval': [str(lo), str(hi)]},
        'critical_parameters_rational_representative': {k: str(v) for k, v in geo.items()},
        'critical_count_rational_representative': {k: str(v) for k, v in count.items()},
        'independent_fixed_t_minimax': {k: str(v) for k, v in minimax.items()},
        'formal_moment_sensitivity': sensitivity,
        'normalization_and_transport': normalization,
        'bootstrap_intervals_from_preceding_bound': bootstrap_intervals(),
        'count_constraints_deleted': {'direct_optimum': '13/15',
            'primal_lengths': {'lx': '7/20', 'ly': '9/20', 'ell': '1/5'},
            'primal_direct_components': {k: str(v) for k, v in primal.items()},
            'attained_conditional_zero_free_bound': False,
            'RH_reachable_by_changing_only_count_constraints': False},
        'source': {'url': 'https://arxiv.org/html/2610.12234v2',
            'archive_url': 'https://arxiv.org/src/2610.12234v2',
            'archive_sha256': 'da1db207bb54437245c4fff75f33cfb29088f32f57e6364a6b3b955bc3372204'}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError('refusing to overwrite a research receipt')
    result = generate()
    result['base_commit'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result['sympy_version'] = sp.__version__
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['regression_values']['variable_moment_B_decimal'], 'direct floor 13/15')


if __name__ == '__main__':
    main()
