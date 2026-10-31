"""Localize a conditional input in Liu's comparison; no new arithmetic bound.

The original moment/count is retained outside the certified class box.
Inside it, either a moment on a narrow length band or an explicit direct
class-count improvement suffices. These are two unproved alternatives.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from math import comb
from pathlib import Path

import sympy as sp

from liu_conditional_moment import (ALPHA, B_GAP, BOUNDARY, ELL, KAPPA,
    certificate as full_certificate, endpoint_polynomials)
from liu_exponent_system import bernstein_positive

OLD_ALPHA = F(5, 6)
DELTA_BOX = (F(1, 3), F(47, 100))
X_BOX = (F(21, 50), F(1, 2))
Y_CUT = F(2, 25)
R_BAND = (F(1099, 1000), F(119, 100))
COUNT_GAIN = F(1, 850)


def bernstein_rectangle(expr, variables, intervals):
    """Exact tensor Bernstein certificate for a polynomial on a rectangle."""
    u, v = sp.symbols('bernstein_u bernstein_v')
    (a, b), (c, d) = [tuple(map(sp.Rational, box)) for box in intervals]
    shifted = sp.Poly(sp.expand(expr.subs({variables[0]: a+(b-a)*u,
                                         variables[1]: c+(d-c)*v})), u, v)
    n, m = shifted.degree(u), shifted.degree(v)
    if n < 0 or m < 0:
        raise ArithmeticError('zero polynomial is not a strict certificate')
    coefficients = [sum(shifted.coeff_monomial(u**p*v**q)
                        *sp.Rational(comb(i, p), comb(n, p))
                        *sp.Rational(comb(j, q), comb(m, q))
                        for p in range(i+1) for q in range(j+1))
                    for i in range(n+1) for j in range(m+1)]
    if min(coefficients) <= 0:
        raise ArithmeticError('positive tensor Bernstein certificate failed')
    return dict(degrees=[n, m], coefficients=list(map(F, coefficients)),
                lower_bound=F(min(coefficients)))


def outside_box_certificate():
    """Old count is strictly sufficient outside DELTA_BOX x X_BOX."""
    delta, y, z = sp.symbols('delta y z')
    p = endpoint_polynomials(alpha=OLD_ALPHA)
    A, B, C, discr = [sum(sp.Rational(v)*y**i for i, v in enumerate(p[n]))
                       for n in ('A', 'B', 'C', 'discriminant_complement')]
    left, right = map(sp.Rational, DELTA_BOX)
    Q = A*delta**2+B*delta+C
    # For 0<=y<=.08, Q decreases up to delta=1/3. Thus the left
    # outside region is controlled by its value at that boundary.
    left_derivative = F(bernstein_positive(-(2*A*left+B), y, (F(0), Y_CUT)))
    left_values = sp.Poly(Q.subs(delta, left), y)
    right_derivative = sp.Poly(2*A*right+B, y)
    right_values = sp.Poly(Q.subs(delta, right), y)
    shifted_discr = sp.Poly(sp.expand(discr.subs(y, sp.Rational(Y_CUT)+z)), z)
    if any(v <= 0 for poly in (left_values, right_derivative, right_values, shifted_discr)
           for v in poly.all_coeffs()):
        raise ArithmeticError('outside-box positive coefficients failed')
    Amax = sum(v*F(1, 2)**i for i, v in enumerate(p['A']))
    savings = {
        'delta_at_most_one_third': F(left_values.nth(0))/(6*OLD_ALPHA),
        'delta_at_least_47_over100': F(right_values.nth(0))/(6*OLD_ALPHA),
        'x_at_most_21_over50': F(shifted_discr.nth(0))/(24*OLD_ALPHA*Amax),
    }
    return dict(left_decreasing_derivative_lower_bound=left_derivative,
                left_boundary_Q_coefficients=[F(left_values.nth(i)) for i in range(4)],
                right_increasing_derivative_coefficients=[F(right_derivative.nth(i)) for i in range(4)],
                right_boundary_Q_coefficients=[F(right_values.nth(i)) for i in range(4)],
                shifted_discriminant_coefficients=[F(shifted_discr.nth(i)) for i in range(5)],
                uniform_endpoint_savings=savings,
                minimum_saving=min(savings.values()),
                domain=dict(delta=[F(0), F(19, 25)], x=[F(0), F(1, 2)]))


def length_band_certificate():
    """Only R_BAND needs the stronger moment inside the class box."""
    delta, x = sp.symbols('delta x')
    c, a, old = sp.Rational(2, 3)/sp.Rational(KAPPA), sp.Rational(ALPHA), sp.Rational(OLD_ALPHA)
    D, P = 3-(1+c)*x, (2-c*x)*(1-x)
    J = (a-delta)*D+delta*P
    R = 1-delta+(a-delta)*delta*P/(2*J)
    rlo, rhi = map(sp.Rational, R_BAND)
    old_at_rlo = 1-old+(old-delta)*rlo
    expressions = {
        'old_count_at_rlo_below_R_new': sp.cancel(2*J*(R-old_at_rlo)),
        'cutoff_above_rlo': delta*P-(rlo-1)*2*J,
        'cutoff_below_rhi': (rhi-1)*2*J-delta*P,
    }
    checks = {name: bernstein_rectangle(expr, (delta, x), (DELTA_BOX, X_BOX))
              for name, expr in expressions.items()}
    # J<=3alpha on this box; dividing by 2J preserves explicit margins.
    return dict(numerator_certificates=checks,
                margin_lower_bounds={name: row['lower_bound']/(6*ALPHA)
                                     for name, row in checks.items()},
                old_long_count_increasing_slope=OLD_ALPHA-DELTA_BOX[1],
                new_long_count_increasing_slope=ALPHA-DELTA_BOX[1],
                required_long_length_band=list(R_BAND),
                arithmetic_moment_proved=False)


def hybrid_detector_count(t, delta, x):
    """Independent affine supremum with the improved moment ONLY in R_BAND.

    For this local box t lies in (1.1,1.19), so all used short selected
    lengths are below .2; the second inverse restriction is redundant.
    Outside the band, even inside the class box, the old moment is used.
    """
    if not F(11, 10) <= t <= R_BAND[1] or not DELTA_BOX[0] <= delta <= DELTA_BOX[1] or not X_BOX[0] <= x <= X_BOX[1]:
        raise ValueError('local class and cutoff box required')
    left, right = t-F(1, 2), t
    cuts = sorted({left, right} | {p for p in (F(1), *R_BAND) if left < p < right})
    result = F(-10)
    for a, b in zip(cuts[:-1], cuts[1:]):
        mid = (a+b)/2
        if mid < 1:
            inv = (1-delta*x, -delta*(1-x))
            plain = (1-2*delta*t-delta*x*(1-2*t)/(3*KAPPA),
                     2*delta-2*delta*x/(3*KAPPA))
        else:
            alpha = ALPHA if R_BAND[0] <= mid <= R_BAND[1] else OLD_ALPHA
            inv = (1-alpha, alpha-delta)
            plain = (1-2*delta*t, 2*delta)  # Unselected fourth moment suffices.
        candidates = {a, b}
        if inv[1] != plain[1]:
            crossing = (plain[0]-inv[0])/(inv[1]-plain[1])
            if a <= crossing <= b:
                candidates.add(crossing)
        result = max(result, *(min(inv[0]+inv[1]*r, plain[0]+plain[1]*r)
                               for r in candidates))
    return result


def direct_count_certificate(gain=COUNT_GAIN):
    """Alternative hypothesis #class << U^(R_old-gain+epsilon)."""
    if not 0 < gain < 1-DELTA_BOX[1]:
        raise ValueError('positive gain preserving a nonnegative count exponent required')
    delta, y = sp.symbols('delta y')
    c, alpha = sp.Rational(2, 3)/sp.Rational(KAPPA), sp.Rational(OLD_ALPHA)
    D, P = (5-c)/2+(1+c)*y, 1-c/4+2*y+c*y**2
    J = (alpha-delta)*D+delta*P
    h = (1+B_GAP+3*ELL)/2
    old = endpoint_polynomials(alpha=OLD_ALPHA)
    A, B, C = [sum(sp.Rational(v)*y**i for i, v in enumerate(old[n])) for n in ('A', 'B', 'C')]
    modified = sp.Poly(sp.expand(A*delta**2+B*delta+C+2*J*sp.Rational(h*gain)), delta)
    A, B, C = (modified.nth(i) for i in (2, 1, 0))
    discr = sp.Poly(sp.expand(4*A*C-B**2), y)
    if min(discr.all_coeffs()) <= 0:
        raise ArithmeticError('the proposed additive count gain does not certify the endpoint')
    Amax = sum(v*F(1, 2)**i for i, v in enumerate(old['A']))
    return dict(additive_count_gain=gain,
                discriminant_coefficients=[F(discr.nth(i)) for i in range(5)],
                uniform_endpoint_saving=F(discr.nth(0))/(24*OLD_ALPHA*Amax),
                local_d_slope_lower_bound=F(33, 50)-DELTA_BOX[1]/2-gain,
                at_R_old_two_thirds_new_exponent=F(2, 3)-gain,
                arithmetic_class_count_proved=False)


def certificate():
    outside = outside_box_certificate()
    full = full_certificate()
    return dict(
        scope='Conditional scalar localization only; neither localized arithmetic alternative is proved.',
        B=BOUNDARY, kappa=KAPPA, class_box=dict(delta=list(DELTA_BOX), x=list(X_BOX)),
        outside_box_uses_original_count=outside,
        localized_moment_option=length_band_certificate(),
        localized_moment_total_endpoint_saving=min(outside['minimum_saving'], full['uniform_endpoint_saving_lower_bound']),
        alternative_direct_class_count=direct_count_certificate(),
        unchanged_auxiliary_reserve_count=len(full['auxiliary_reserves']),
        globally_minimal_box_claimed=False,
        arithmetic_estimate_proved=False, DH_family_instantiated=False,
        external_Lean_rebuilt=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = certificate()
    data = json.dumps(result, default=str, indent=2)+'\n'
    if args.output:
        with args.output.open('x') as f:
            f.write(data)
    else:
        print(data, end='')


if __name__ == '__main__':
    main()
