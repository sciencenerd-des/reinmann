"""Conditional scalar certificate for a stronger Liu long inverse moment.

No arithmetic moment is proved here. All inequalities are exact rationals;
the hypothetical long moment and the existing analytic assembly are inputs.
Phase-1 code and immutable receipts are deliberately left unchanged.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import sympy as sp

from liu_exponent_system import direct_components, nonprincipal

ALPHA = F(4, 5)
KAPPA = F(3, 4)  # Supplied by the preceding 7/8 bound, not the desired bound.
ELL = F(125621, 750000)
B_GAP = F(55363, 500000)
BOUNDARY = F(874793, 1000000)
DELTA_MAX = F(19, 25)  # Actual classes <=3/4 plus a fixed rounding margin.
X_ROUND_MAX = F(51, 100)


def endpoint_polynomials(alpha=ALPHA, kappa=KAPPA, ell=ELL, b=B_GAP):
    """Derive Q=-2JE; return its coefficient lists in increasing powers."""
    delta, y = sp.symbols('delta y')
    a, k, l, gap = map(sp.Rational, (alpha, kappa, ell, b))
    c = sp.Rational(2, 3)/k
    D = (5-c)/2+(1+c)*y
    P = 1-c/4+2*y+c*y**2
    J = (a-delta)*D+delta*P
    h, C0 = (1+gap+3*l)/2, -sp.Rational(1, 4)+gap/6+5*l/4
    R = 1-delta+(a-delta)*delta*P/(2*J)
    E = C0+(sp.Rational(1, 2)+l)*delta+l*(sp.Rational(1, 2)-y)*delta-h*(1-R)
    Q = -2*C0*J+(gap+2*l*y)*delta*J-h*(a-delta)*delta*P
    if sp.cancel(Q+2*J*E) != 0:
        raise ArithmeticError('endpoint identity failed')
    poly = sp.Poly(sp.expand(Q), delta)
    A, B, C = (sp.Poly(poly.nth(i), y) for i in (2, 1, 0))
    discr = sp.Poly(sp.expand(4*A.as_expr()*C.as_expr()-B.as_expr()**2), y)
    # Completing the square is the uniform certificate, not a class grid.
    if sp.expand(4*A.as_expr()*Q-(2*A.as_expr()*delta+B.as_expr())**2-discr.as_expr()) != 0:
        raise ArithmeticError('completion-of-square identity failed')
    return {name: [F(p.nth(i)) for i in range(p.degree()+1)]
            for name, p in (('A', A), ('B', B), ('C', C), ('discriminant_complement', discr))}


def count_identities():
    """General alpha balancing, with unchanged short moments."""
    delta, x, alpha, c, t, r = sp.symbols('delta x alpha c t r')
    D, P = 3-(1+c)*x, (2-c*x)*(1-x)
    J = (alpha-delta)*D+delta*P
    cutoff = 1+delta*P/(2*J)
    crossing = ((2-c*x)*t+(c/2-1)*x)/D
    FI, FS = x+(1-x)*r, 2*(t-r)+c*x*(1-2*(t-r))/2
    short = 1-delta+delta*P*(sp.Rational(3, 2)-t)/D
    long = 1-alpha+(alpha-delta)*t
    R = 1-delta+(alpha-delta)*delta*P/(2*J)
    identities = {
        'short_moment_crossing': (FI-FS).subs(r, crossing),
        'short_count_at_crossing': (1-delta*FI).subs(r, crossing)-short,
        'short_count_at_cutoff': short.subs(t, cutoff)-R,
        'long_count_at_cutoff': long.subs(t, cutoff)-R,
        'cutoff_upper_margin': sp.Rational(3, 2)-cutoff-(alpha-delta)*D/(2*J),
        'D_minus_P': D-P-(1+x-c*x*x),
        'crossing_at_three_halves': crossing.subs(t, sp.Rational(3, 2))-1,
        'crossing_t_derivative': sp.diff(crossing, t)-(2-c*x)/D,
        'crossing_x_derivative': sp.diff(crossing, x)-(2-c)*(2*t-3)/(2*D**2),
        'second_inverse_support_gap': 3-2*r-8*(1-r)/2-(2*r-1),
    }
    if any(sp.cancel(v) != 0 for v in identities.values()):
        raise ArithmeticError('general-alpha count identity failed')
    return list(identities)


def reserve_values(alpha=ALPHA, kappa=KAPPA, ell=ELL, b=B_GAP):
    """Relevant fixed-parameter reserves from Liu 31-32, not 29 derivatives.

    xi/kappa derivative tests in the original iteration are inapplicable:
    kappa is fixed here. The denominator and cutoff bounds use the enlarged
    rounding box and the new alpha, rather than assuming the old constants.
    """
    lx, ly = (1-b-ell)/2, (1+b-ell)/2
    h, B = 1-lx+ell, F(11, 12)-ell/4
    c, C0 = F(2, 3)/kappa, -F(1, 4)+b/6+5*ell/4
    mI = lambda delta: -((225*ell+50-75*b)*delta+78*ell-49*b-73)/300
    return {
        'kappa_minus_13_over18': kappa-F(13, 18),
        'four_fifths_minus_kappa': F(4, 5)-kappa,
        'alpha_minus_delta_max': alpha-DELTA_MAX,
        'b': b, 'ell': ell, 'one_fifth_minus_ell': F(1, 5)-ell,
        'lx_minus_b_minus_ell': lx-b-ell,
        'ly_minus_ell': ly-ell,
        'ly_minus_ell_minus_11b_over6': ly-ell-F(11, 6)*b,
        'one_minus_h': 1-h, 'five_ell_minus_h': 5*ell-h,
        'B_minus_43_over50': B-F(43, 50),
        'B_minus_437_over500': B-F(437, 500),
        'seven_eighths_minus_B': F(7, 8)-B,
        'lowest_class_saving': -C0-(F(1, 2)+3*ell/2)/50,
        'small_norm_saving_with_previous_gap': ly/2-13*h/75-F(1, 50)-(F(7, 8)-B),
        'intermediate_saving_at_1_over50': mI(F(1, 50)),
        'intermediate_saving_at_19_over25': mI(DELTA_MAX),
        'c': c, 'one_minus_c': 1-c,
        'inverse_prime_support_margin': F(1, 5)-(4-c)/(20-4*c),
        'plain_prime_support_margin': F(1, 5)-c/12,
        # D decreases and P decreases in x on [0,.51]; D>2, P>3/4.
        'D_margin_at_round_max': 3-(1+c)*X_ROUND_MAX-2,
        'P_margin_at_round_max': (2-c*X_ROUND_MAX)*(1-X_ROUND_MAX)-F(3, 4),
        'J_uniform_margin_over_three_fifths': 2*alpha-F(5, 4)*DELTA_MAX-F(3, 5),
        'cutoff_margin_below_three_halves': (alpha-DELTA_MAX)/(2*alpha),
        'endpoint_d_slope_lower': F(33, 50)-DELTA_MAX/2,
        'endpoint_d_slope_upper_margin_below_two': 2-(F(33, 50)+DELTA_MAX/2),
        'intermediate_d_slope_lower': F(101, 150)-DELTA_MAX/6,
        'inverse_crossing_second_support_gap': 1/(5-c),
    }


def certificate(alpha=ALPHA, kappa=KAPPA, ell=ELL, b=B_GAP):
    if not DELTA_MAX < alpha <= 1 or kappa != KAPPA:
        raise ValueError('fixed antecedent and rounded count domain required')
    polys = endpoint_polynomials(alpha, kappa, ell, b)
    if min(polys['A']+polys['discriminant_complement']) <= 0:
        raise ArithmeticError('uniform positive-coefficient certificate failed')
    reserves = reserve_values(alpha, kappa, ell, b)
    if min(reserves.values()) <= 0:
        raise ArithmeticError('an auxiliary range/support reserve failed')
    lx, ly = (1-b-ell)/2, (1+b-ell)/2
    h, B = 1-lx+ell, F(11, 12)-ell/4
    direct = direct_components(lx, ly, ell)
    if direct['B_low'] != B or direct['reflection_k'] != 0:
        raise ArithmeticError('full direct majorant differs from balanced boundary')
    # A(y)<=Amax for y in [0,1/2], J<=alpha*D<=3alpha.
    # Q>=(4AC-Bq^2)/(4A)>=d0/(4Amax), so -E>=d0/(24alpha*Amax).
    Amax = sum(v*F(1, 2)**i for i, v in enumerate(polys['A']))
    saving = polys['discriminant_complement'][0]/(24*alpha*Amax)
    if saving <= 0:
        raise ArithmeticError('strict endpoint saving failed')
    # Independent relative-exponent formula must agree for every class and
    # central contour coordinate; this is an identity, not a point check.
    delta, x, R, z0 = sp.symbols('delta x R z0')
    E = -F(1, 4)+b/6+5*ell/4+(F(1, 2)+ell)*delta+ell*x*delta-h*(1-R)
    if sp.cancel(nonprincipal(lx, ly, ell, B, delta, x, h, R, z0)-E) != 0:
        raise ArithmeticError('relative exponent normalization failed')
    return {
        'scope': 'Conditional scalar certificate only; no new arithmetic estimate or zero-free theorem.',
        'hypothetical_long_inverse_moment': {
            'alpha': alpha, 'U_exponent': 1-alpha, 'D_exponent': alpha,
            'r_range': [F(1), F(3, 2)],
            'saving_against_original': '(D/U)^(1/30)' if alpha == ALPHA else None,
            'proved': False, 'DH_family_instantiated': False},
        'parameters': dict(alpha=alpha, kappa=kappa, ell=ell, b=b, lx=lx, ly=ly, h=h, B=B),
        'prior_bound_justifying_kappa': F(7, 8),
        'endpoint_domain': dict(delta=[F(0), alpha], x=[F(0), F(1, 2)]),
        'count_denominator_rounding_box': dict(delta=[F(0), DELTA_MAX], x=[F(0), X_ROUND_MAX]),
        'endpoint_polynomials_in_y': polys,
        'uniform_endpoint_saving_lower_bound': saving,
        'general_alpha_count_identities': count_identities(),
        'auxiliary_reserves': reserves,
        'full_direct_majorant': direct,
        'all_scalar_checks_passed': True,
        'arithmetic_estimate_proved': False,
        'analytic_assembly_reproved': False,
        'external_Lean_rebuilt': False,
    }


def critical_class():
    """Exact algebraic tangency for alpha=4/5,kappa=3/4 (not a theorem)."""
    xi = (475-sp.sqrt(83545))/480
    ell = (5-6*xi)/(9+18*xi)
    d, b = sp.symbols('delta b')
    c, a = sp.Rational(8, 9), sp.Rational(4, 5)
    D, P = (5-c)/2, 1-c/4
    J = (a-d)*D+d*P
    R = 1-d+(a-d)*d*P/(2*J)
    if sp.cancel(R-sp.Rational(2, 3)+(240*d*d-475*d+148)/(3*(115*d-148))) != 0:
        raise ArithmeticError('critical class polynomial failed')
    if sp.simplify(240*xi**2-475*xi+148) != 0:
        raise ArithmeticError('critical root failed')
    h, C0 = (1+b+3*ell)/2, -sp.Rational(1, 4)+b/6+5*ell/4
    E = C0+(sp.Rational(1, 2)+3*ell/2)*d-h*(1-R)
    tangency_b = sp.solve(sp.diff(E, d).subs(d, xi), b)[0]
    if sp.simplify(E.subs({d: xi, b: tangency_b})) != 0:
        raise ArithmeticError('critical tangency failed')
    return {name: str(v.evalf(40)) for name, v in (
        ('delta_display', xi), ('ell_display', ell), ('b_display', tangency_b),
        ('B_tangency_display', sp.Rational(11, 12)-ell/4),
        ('t_display', (1+d*P/(2*J)).subs(d, xi)))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = certificate()
    result['critical_class_algebraic_diagnostic'] = critical_class()
    data = json.dumps(result, default=str, indent=2)+'\n'
    if args.output:
        if args.output.exists():
            raise FileExistsError('refusing to overwrite a receipt')
        args.output.write_text(data)
    else:
        print(data, end='')


if __name__ == '__main__':
    main()
