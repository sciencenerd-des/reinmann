"""Conditional band-only H(4/5) pricing in the refined numerator ledger.

The arithmetic moment is unproved. This certificate retains the printed
auxiliary conditions and does not claim the best conditional boundary.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import sympy as sp

from liu_exponent_system import bernstein_positive, count_closed, direct_components
from liu_localized_target import bernstein_rectangle

Q = sp.Rational
KAPPA = F(3, 4)
ALPHA = F(4, 5)
OLD = F(5, 6)
B_TARGET = F(34993, 40000)
ELL = F(5021, 30000)
B_GAP = F(17, 200)
DELTA_BOX = (F(21, 50), F(51, 100))
X_BOX = (F(21, 50), F(1, 2))
R_BAND = (F(1099, 1000), F(119, 100))
Y_CUT = F(2, 25)


def expressions(alpha):
    d, y = sp.symbols('delta y')
    x = Q(1, 2)-y
    k, b, ell, a = map(Q, (KAPPA, B_GAP, ELL, alpha))
    c = 1/(3*k)
    lx, ly, h = (1-b-ell)/2, (1+b-ell)/2, (1+b+3*ell)/2
    D, P = 3-(1+2*c)*x, (2-2*c*x)*(1-x)
    J = (a-d)*D+d*P
    R = 1-d+(a-d)*d*P/(2*J)
    t = 1+d*P/(2*J)
    C0 = -Q(1, 4)+b/6+5*ell/4
    E = C0+d/2+d*x*(ell+c*(h/4-ly/2))-3*h*(1-R)/4
    poly = sp.Poly(sp.cancel(-2*J*E), d)
    A, B, C = [sp.Poly(poly.nth(i), y) for i in (2, 1, 0)]
    discr = sp.Poly(4*A.as_expr()*C.as_expr()-B.as_expr()**2, y)
    return dict(delta=d, y=y, x=x, D=D, P=P, J=J, R=R, t=t, E=E,
                C0=C0, lx=lx, ly=ly, h=h, poly=poly, A=A, B=B, C=C, discr=discr)


def outside_certificate():
    e = expressions(OLD)
    d, y = e['delta'], e['y']
    A, B = e['A'], e['B']
    left, right = map(Q, DELTA_BOX)
    derivative = bernstein_positive(-(2*A.as_expr()*left+B.as_expr()), y, (F(0), Y_CUT))
    left_Q = sp.Poly(e['poly'].as_expr().subs(d, left), y)
    right_Q = sp.Poly(e['poly'].as_expr().subs(d, right), y)
    right_derivative = sp.Poly(2*A.as_expr()*right+B.as_expr(), y)
    z = sp.Symbol('z')
    shifted_discr = sp.Poly(e['discr'].as_expr().subs(y, Q(Y_CUT)+z), z)
    assert all(c > 0 for p in [A, left_Q, right_Q, right_derivative, shifted_discr]
               for c in p.all_coeffs())
    Amax = A.eval(Q(1, 2))
    savings = dict(left=left_Q.nth(0)/(6*Q(OLD)),
                   right=right_Q.nth(0)/(6*Q(OLD)),
                   side=shifted_discr.nth(0)/(24*Q(OLD)*Amax))
    assert all(v > 0 for v in savings.values())
    return dict(unchanged_old_count_outside_class_box=True,
                delta_box=list(map(str, DELTA_BOX)), x_box=list(map(str, X_BOX)),
                left_derivative_bound=derivative,
                uniform_savings={k: str(v) for k, v in savings.items()})


def local_certificate():
    e = expressions(ALPHA)
    d, y = e['delta'], e['y']
    assert all(c > 0 for p in [e['A'], e['discr']] for c in p.all_coeffs())
    anew = e['A'].eval(Q(1, 2))
    balanced_saving = e['discr'].nth(0)/(24*Q(ALPHA)*anew)
    # At t=min(t_alpha,r_hi), the hybrid count is bounded by the maximum
    # of R_alpha, R_short(r_hi), and the old long branch at r_lo.
    Rcap = 1-d+d*e['P']*(Q(3, 2)-Q(R_BAND[1]))/e['D']
    Rleft = 1-Q(OLD)+(Q(OLD)-d)*Q(R_BAND[0])
    Ewith = lambda R: e['E']+3*e['h']*(R-e['R'])/4
    x = sp.Symbol('x')
    substitutions = {y: Q(1, 2)-x}
    polynomials = {
        'capped_short': sp.cancel(-e['D']*Ewith(Rcap)),
        'old_long_below_band': sp.cancel(-Ewith(Rleft)),
        'cutoff_above_band_start': sp.cancel(d*e['P']-(Q(R_BAND[0])-1)*2*e['J']),
    }
    proofs = {name: bernstein_rectangle(sp.expand(p.subs(substitutions)),
                                       (d, x), (DELTA_BOX, X_BOX))
              for name, p in polynomials.items()}
    margins = dict(balanced=balanced_saving,
                   capped_short=Q(proofs['capped_short']['lower_bound'])/3,
                   old_long_below_band=Q(proofs['old_long_below_band']['lower_bound']))
    assert all(v > 0 for v in margins.values())
    return dict(count_upper_envelope='max{R_alpha, R_short(119/100), R_old_long(1099/1000)}',
                chosen_cutoff='min(t_alpha,119/100)',
                upper_length_band_enforced=True,
                new_moment_used_only_in_band=list(map(str, R_BAND)),
                positive_discriminant_coefficients=[str(e['discr'].nth(i)) for i in range(5)],
                uniform_savings={k: str(v) for k, v in margins.items()},
                tensor_Bernstein_bounds={k: str(v['lower_bound']) for k, v in proofs.items()})


def hybrid_detector(t, delta, x):
    """Independent affine-cell bound; old moment outside the declared band."""
    if not (DELTA_BOX[0] <= delta <= DELTA_BOX[1] and X_BOX[0] <= x <= X_BOX[1]
            and R_BAND[0] <= t <= R_BAND[1]):
        raise ValueError('localized class and capped cutoff required')
    left, right = t-F(1, 2), t
    cuts = sorted({left, right} | {v for v in [F(1), *R_BAND] if left < v < right})
    best = F(-100)
    for l, r in zip(cuts[:-1], cuts[1:]):
        mid = (l+r)/2
        if mid < 1:
            inv = (1-delta*x, -delta*(1-x))
            plain = (1-2*delta*t-delta*x*(1-2*t)/(3*KAPPA),
                     2*delta-2*delta*x/(3*KAPPA))
        else:
            alpha = ALPHA if R_BAND[0] <= mid <= R_BAND[1] else OLD
            inv = (1-alpha, alpha-delta)
            plain = (1-2*delta*t, 2*delta)
        points = {l, r}
        if inv[1] != plain[1]:
            cross = (plain[0]-inv[0])/(inv[1]-plain[1])
            if l <= cross <= r:
                points.add(cross)
        best = max(best, *(min(inv[0]+inv[1]*v, plain[0]+plain[1]*v) for v in points))
    return best


def auxiliary_reserves():
    b, ell, k = B_GAP, ELL, KAPPA
    lx, ly, h = (1-b-ell)/2, (1+b-ell)/2, (1+b+3*ell)/2
    C0 = -F(1, 4)+b/6+5*ell/4
    Asm = F(1, 2)+ell/2*(F(1, 2)+2*ell/h)-h/2
    reserves = dict(b=b, ell_lower=ell-F(1, 6), ell_upper=F(1, 5)-ell,
                    lx_support=lx-ell, gram_geometry=ly-ell-11*b/6,
                    principal_region=B_TARGET-F(437, 500),
                    prime_numerator=6*k*ell-F(3, 4),
                    prime_supply_lower=ell/h-F(21, 100),
                    prime_supply_upper=1/(6*k)-ell/h,
                    numerator_geometry=ly-h/2, ly_upper=F(1, 2)-ly,
                    small_C0=-F(1, 250)-C0,
                    small_endpoint=-F(1, 250)-C0-Asm/8,
                    detector_floor=-F(1, 100)-C0-(F(1, 2)+3*ell/2)/50,
                    small_rows=-F(1, 20)-(13*h/75-ly/2+F(1, 50)),
                    conditional_slope=ALPHA-DELTA_BOX[1])
    assert F(11, 12)-ell/4 == B_TARGET
    assert F(13, 18) < k <= F(3, 4) and k >= F(29991, 40000)
    assert direct_components(lx, ly, ell)['B_low'] == B_TARGET
    assert min(reserves.values()) > 0
    return reserves


def certificate():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    outside, local, reserves = outside_certificate(), local_certificate(), auxiliary_reserves()
    saving = min(F(v) for r in [outside, local] for v in r['uniform_savings'].values())
    h = (1+B_GAP+3*ELL)/2
    zeta = min(saving/8, F(1, 10**7), (100*ELL/21-h)/2)
    retained = (saving-2*zeta)/2
    assert 0 < 2*zeta < F(1, 1000) and ELL/(h+zeta) > F(21, 100)
    assert 0 < retained < F(1, 1000) and saving-2*zeta > retained
    assert B_TARGET < F('0.874886647039964')
    # The conservative certificate is intentionally not a claim to beat the
    # older conditional pointwise certificate, which has different gates.
    assert B_TARGET > F(874793, 1000000)
    return dict(conditional_B=str(B_TARGET), conditional_B_decimal='0.874825',
                parameters=dict(kappa=str(KAPPA), b=str(B_GAP), ell=str(ELL)),
                antecedent='previous 7/8 bound licenses kappa=3/4',
                moment_hypothesis='ideal-Mobius H(4/5) only on r in [1099/1000,119/100]',
                moment_gain='(D/U)^(1/30)',
                outside=outside, local=local,
                strict_auxiliary_reserves={k: str(v) for k, v in reserves.items()},
                row_extension=str(zeta), retained_margin=str(retained),
                improves_B_flat=True, improves_older_conditional_B_0_874793=False,
                optimized_or_minimal_claim=False, arithmetic_moment_proved=False,
                analytic_assembly_reproved=False, DH_family_instantiated=False,
                RH_claim=False, novelty_claim=False)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    text = json.dumps(certificate(), indent=2)+'\n'
    if args.output:
        with args.output.open('x') as f:
            f.write(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
