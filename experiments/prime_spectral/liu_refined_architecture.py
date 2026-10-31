"""Exact scalar audit of Xu--Sang/Liu's refined comparison.

No analytic estimates or external optimality theorem are reproved here.
The direct-only relaxation deletes ALL high-side and assembly constraints.
Its minimum is a lower bound, not an attained optimum of an idealized full
analytic system. The retained Gram/reflection inputs are part of its scope.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import sympy as sp

from liu_exponent_system import (bernstein_positive, boundary, count_closed,
                                 direct_components)

Q = sp.Rational
STAGES = (
    (F(3, 4), F(173, 2000), F(10027, 60000), F(1, 10**6)),
    (F(29991, 40000), F(17307, 200000), F(1253399, 7500000), F(1, 10**7)),
    (F(3748867, 5000000), F(1081687, 12500000), F(501360233, 3000000000), F(0)),
    (F(1499546589, 2000000000), F(1081687, 12500000),
     F(125340058877, 750000000000), F(0)),
)


def geometry(b, ell):
    return ((1-b-ell)/2, (1+b-ell)/2, (1+b+3*ell)/2)


def refined_endpoint(b, ell, kappa, delta, x):
    """Liu (14.8), using c=1/(3*kappa), not the old ledger's 2/(3*kappa)."""
    lx, ly, h = geometry(b, ell)
    c = 1/(3*kappa)
    D, P = 3-(1+2*c)*x, (2-2*c*x)*(1-x)
    J = (Q(5, 6)-delta)*D+delta*P
    R = 1-delta+(Q(5, 6)-delta)*delta*P/(2*J)
    C0 = -Q(1, 4)+b/6+5*ell/4
    E = C0+delta/2+delta*x*(ell+c*(h/4-ly/2))-3*h*(1-R)/4
    return dict(E=E, J=J, R=R, D=D, P=P, lx=lx, ly=ly, h=h, C0=C0)


def endpoint_certificate(stage):
    """Regenerate the polynomial certificate, rather than trusting tables."""
    kappa, b, ell, margin = map(Q, stage)
    delta, y = sp.symbols('delta y')
    e = refined_endpoint(b, ell, kappa, delta, Q(1, 2)-y)
    poly = sp.Poly(sp.cancel(2*e['J']*(-e['E']-margin)), delta)
    assert poly.degree() == 2
    A, B, C = [sp.Poly(poly.nth(i), y) for i in (2, 1, 0)]
    discr = sp.Poly(4*A.as_expr()*C.as_expr()-B.as_expr()**2, y)
    assert all(v > 0 for v in A.all_coeffs()+discr.all_coeffs())
    # D>0 and P>0 on x in [0,1/2], kappa>=13/18.
    # J=(5/6-delta)D+delta P is positive throughout the closed rectangle.
    assert kappa >= Q(13, 18)
    assert e['D'].subs(y, 0) > 0
    assert 2-1/(3*kappa) > 0
    lx, ly, h, C0 = (e[n] for n in ('lx', 'ly', 'h', 'C0'))
    Asm = Q(1, 2)+(ell/2)*(Q(1, 2)+2*ell/h)-h/2
    reserves = {
        'b': b, 'ell_lower': ell-Q(1, 6), 'ell_upper': Q(1, 5)-ell,
        'kappa_lower': kappa-Q(7497, 10000),
        'principal_region': Q(boundary(F(ell)))-Q(437, 500),
        'lx_minus_ell': lx-ell, 'gram_geometry': ly-ell-11*b/6,
        'moment_supply': 6*kappa*ell-Q(3, 4),
        'supply_upper': 1/(6*kappa)-ell/h,
        'supply_lower': ell/h-Q(21, 100),
        'ly_minus_half_h': ly-h/2, 'half_minus_ly': Q(1, 2)-ly,
        'small_delta_C0': -Q(1, 250)-C0,
        'small_delta_endpoint': -Q(1, 250)-C0-Asm/8,
        'detector_floor': -Q(1, 100)-C0-(Q(1, 2)+3*ell/2)/50,
        'small_rows': -Q(1, 20)-(13*h/75-ly/2+Q(1, 50)),
    }
    assert kappa <= Q(3, 4) and all(v > 0 for v in reserves.values())
    # A positive constant of 4AC-B^2 gives an explicit uniform margin,
    # including stages 2 and 3 where the source prescribes margin=0.
    Amax = A.eval(Q(1, 2))
    # D<=3, P<=2, hence J<=3*(5/6-delta)+2*delta<=5/2.
    extra_margin = discr.nth(0)/(20*Amax)
    assert extra_margin > 0
    zeta = min(extra_margin/8, Q(1, 10**6), (100*ell/21-h)/2)
    assert 0 < 2*zeta < Q(1, 1000)
    assert ell/(h+zeta) > Q(21, 100)
    assert margin+extra_margin-2*zeta > extra_margin/2 > 0
    coeffs = lambda p: [str(p.nth(i)) for i in range(p.degree()+1)]
    return dict(kappa=str(kappa), b=str(b), ell=str(ell),
                B=str(boundary(F(ell))), licensed_by_B=str((1+kappa)/2),
                prescribed_margin=str(margin),
                additional_uniform_margin=str(extra_margin),
                constructed_row_extension=str(zeta),
                retained_uniform_margin=str(margin+extra_margin-2*zeta),
                A=coeffs(A), B_polynomial=coeffs(B), C=coeffs(C),
                discriminant_complement=coeffs(discr),
                strict_scalar_reserves={k: str(v) for k, v in reserves.items()})


def direct_relaxation_certificate():
    """Exact dual and feasible primal for a superset of the refined system."""
    M, ell, b = sp.symbols('M ell b', real=True)
    # Gram>=b/12 and k>=each of these branches give three affine bounds.
    L0 = Q(5, 6)+M/12-ell/6
    branches = (L0, L0+(1+3*ell-2*M)/8, L0+(M+ell-1)/2)
    weights = (Q(17, 30), Q(2, 5), Q(1, 30))
    assert sum(weights) == 1 and all(w > 0 for w in weights)
    assert sp.expand(sum(w*v for w, v in zip(weights, branches))) == Q(13, 15)
    lx, ly, le = F(7, 20), F(9, 20), F(1, 5)
    primal = direct_components(lx, ly, le)
    assert primal['B_low'] == F(13, 15)
    assert lx > le and ly-le > 11*(ly-lx)/6
    # Independently, the balanced system's explicit length cap gives this.
    assert sp.expand(Q(11, 12)-ell/4-Q(13, 15)-(Q(1, 5)-ell)/4) == 0
    # Even extending balanced ell beyond 1/5 retains the reflection penalty:
    # B_low >= B(ell)+(5ell-1)_+/8. Its right-hand slope is 3/8>0.
    assert sp.expand(Q(11, 12)-ell/4+(5*ell-1)/8-Q(13, 15)
                     -Q(3, 8)*(ell-Q(1, 5))) == 0
    return dict(floor='13/15', RH_gap='11/30',
                exact_optimum_of='direct-only relaxation, not the full idealized analytic system',
                high_side_constraints='all deleted, not R=0 or any asserted moment theorem',
                retained_inputs='full direct Gram/reflection majorant and original principal signal normalization',
                dual_weights=list(map(str, weights)), dual_branches=list(map(str, branches)),
                primal=dict(lx=str(lx), ly=str(ly), ell=str(le),
                            **{k: str(v) for k, v in primal.items()}),
                balanced_identity='B(ell)-13/15=(1/5-ell)/4',
                extended_balanced_right_slope='3/8',
                full_idealized_system_exact_optimum=None)


def fixed_point_regression():
    """Derive the quartic from the critical class; not its full optimality proof."""
    delta, kappa, b, ell, B = sp.symbols('delta kappa b ell B')
    e = refined_endpoint(b, ell, kappa, delta, Q(1, 2))
    cr = ((3-324*kappa**2)*delta**2
          +(756*kappa**2-54*kappa-5)*delta+40*kappa-300*kappa**2)
    derivative = cr/(24*kappa*(54*delta*kappa-6*delta-75*kappa+10))
    assert sp.cancel(sp.diff(e['E'], b)-derivative) == 0
    assert sp.cancel(54*delta*kappa-6*delta-75*kappa+10+36*kappa*e['J']) == 0
    # At the fixed point ell=4*(11/12-(1+kappa)/2)=5/3-2*kappa.
    fixed_E = sp.fraction(sp.cancel(e['E'].subs({b: 0, ell: Q(5, 3)-2*kappa})))[0]
    resultant = sp.factor(sp.resultant(cr, fixed_E, delta))
    quartic = 16686*kappa**4-27405*kappa**3+9936*kappa**2+1290*kappa-275
    assert sp.rem(sp.Poly(resultant, kappa), sp.Poly(quartic, kappa)).is_zero
    Bquartic = 133488*B**4-376596*B**3+384534*B**2-167541*B+26231
    assert sp.expand(quartic.subs(kappa, 2*B-1)-2*Bquartic) == 0
    blo, bhi = Q('0.874886647039964'), Q('0.8748866470399645')
    poly = sp.Poly(Bquartic, B)
    assert poly.count_roots(blo, bhi) == 1
    assert poly.eval(blo)*poly.eval(bhi) < 0
    for _ in range(160):
        mid = (blo+bhi)/2
        if poly.eval(blo)*poly.eval(mid) < 0:
            bhi = mid
        else:
            blo = mid
    assert Q('0.749773294079928') < 2*blo-1 < 2*bhi-1 < Q('0.749773294079929')
    # Select the critical delta on this root, rather than accepting any root
    # introduced by elimination. The penultimate subresultant is linear.
    linear = sp.Poly(sp.subresultants(cr, fixed_E, delta)[-2], delta)
    assert linear.degree() == 1
    critical_delta = sp.cancel(-linear.nth(0)/linear.nth(1))
    for expr in (cr, fixed_E):
        numerator = sp.fraction(sp.cancel(expr.subs(delta, critical_delta)))[0]
        assert sp.rem(sp.Poly(numerator, kappa), sp.Poly(quartic, kappa)).is_zero
    kinterval = (F(2*blo-1), F(2*bhi-1))
    delta_lower = bernstein_positive(critical_delta-Q(23, 50), kappa, kinterval)
    delta_upper = bernstein_positive(Q(12, 25)-critical_delta, kappa, kinterval)
    # Reject the other root of the quartic in the broad kappa range.
    assert sp.Poly(quartic, kappa).count_roots(Q(13, 18), Q(1)) == 2
    return dict(critical_b_derivative_identity=True,
                resultant=str(resultant), kappa_quartic=str(quartic),
                B_quartic=str(Bquartic), B_interval=[str(blo), str(bhi)],
                B_decimal=str(sp.N((blo+bhi)/2, 60)),
                critical_delta_as_function_of_kappa=str(critical_delta),
                critical_delta_interval=['23/50', '12/25'],
                critical_delta_positive_bounds=[delta_lower, delta_upper],
                quartic_roots_in_broad_kappa_range=2,
                external_optimality_and_tangent_family_reproved=False,
                scope='critical-class elimination and relevant root isolation only')


def certificate():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled for certificate verification')
    stages = [endpoint_certificate(stage) for stage in STAGES]
    previous = F(7, 8)
    for stage in stages:
        assert F(stage['licensed_by_B']) == previous
        assert F(stage['B']) < previous
        previous = F(stage['B'])
    assert F(stages[1]['B']) == F(8748867, 10**7)
    assert previous == F(874886647041, 10**12)
    # Independent rational comparison to the old count ledger.
    for delta, x in ((F(1, 5), F(1, 4)), (F(2, 5), F(1, 2))):
        assert refined_endpoint(Q(STAGES[0][1]), Q(STAGES[0][2]), Q(3, 4),
                                Q(delta), Q(x))['R'] == Q(count_closed(delta, x, F(3, 4))['R'])
    return dict(scope='exact scalar reproduction and retained-direct-side barrier',
                analytic_estimate_proved=False, RH_claim=False, novelty_claim=False,
                stages=stages, fixed_point=fixed_point_regression(),
                direct_relaxation=direct_relaxation_certificate())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    data = json.dumps(certificate(), indent=2)+'\n'
    if args.output:
        # Validation receipts are never silently replaced.
        with args.output.open('x') as f:
            f.write(data)
    else:
        print(data, end='')


if __name__ == '__main__':
    main()
