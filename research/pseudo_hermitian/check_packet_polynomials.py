"""Exact synthetic checks of packet factors, signs and paired residuals.

The inputs are reflection-symmetric rational polynomials, not Riemann Xi.
This independently assembles the jet Gram matrix and differentiation matrix.
It is diagnostic evidence for the written formulas, not a proof about Xi zeros.
"""
from pathlib import Path
import json
import sympy as sp


def check_case(critical: bool, multiplicity: int) -> dict:
    z, s, u = sp.symbols('z s u')
    rho = (sp.Rational(1, 2) if critical else sp.Rational(1, 4)) + sp.I
    sigma = 1 - sp.conjugate(rho)
    roots = sorted({rho, sp.conjugate(rho), 1-rho, 1-sp.conjugate(rho)}, key=str)
    polynomial = sp.expand(sp.prod((z-root)**multiplicity for root in roots))
    assert sp.expand(polynomial.subs(z, 1-z)-polynomial) == 0
    assert all(sp.im(c) == 0 for c in sp.Poly(polynomial, z).all_coeffs())
    kernel = sp.cancel(sp.I*(polynomial.subs(z, s)-polynomial.subs(z, u))/(s+u-1))
    sp.Poly(kernel, s, u)  # Confirm the removable quotient is a polynomial.
    p = multiplicity-1
    labels = list(dict.fromkeys([(rho, 0), *[(sigma, j) for j in range(p+1)]]))
    index = {label: i for i, label in enumerate(labels)}
    gram = sp.Matrix(len(labels), len(labels), lambda a, b: sp.simplify(
        sp.diff(kernel, s, labels[a][1], u, labels[b][1]).subs(
            {s: labels[a][0], u: sp.conjugate(labels[b][0])})))
    action = sp.zeros(len(labels))
    lam = lambda point: -sp.I*(point-sp.Rational(1, 2))
    for column, (point, order) in enumerate(labels):
        action[column, column] = lam(point)
        if order:
            action[index[(point, order-1)], column] = -sp.I*order
    assert gram == sp.conjugate(gram.T)
    assert sp.simplify(action.T*gram-gram*sp.conjugate(action)) == sp.zeros(len(labels))
    v, w = index[(rho, 0)], index[(sigma, p)]
    cross = gram[v, w]
    expected = sp.I*(-1)**(multiplicity+1)*sp.diff(polynomial, z, multiplicity).subs(z, rho)/multiplicity
    assert sp.simplify(cross-expected) == 0 and cross != 0
    state = sp.zeros(len(labels), 1)
    state[v] = 1
    if gram[v, v] == 0:
        b = sp.sqrt(sp.simplify(cross*sp.conjugate(cross)))
        diagonal = gram[w, w]
        h = b/(2*(1+b)*(1+sp.Abs(diagonal)))
        state[w] += h*cross/b
        raw_mass = sp.simplify((state.T*gram*sp.conjugate(state))[0])
        assert sp.simplify(raw_mass-(2*h*b+h*h*diagonal)) == 0
        assert sp.simplify(raw_mass-h*b).is_positive
    else:
        h = None
        raw_mass = gram[v, v]
    state = state/sp.sqrt(sp.Abs(raw_mass))
    mass = sp.simplify((state.T*gram*sp.conjugate(state))[0])
    residual = (action-lam(rho)*sp.eye(len(labels)))*state
    paired_defect = sp.simplify((residual.T*gram*sp.conjugate(state)
        -state.T*gram*sp.conjugate(residual))[0])
    assert sp.Abs(mass) == 1
    assert sp.simplify(paired_defect+(lam(rho)-sp.conjugate(lam(rho)))*mass) == 0
    expected_defect = 2*sp.Abs(sp.re(rho)-sp.Rational(1, 2))
    assert sp.simplify(sp.Abs(paired_defect)-expected_defect) == 0
    return {'synthetic_polynomial': str(polynomial), 'rho': str(rho),
            'multiplicity': multiplicity, 'packet_dimension': len(labels),
            'nonzero_cross_pairing': str(cross), 'mixture_parameter': str(h),
            'normalized_signed_mass': str(mass),
            'paired_residual_defect_norm': str(sp.Abs(paired_defect)),
            'exact_checks_passed': True, 'input_is_riemann_xi': False}


if __name__ == '__main__':
    cases = [check_case(critical, m) for critical in (True, False) for m in (1, 2, 3)]
    target = Path(__file__).with_name('packet_polynomial_diagnostics.json')
    target.write_text(json.dumps({'status': 'exact_synthetic_checks_passed',
        'sympy_version': sp.__version__, 'cases': cases, 'rh_proved': False,
        'scope': 'Synthetic polynomial packets only; not a certificate for Xi zeros.'}, indent=2)+'\n')
    print(f'{len(cases)} exact synthetic packet checks passed; saved {target}')
