"""Compare the Green recurrence with independent polynomial kernel derivatives.

This exercises reflected and nonreflected parameters, mixed jet orders, and
nonzero Green boundary terms. These are exact synthetic algebra diagnostics,
not a Lean check, a Xi-zero certificate, or an RH proof.
"""
from functools import lru_cache
from pathlib import Path
import json
import sympy as sp


def check_polynomial(degree: int) -> dict:
    z, s, u = sp.symbols('z s u')
    f = sp.expand(sum((2*z-1)**k for k in range(0, degree+1, 2)))
    assert sp.expand(f.subs(z, 1-z)-f) == 0
    kernel = sp.cancel(sp.I*(f.subs(z, s)-f.subs(z, u))/(s+u-1))
    sp.Poly(kernel, s, u)
    points = (sp.Rational(1, 4)+sp.I, sp.Rational(3, 4)+sp.I,
              sp.Rational(1, 2)+2*sp.I)
    order = 3

    @lru_cache(None)
    def derivative(p, point):
        return sp.expand(sp.diff(f, z, p).subs(z, point))

    @lru_cache(None)
    def recurrence(left, right, p, q):
        delta = sp.simplify(left+sp.conjugate(right)-1)
        if delta == 0:
            value = (sp.I*(-1)**q*sp.factorial(p)*sp.factorial(q)
                     *derivative(p+q+1, left)/sp.factorial(p+q+1))
        else:
            boundary = (derivative(p, left) if q == 0 else 0)
            boundary -= (sp.conjugate(derivative(q, right)) if p == 0 else 0)
            lower_left = p*recurrence(left, right, p-1, q) if p else 0
            lower_right = q*recurrence(left, right, p, q-1) if q else 0
            value = (sp.I*boundary-lower_left-lower_right)/delta
        return sp.simplify(value)

    labels = [(point, p) for point in points for p in range(order+1)]
    gram = sp.zeros(len(labels))
    reflected, away = 0, 0
    for a, (left, p) in enumerate(labels):
        for b, (right, q) in enumerate(labels):
            calculated = recurrence(left, right, p, q)
            independent = sp.diff(kernel, s, p, u, q).subs(
                {s: left, u: sp.conjugate(right)})
            assert sp.simplify(calculated-independent) == 0, (degree, left, right, p, q)
            gram[a, b] = calculated
            if sp.simplify(left+sp.conjugate(right)-1) == 0:
                reflected += 1
            else:
                away += 1
    assert sp.simplify(gram-sp.conjugate(gram.T)) == sp.zeros(len(labels))
    action = sp.zeros(len(labels))
    index = {label: a for a, label in enumerate(labels)}
    for a, (point, p) in enumerate(labels):
        action[a, a] = -sp.I*(point-sp.Rational(1, 2))
        if p:
            action[index[(point, p-1)], a] = -sp.I*p
    row = sp.Matrix([derivative(p, point) for point, p in labels])
    constant = sp.Matrix([int(p == 0) for _, p in labels])
    boundary = row*constant.T-constant*sp.conjugate(row.T)
    assert boundary != sp.zeros(len(labels))  # Test actual nonzero boundary terms.
    assert sp.simplify(action.T*gram-gram*sp.conjugate(action)-boundary) == sp.zeros(len(labels))
    return {'polynomial': str(f), 'degree': degree, 'jet_order_through': order,
            'matrix_dimension': len(labels), 'entries_compared': len(labels)**2,
            'reflected_entries': reflected, 'nonreflected_entries': away,
            'hermitian_matrix': True, 'green_identity_with_nonzero_boundary': True,
            'input_is_riemann_xi': False}


if __name__ == '__main__':
    cases = [check_polynomial(degree) for degree in (4, 8)]
    result = {'status': 'exact_synthetic_checks_passed', 'sympy_version': sp.__version__,
              'cases': cases, 'entries_compared': sum(c['entries_compared'] for c in cases),
              'scope': 'Synthetic polynomial diagnostics only; no Xi certificate or RH proof.',
              'rh_proved': False, 'lean_construction_verified': False}
    target = Path(__file__).with_name('green_recurrence_polynomial_diagnostics.json')
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(f"Compared {result['entries_compared']} exact entries and both nonzero-boundary Green matrices.")
