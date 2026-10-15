"""Exact toy-model check; not an Xi model or an RH counterexample.

Requires SymPy. Prints JSON; makes no repository changes.
"""
import json
import sympy as s

h = s.symbols("h", positive=True)
z, u = s.symbols("z u")
a = s.Rational(1, 4)
P = ((z - s.Rational(1, 2) - a) ** 2 + 1) * (
    (z - s.Rational(1, 2) + a) ** 2 + 1
)
rho = s.Rational(3, 4) + s.I
sigma = s.Rational(1, 4) + s.I
B = s.simplify(s.I * s.diff(P, z).subs(z, rho))
T = s.diag(1 - s.I / 4, 1 + s.I / 4)
H = s.Matrix([[0, B], [s.conjugate(B), 0]])


def eta(x, y):
    """Linear in x, conjugate-linear in y."""
    return s.simplify((x.T * H * s.conjugate(y))[0])


def norm_sq(x):
    return s.simplify((s.conjugate(x).T * x)[0])


assert s.simplify(P - P.subs(z, 1 - z)) == 0
assert s.simplify(P.subs(z, rho)) == 0
assert s.simplify(P.subs(z, sigma)) == 0
assert H == s.conjugate(H.T)
assert s.simplify(T.T * H - H * s.conjugate(T)) == s.zeros(2)
folded = s.expand(P.subs(z, s.Rational(1, 2) + s.sqrt(u)))
assert all(c > 0 for c in s.Poly(folded, u).all_coeffs())
v = s.Matrix([1, 0])
w = s.Matrix([0, 1])
y = v + h * B * w
q = eta(y, y)
assert q == s.Rational(17, 2) * h
psi = y / s.sqrt(q)
residual = (T - (1 - s.I / 4) * s.eye(2)) * psi
defect = s.simplify(eta(residual, psi) - eta(psi, residual))
assert eta(psi, psi) == 1
assert norm_sq(residual) == h / 8
assert s.simplify(s.Abs(defect)) == s.Rational(1, 2)
assert s.limit(norm_sq(psi), h, 0, dir="+") == s.oo
assert s.limit(norm_sq(residual), h, 0, dir="+") == 0

print(json.dumps({
    "status": "passed",
    "kind": "exact symbolic countermodel to a generic inference, not RH",
    "sympy_version": s.__version__,
    "folded_polynomial": str(folded),
    "B": str(B),
    "packet_mass": str(eta(psi, psi)),
    "packet_norm_squared": str(norm_sq(psi)),
    "residual_norm_squared": str(norm_sq(residual)),
    "paired_defect_absolute": str(s.Abs(defect)),
    "norm_product_limit_squared": str(s.limit(norm_sq(psi) * norm_sq(residual), h, 0, dir="+")),
}, indent=2))
