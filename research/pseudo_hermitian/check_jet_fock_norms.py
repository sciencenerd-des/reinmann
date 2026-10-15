"""Exact finite diagnostics for the written all-order Fock jet norm formulas.

These checks do not certify Xi zeros, formalize the all-order result in Lean,
or establish the RH-strength relative paired residual budget.
"""
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json
import sympy as sp


def check_formulas(max_order=12, max_coefficient=80):
    r = sp.symbols('r', real=True)
    norm_coefficients = cross_coefficients = symbolic_identities = 0
    for p in range(max_order + 1):
        polynomial = factorial(p) * sum(
            sp.binomial(p, j) * r**j / sp.factorial(j) for j in range(p + 1))
        independent = sp.diff(r**p * sp.exp(r), r, p) / sp.exp(r)
        assert sp.expand(independent - polynomial) == 0, ('norm_symbolic', p)
        symbolic_identities += 1
        for k in range(max_coefficient + 1):
            lhs = Fraction(factorial(k + p), factorial(k)**2)
            rhs = sum((Fraction(factorial(p) * comb(p, j),
                                factorial(j) * factorial(k - j))
                       for j in range(min(p, k) + 1)), Fraction(0))
            assert lhs == rhs, ('norm_coefficient', p, k)
            norm_coefficients += 1
        if p:
            cross_polynomial = factorial(p - 1) * sum(
                sp.binomial(p, j + 1) * r**j / sp.factorial(j)
                for j in range(p))
            independent_cross = sp.cancel(
                sp.diff(r**p * sp.exp(r), r, p - 1) / (r * sp.exp(r)))
            assert sp.expand(independent_cross - cross_polynomial) == 0, ('cross_symbolic', p)
            symbolic_identities += 1
            for k in range(max_coefficient + 1):
                lhs = Fraction(factorial(k + p), factorial(k) * factorial(k + 1))
                rhs = sum((Fraction(factorial(p - 1) * comb(p, j + 1),
                                    factorial(j) * factorial(k - j))
                           for j in range(min(p - 1, k) + 1)), Fraction(0))
                assert lhs == rhs, ('cross_coefficient', p, k)
                cross_coefficients += 1
    return {'max_jet_order': max_order, 'max_series_coefficient': max_coefficient,
            'exact_norm_coefficients': norm_coefficients,
            'exact_adjacent_pairing_coefficients': cross_coefficients,
            'symbolic_derivative_identities': symbolic_identities}


if __name__ == '__main__':
    result = {'status': 'exact_finite_algebra_checks_passed',
              'checks': check_formulas(), 'sympy_version': sp.__version__,
              'scope': 'Finite combinatorial and symbolic diagnostics for the written formulas.',
              'general_lean_proof': False, 'xi_zero_certificate': False,
              'relative_paired_budget_proved': False, 'rh_proved': False}
    Path(__file__).with_name('jet_fock_norm_diagnostics.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result['checks'], sort_keys=True))
