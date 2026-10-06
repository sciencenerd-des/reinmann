"""Exact Gaussian cancellation identities and a conservative tail budget.

The associated analytic proof is in RH_GAUSSIAN_CURVATURE_TAIL_2026_09_19.md.
These algebraic checks alone are not an analytic sign certificate or an RH proof.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from pathlib import Path
from flint import fmpq_mpoly_ctx, fmpq_poly


def exact_identities():
    context = fmpq_mpoly_ctx.get(('t', 'lam', 'b', 'c'))
    t, lam, b, c = context.gens()
    moments = [context.constant(1), t]
    for n in range(1, 6):
        moments.append(t * moments[n] + n * moments[n - 1])
    first = lam * moments[1] + b * moments[3]
    second = (c * moments[4] + lam**2 * moments[2] / 2
              + lam * b * moments[4] + b**2 * moments[6] / 2)
    cumulant = first + second - first**2 / 2
    expected = (lam**2 / 2 + 3*c + 3*lam*b + 15*b**2 / 2
                + (lam + 3*b)*t + (6*c + 3*lam*b + 18*b**2)*t**2
                + b*t**3 + (c + 9*b**2 / 2)*t**4)
    u = fmpq_poly([0, 1])
    v = 1 + 2*u
    t3 = 1 + 6*u + 4*u**2
    t4 = 1 + 14*u + 24*u**2 + 8*u**3
    ell_numerator = 2*v**3 - 2*t3
    m_numerator = -4*v**5 - 2*t4*v + 6*t3**2
    curvature_numerator = -16*u**2*v**4 - 4*u*m_numerator - ell_numerator**2
    checks = {
        'gaussian_log_polynomial': cumulant == expected,
        'ell_factorization': ell_numerator == 16*u**2*(u+1),
        'm_factorization': m_numerator == -16*u**3*(8*u**2+16*u+9),
        'negative_curvature_numerator': curvature_numerator == -16*u**2*(4*u**2+8*u+1),
    }
    if not all(checks.values()):
        raise ArithmeticError('exact polynomial identity failed')
    return checks


def tail_budget(threshold_u=2000):
    if type(threshold_u) is not int or threshold_u < 2000:
        raise ValueError('integer Lambert coordinate threshold at least 2000 required')
    # exp(u) >= 2**u and d/du log(u**102 * 2**(-u)) <= 102/u - 1/2 < 0.
    smallness = Fraction(10**70 * threshold_u**60, 2**threshold_u)
    if smallness >= Fraction(1, 10**100):
        raise ArithmeticError('Gaussian expansion smallness check failed')
    ratio = Fraction(81 * 10**131 * threshold_u**102, 2**threshold_u)
    if ratio >= Fraction(1, 2):
        raise ArithmeticError('tail error does not fit half the negative margin')
    return {'u_threshold': threshold_u,
            'anchor_threshold': f'pi*{threshold_u}*exp({2*threshold_u})',
            'relative_error_upper': str(ratio),
            'smallness_upper': str(smallness),
            'scope': 'All real anchors with u=W(2a/pi)/2 at least u_threshold; analytic majorant requires the accompanying proof.'}


def run():
    return {'schema_version': 1,
            'status': 'exact_algebra_and_tail_budget_checked',
            'identities': exact_identities(), 'tail_budget': tail_budget(),
            'analytic_reference': 'research/RH_GAUSSIAN_CURVATURE_TAIL_2026_09_19.md',
            'remaining': 'All anchors below the tail threshold and the interior all-rank budget; RH is not proved.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'])


if __name__ == '__main__':
    main()
