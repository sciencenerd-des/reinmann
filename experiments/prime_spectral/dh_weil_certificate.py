"""Actual DH geometric form: conductor five, odd gamma, no pole block.

The log-derivative measure runs over all integers, not just prime powers.
An explicit negative trial proves failure of the full form; positive finite
sections do not prove full-window positivity. All integrals are Arb balls.
"""
import argparse
import json
from pathlib import Path

from flint import acb, arb, ctx

from certified_weil import arch_regularized, correlation_ball, endpoints, inertia
from davenport_heilbronn_control import dirichlet_coefficients, log_derivative_coefficients
from full_ground_fourier import sha256
from full_cluster_residual import select_columns

OUT = Path('research/prime_spectral/verification_2026_10_12_remaining')


def geometric_entry(m, n, length, coefficients, cutoff):
    # Re psi(3/4+it/2)-Re psi(1/4+it/2) has Fourier kernel
    # 1/(2 cosh(y/2)); the conductor adds log(5)*||f||^2.
    tol = arb(2)**-360
    integral = acb.integral(
        lambda z, _: -arch_regularized(m, n, z, length)
        + correlation_ball(m, n, z, length)/(2*(z/2).cosh()),
        0, length, rel_tol=tol, abs_tol=tol, eval_limit=400000)
    q0 = 2 if m == n else 0
    integral += (arb(5).log()-(4*arb.pi()).log()-arb.const_euler()
                 -(length/2).tanh().log())*q0/2
    for j in range(2, cutoff):
        integral -= coefficients[j]/arb(j).sqrt()*correlation_ball(
            m, n, acb(arb(j).log()), length)
    if not integral.is_finite() or not integral.imag.contains(0):
        raise ArithmeticError('DH integral unresolved')
    return integral.real


def assemble(cutoff, modes):
    if type(cutoff) is not int or not 2 <= cutoff <= 1000:
        raise ValueError('integer cutoff 2..1000 required')
    if type(modes) is not int or not 1 <= modes <= 128:
        raise ValueError('modes 1..128 required')
    L = arb(cutoff).log()
    c = log_derivative_coefficients(dirichlet_coefficients(cutoff))
    b = [arb(0)]
    diagonal, opposite = [], []
    diagonal.append(geometric_entry(0, 0, L, c, cutoff))
    for n in range(1, modes+1):
        b.append(n*geometric_entry(n, 0, L, c, cutoff))
        diagonal.append(geometric_entry(n, n, L, c, cutoff))
        opposite.append(geometric_entry(n, -n, L, c, cutoff))
    even = [[arb(0) for _ in range(modes+1)] for _ in range(modes+1)]
    odd = [[arb(0) for _ in range(modes)] for _ in range(modes)]
    even[0][0] = diagonal[0]
    for n in range(1, modes+1):
        even[0][n] = even[n][0] = arb(2).sqrt()*b[n]/n
        even[n][n] = diagonal[n]+opposite[n-1]
        odd[n-1][n-1] = diagonal[n]-opposite[n-1]
        for m in range(1, n):
            even[m][n] = even[n][m] = 2*(n*b[n]-m*b[m])/(n*n-m*m)
            odd[m-1][n-1] = odd[n-1][m-1] = 2*(m*b[n]-n*b[m])/(n*n-m*m)
    return even, odd


def negative_ldl_witness(A):
    """Find first negative leading pivot; exact decimals then Arb Rayleigh."""
    n = len(A)
    L = [[arb(0) for _ in range(n)] for _ in range(n)]
    pivots = []
    for i in range(n):
        d = A[i][i]-sum((L[i][k]**2*pivots[k] for k in range(i)), arb(0))
        if d.contains(0) or not d.is_finite():
            raise ArithmeticError('LDL sign unresolved')
        L[i][i] = arb(1)
        pivots.append(d)
        if d < 0:
            # x=L^{-T}e_i makes x^T A x=d, in exact arithmetic.
            x = [arb(0) for _ in range(i+1)]
            x[i] = arb(1)
            for j in range(i-1, -1, -1):
                x[j] = -sum((L[k][j]*x[k] for k in range(j+1, i+1)), arb(0))
            # Rational midpoints are exact, so no eigenvector oracle is trusted.
            exact = [str(v.mid().fmpq()) for v in x]
            v = [arb(t) for t in exact]
            norm = sum((t*t for t in v), arb(0))
            q = sum((v[j]*A[j][k]*v[k] for j in range(i+1)
                     for k in range(i+1)), arb(0))/norm
            if not q < 0:
                raise ArithmeticError('explicit negative Rayleigh gate failed')
            return {'first_negative_pivot_index': i,
                    'earlier_leading_sections_positive': i,
                    'exact_trial_coefficients': exact,
                    'normalized_full_form': endpoints(q),
                    'pivots_through_failure': [endpoints(p) for p in pivots]}
        for j in range(i+1, n):
            L[j][i] = (A[j][i]-sum((L[j][k]*L[i][k]*pivots[k]
                                   for k in range(i)), arb(0)))/d
    return {'positive_finite_section': True,
            'positive_pivots': [endpoints(p) for p in pivots]}


def generate(cutoff=31, modes=60):
    with ctx.workprec(768):
        even, odd = assemble(cutoff, modes)
        sectors = []
        for parity, A in [('even', even), ('odd', odd)]:
            result = negative_ldl_witness(A)
            result.update(parity=parity, dimension=len(A),
                          matrix=[[endpoints(x) for x in row] for row in A])
            sectors.append(result)
        negative = any('normalized_full_form' in s for s in sectors)
        return {'status': 'certified_full_DH_form_negative_trial' if negative
                else 'certified_positive_DH_finite_sections_only',
                'C': cutoff, 'modes': modes, 'bits': 768, 'sectors': sectors,
                'normalization': 'Lambda(s)=(5/pi)^(s/2)*Gamma((s+1)/2)*H(s)',
                'source_sha256': {name: sha256(Path(__file__).with_name(name))
                                  for name in ['dh_weil_certificate.py',
                                  'davenport_heilbronn_control.py',
                                  'certified_weil.py', 'weil_matrix.py']},
                'scope': 'Negativity is a full-form witness. First pivot is first only in this nested finite parity family at this C, not a first full negative window.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff', type=int, default=31)
    parser.add_argument('--modes', type=int, default=60)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    result = generate(args.cutoff, args.modes)
    (OUT/f'dh_weil_C{args.cutoff}_N{args.modes}.json').write_text(
        json.dumps(result, indent=2)+'\n')
    print(result['status'], flush=True)
    for s in result['sectors']:
        print(s['parity'], s.get('first_negative_pivot_index', 'positive'),
              s.get('normalized_full_form'), flush=True)
