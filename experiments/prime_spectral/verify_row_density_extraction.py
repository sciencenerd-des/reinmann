"""Exact arithmetic checks for the conditional row-density audit; no RH proof."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'research/prime_spectral/verification_2026_10_22_row_density'


def add(a, b):
    c = [0] * max(len(a), len(b))
    for i, v in enumerate(a): c[i] += v
    for i, v in enumerate(b): c[i] += v
    while len(c) > 1 and c[-1] == 0: c.pop()
    return tuple(c)


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): c[i+j] += x*y
    return add(tuple(c), (0,))


def neg(a): return tuple(-x for x in a)


def dh_inverse():
    # Independent polynomial Dirichlet inversion of the actual period;
    # coefficients are polynomials in the real parameter kappa.
    period = [(0,), (1,), (0, 1), (0, -1), (-1,)]
    a = [(0,)] + [period[n % 5] for n in range(1, 92)]
    b = [(0,)] * 92; b[1] = (1,)
    for n in range(2, 92):
        value = (0,)
        for d in range(2, n+1):
            if n % d == 0: value = add(value, mul(a[d], b[n//d]))
        b[n] = neg(value)
    for n in range(1, 92):
        value = (0,)
        for d in range(1, n+1):
            if n % d == 0: value = add(value, mul(a[d], b[n//d]))
        assert value == ((1,) if n == 1 else (0,))
    assert b[7] == (0, -1) and b[13] == (0, 1)
    assert b[91] == (-1, 0, -2)
    defect = add(b[91], neg(mul(b[7], b[13])))
    assert defect == (-1, 0, -1) and gcd(91, 2*3*5) == 1
    return {'convention': 'ordinary Dirichlet inverse of DH, polynomial coefficients in kappa, not Taylor coefficients',
            'inverse_convolution_indices_checked': 91, 'b7': list(b[7]),
            'b13': list(b[13]), 'b91': list(b[91]),
            'b91_minus_b7_b13': list(defect),
            'interpretation': '-1-kappa^2 < 0 for every real kappa; witness survives exclusion of primes 2,3,5',
            'globally_first_cancellation_or_PF_failure': False}


def emul(x, y):
    a, b = x; c, d = y
    return a*c-b*d, a*d+b*c-b*d


def epow(z, n):
    out = (1, 0)
    for _ in range(n): out = emul(out, z)
    return out


def local_characters():
    results = []
    for a, b in [(-2, -3), (1, -3), (-2, 3), (1, 6)]:
        q = a*a-a*b+b*b
        assert all(q % p for p in range(2, isqrt(q)+1)) and q % 6 == 1
        assert a % 3 == 1 and b % 3 == 0
        omega = (-a*pow(b, -1, q)) % q
        root = (1+omega) % q
        log6 = {pow(root, j, q): j for j in range(6)}
        assert len(log6) == 6
        char = {x: log6[pow(x, (q-1)//6, q)] for x in range(1, q)}
        jacobi = (0, 0)
        for x in range(2, q):
            value = epow((0, 1), (char[x]+char[(1-x) % q]) % 3)
            jacobi = jacobi[0]+value[0], jacobi[1]+value[1]
        assert jacobi == (-a, -b), (a, b, jacobi)
        results.append({'primary_prime': [a, b], 'norm': q, 'omega_mod_prime': omega,
                        'exact_cubic_Jacobi_sum': list(jacobi)})
    # n=-2-3omega, norm 7; row prime p=1-3omega, norm 13.
    # Mod n: omega=4 and p=3. Its sextic-character exponent is 5.
    n = results[0]; q = n['norm']; omega = n['omega_mod_prime']
    u = (1-3*omega) % q
    log6 = {pow(1+omega, j, q): j for j in range(6)}
    j = log6[pow(u, (q-1)//6, q)]
    assert q == 7 and u == 3 and j == 5
    assert 3*j % 6 == 3 and 6*j % 6 == 0 and 2*3*j % 6 == 0
    reflection = {str(j): {'exponent': (-j-2) % 6,
                           'order': 6//gcd((-j-2) % 6, 6)} for j in [1, 2, 3, 5]}
    assert reflection['1']['order'] == 2 and reflection['2']['order'] == 3
    return {'normalization_checks': results,
            'exact_cubic_row_counterexample': {'column_prime_norm': 7, 'row_prime_norm': 13,
                'sextic_character_at_row_prime_exponent_mod_6': j,
                'sextic_character_at_cube_exponent_mod_6': 3*j % 6,
                'sextic_character_at_cube': -1,
                'sextic_character_at_sixth_power': 1,
                'cubic_character_at_cube': 1},
            'reflection_on_generic_character_cases': reflection,
            'scope': 'Exact finite-field checks and a row-identity counterexample; not a mean-square estimate or proof of all theta identities.'}


def optimization():
    rows = []
    for k in range(1, 101):
        h = Q(k, k+1); target = h
        a, slope = Q(1, 2), Q(k-1, 2*k)
        w1, w2 = Q(2, k+1), Q(k-1, k+1)
        assert w1+w2 == 1 and min(w1, w2) >= 0
        assert w1*a+w2 == target and w1*slope-w2/k == 0
        assert a+slope*h == 1-h/k == target
        at_one = max(a+slope, 1-Q(1, k))
        assert at_one == 1-Q(1, 2*k)
        for hn in [Q(0), Q(1, 4), h, Q(1), Q(2), Q(10)]:
            assert max(a+slope*hn, 1-hn/k) >= target
        if k <= 6:
            rows.append({'k': k, 'smallest_minimizing_h': str(h),
                         'unrestricted_infimum_sigma': str(target),
                         'infimum_for_h_greater_than_1': str(at_one),
                         'minimizer_unique': k != 1})
    assert max(Q(1,2), 1-Q(3,4)) == Q(1,2)
    assert max(Q(1,2), 1-Q(2)) == Q(1,2)
    return {'table': rows, 'rational_parameter_checks_k': [1, 100],
            'general_proof': 'See note: 2 A(h)+(k-1) B(h)=k, and both lines meet at h=k/(k+1). For k=1, every h>=1/2 minimizes.',
            'scope': 'Algebra of an assumed extraction upper bound, not an arithmetic lower bound or a Lean theorem.'}


def calculate():
    paper = (OUT/'paper2.tex').read_text()
    for anchor in [r'\label{eq:ms}', r'\label{eq:prime-extract}',
                   r'\label{eq:convert2}', r'\label{eq:theta-local-factors}',
                   r'\label{eq:initial-positive-gap}']:
        assert anchor in paper, anchor
    return {'status': 'exact_row_density_and_DH_structure_checks_passed',
            'optimization': optimization(), 'local_arithmetic': local_characters(),
            'DH_reciprocal': dh_inverse(), 'new_mean_square_proved': False,
            'cubic_substitution_proved': False, 'RH_proved': False,
            'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in [Path(__file__).resolve(), OUT/'paper2.tex',
                    ROOT/'experiments/prime_spectral/davenport_heilbronn_control.py']}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true'); args = parser.parse_args()
    result = calculate()
    if args.write:
        path = OUT/'exact_checks.json'
        assert not path.exists(), 'Preserve existing verification receipt'
        path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
