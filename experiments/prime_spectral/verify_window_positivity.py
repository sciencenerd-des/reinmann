"""Recheck the full-window certificate and independently integrate low entries."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx

from certified_weil import entry, inertia
from weil_matrix import prime_powers
from compact_window_certificate import bounds, pole_legendre


def box(data):
    return arb(data['lo']).union(arb(data['hi']))


def independent_entry(n, m, a, cutoff, beta, powers):
    """Adaptive complex-ball integration, independent of Gauss assembly."""
    def amplitude(n, t):
        z = a*t
        return ((2*a*(2*n+1)).sqrt() * z**n
                / (arb(2)**(n+1) * (arb(n)+arb(3)/2).gamma())
                * arb.pi().sqrt()
                * (-z*z/4).hypgeom_0f1(arb(n)+arb(3)/2))

    def integrand(t, analytic):
        # This is meromorphic; poles produce nonfinite balls automatically.
        z1, z2 = arb(1)/4 + acb(0,1)*t/2, arb(1)/4 - acb(0,1)*t/2
        h = (z1.digamma()+z2.digamma())/2 - arb.pi().log() - beta
        h -= sum((2*arb(p).log()/arb(q).sqrt() * (t*arb(q).log()).cos()
                  for q,p in powers), acb(0))
        return h * amplitude(n,t)*amplitude(m,t) * (-1)**((n-m)//2) / arb.pi()

    tol = arb(2)**-180
    value = sum((acb.integral(integrand, j, min(j+4,cutoff), abs_tol=tol, rel_tol=tol,
                             eval_limit=200000) for j in range(0,cutoff,4)), acb(0))
    if (not value.is_finite() or not value.imag.contains(0)
            or not value.real.rad() < arb('1e-48')):
        raise ArithmeticError(f'independent integral unresolved at {(n,m)}: {value}')
    poles = pole_legendre(a, max(n,m)+1)
    return value.real + 2*(-1)**(n%2)*poles[n]*poles[m] + (beta if n==m else 0)


def verify(path, independent=True):
    data = json.loads(Path(path).read_text())
    if data['status'] != 'certified_full_window_lower_bound':
        raise ValueError('full-window certificate required')
    for name, digest in data['source_hashes'].items():
        if hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() != digest:
            raise ValueError('source mismatch: '+name)
    with ctx.workprec(max(512, data['bits'])):
        a, count, cutoff = arb(data['half_width']), data['polynomial_count'], data['cutoff']
        c = (2*a).exp()
        powers = [(q,p) for q,p in prime_powers(int(c.ceil().fmpq()))
                  if arb(q).log() < 2*a]
        if [list(x) for x in powers] != data['active_prime_powers']:
            raise ValueError('prime content mismatch')
        beta, quad, coupling, tail, _ = bounds(a, cutoff, count, data['gauss_order'], powers)
        lower = arb(data['finite_lower'])
        if not (0 < a <= 1 and count >= 2 and count % 2 == 0 and lower > 0):
            raise ValueError('invalid window certificate parameters')
        for label, value in [('C',c), ('beta',beta), ('quadrature_operator_error',quad),
                             ('infinite_coupling_bound',coupling), ('infinite_tail_deviation',tail)]:
            if not box(data[label]).contains(value):
                raise ValueError('recorded constant does not enclose recomputation: '+label)
        if len(data['sectors']) != 2:
            raise ValueError('both parity sectors required')
        independent_checks = []
        for parity, sector in enumerate(data['sectors']):
            if sector['parity'] != ('odd' if parity else 'even') or sector['dimension'] != count//2:
                raise ValueError('sector mismatch')
            rows = [[box(x) for x in row] for row in sector['quadrature_matrix']]
            if len(rows) != count//2 or any(len(row) != count//2 for row in rows):
                raise ValueError('matrix shape mismatch')
            if any(not rows[i][j].overlaps(rows[j][i]) for i in range(len(rows)) for j in range(i)):
                raise ValueError('matrix not symmetric')
            negatives, pivots = inertia(rows, lower+quad)
            if negatives or not all(x>0 for x in pivots):
                raise ArithmeticError('shifted LDL check failed')
            if independent:
                for i,j in [(0,0), (0,1)]:
                    with ctx.workprec(256):
                        exact = independent_entry(2*i+parity, 2*j+parity, a, cutoff, beta, powers)
                    if not (rows[i][j]+arb(0,quad.upper())).overlaps(exact):
                        raise ArithmeticError('independent frequency integral mismatch')
                    independent_checks.append([2*i+parity,2*j+parity])
                    print('independent entry checked:', independent_checks[-1], flush=True)
        method = data.get('block_method', 'linear')
        if method == 'schur':
            target = arb(data['schur_target'])
            determinant = (lower-target)*(beta-tail-target)-coupling**2
            if (not lower > target or not determinant > 0
                    or not box(data['schur_determinant']).contains(determinant)):
                raise ArithmeticError('Schur determinant check failed')
            full = target
        elif method == 'linear':
            full = lower.min(beta-tail)-coupling
        else:
            raise ValueError('unknown block method')
        # The public decimal is deliberately weaker than the unrounded bound.
        if not full > arb('9e-13') or not box(data['full_lower_bound']).contains(full):
            raise ArithmeticError('full-window public lower bound failed')
        # Independent geometric-side normalization of the constant function.
        # R <= Q, with all prime weights intact.
        if independent:
            with ctx.workprec(256):
                geometric = entry(0,0,2*a,powers,c)
                reduced = independent_entry(0,0,a,cutoff,beta,powers)
            if not geometric >= reduced:
                raise ArithmeticError('constant-function normalization/order mismatch')
        return {'status':'verified_full_window_certificate',
                'public_lower':'9e-13', 'C':'exp(6/5)' if data['half_width']=='3/5' else str(c),
                'independent_adaptive_integral_entries':independent_checks,
                'independent_geometric_constant_check':independent,
                'block_method':method,
                'certificate_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest(),
                'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.certificate)
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
