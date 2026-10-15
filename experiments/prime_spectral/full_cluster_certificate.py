"""Full Weil cluster counts from two-sided min--max certificates.

The comparison block includes its infinite complement. Actual geometric-side
Ritz matrices supply upper bounds at the target support. No internal gap,
zero ordinates, RH, or conjectural counting law is used by the verifier.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path

from flint import arb, ctx
import mpmath as mp

from certified_weil import entry, endpoints, inertia
from compact_window_certificate import bounds
from full_ground_fourier import require_replay, sha256
from threshold_ground_gap import box
from weil_matrix import prime_powers

OUT = Path('research/prime_spectral/verification_2026_10_12_cluster')
BASE = Path('research/prime_spectral/verification_2026_10_11_fourier_ground_state')


def proposed_rank(cutoff):
    """User-proposed rank; only a proposal, never a verified spectral count."""
    c = Fraction(cutoff)
    if c < 2:
        raise ValueError('cutoff at least two required')
    return (2*c-Fraction(7, 4)).__floor__()+1


def actual_ritz(cutoff, modes):
    """Adaptive Arb integration of both parity sectors at exact rational C."""
    c = arb(cutoff)
    if not c.is_finite() or not c >= 2 or type(modes) is not int or not 1 <= modes <= 32:
        raise ValueError('finite C >= 2 and modes 1..32 required')
    L = c.log()
    powers = []
    for q, p in prime_powers(int(c.ceil().fmpq())):
        if arb(q) < c:
            powers.append((q, p))
        elif not arb(q) >= c:
            raise ArithmeticError('prime threshold unresolved')
    # Off-diagonal entries follow the exact divided-difference formula in
    # the original exponential basis; both parity diagonals are integrated.
    b = [arb(0)] + [n*entry(n, 0, L, powers, c) for n in range(1, modes+1)]
    even = [[arb(0) for _ in range(modes+1)] for _ in range(modes+1)]
    odd = [[arb(0) for _ in range(modes)] for _ in range(modes)]
    even[0][0] = entry(0, 0, L, powers, c)
    for n in range(1, modes+1):
        even[0][n] = even[n][0] = arb(2).sqrt()*b[n]/n
        d = entry(n, n, L, powers, c)
        e = entry(n, -n, L, powers, c)
        even[n][n], odd[n-1][n-1] = d+e, d-e
        for m in range(1, n):
            even[m][n] = even[n][m] = 2*(n*b[n]-m*b[m])/(n*n-m*m)
            odd[m-1][n-1] = odd[n-1][m-1] = 2*(m*b[n]-n*b[m])/(n*n-m*m)
    return even, odd, powers


def check_ritz(data, cutoff, upper):
    if (data.get('status') != 'geometric_ritz_blocks' or data.get('C') != cutoff
            or data.get('source_sha256') != {
                n: sha256(Path(__file__).with_name(n)) for n in
                ('full_cluster_certificate.py', 'certified_weil.py', 'weil_matrix.py')}):
        raise ValueError('Ritz provenance mismatch')
    modes = data['modes']
    c = arb(cutoff)
    powers = [[q, p] for q, p in prime_powers(int(c.ceil().fmpq())) if arb(q) < c]
    if data.get('active_prime_powers') != powers:
        raise ValueError('Ritz prime content mismatch')
    counts, records = [], []
    if len(data['sectors']) != 2:
        raise ValueError('both Ritz parities required')
    for parity, size, sector in zip(('even', 'odd'), (modes+1, modes), data['sectors'], strict=True):
        A = [[box(e) for e in row] for row in sector['matrix']]
        if (sector['parity'] != parity or len(A) != size or any(len(row) != size for row in A)
                or any(not A[i][j].overlaps(A[j][i]) for i in range(size) for j in range(i))):
            raise ValueError('Ritz shape or symmetry mismatch')
        count, pivots = inertia(A, upper)
        counts.append(count)
        records.append({'parity': parity, 'count_below_upper': count,
                        'pivots': [endpoints(p) for p in pivots]})
    return counts, records


def lower_counts(data, target, shift):
    """Return full lower bound on the first eigenvalue above each finite count."""
    if data.get('status') != 'certified_full_window_lower_bound':
        raise ValueError('full lower comparison required')
    for name in ('compact_window_certificate.py', 'certified_weil.py', 'weil_matrix.py'):
        if data.get('source_hashes', {}).get(name) != sha256(Path(__file__).with_name(name)):
            raise ValueError('comparison source mismatch')
    a = arb(data['half_width'])
    if not 0 < a <= 1 or not 2*a >= arb(target).log():
        raise ValueError('comparison must contain the target support')
    c = (2*a).exp()
    powers = [(q, p) for q, p in prime_powers(int(c.ceil().fmpq())) if arb(q).log() < 2*a]
    if data['active_prime_powers'] != [list(x) for x in powers]:
        raise ValueError('comparison prime content mismatch')
    n = data['polynomial_count']
    if type(n) is not int or n < 2 or n % 2:
        raise ValueError('positive even comparison dimension required')
    beta, quad, coupling, tail, _ = bounds(a, data['cutoff'], n, data['gauss_order'], powers)
    for name, value in [('C', c), ('beta', beta), ('quadrature_operator_error', quad),
                        ('infinite_coupling_bound', coupling), ('infinite_tail_deviation', tail)]:
        if not box(data[name]).contains(value):
            raise ValueError('comparison bound mismatch: '+name)
    s = arb(shift)
    if not s.is_finite() or not s < beta:
        raise ArithmeticError('outer shift must be below the infinite complement')
    counts, records = [], []
    if len(data['sectors']) != 2:
        raise ValueError('both comparison parities required')
    for parity, sector in zip(('even', 'odd'), data['sectors'], strict=True):
        A = [[box(e) for e in row] for row in sector['quadrature_matrix']]
        if (sector['parity'] != parity or sector['dimension'] != n//2 or len(A) != n//2
                or any(len(row) != n//2 for row in A)
                or any(not A[i][j].overlaps(A[j][i]) for i in range(n//2) for j in range(i))):
            raise ValueError('comparison shape or symmetry mismatch')
        count, pivots = inertia(A, s+quad)
        counts.append(count)
        records.append({'parity': parity, 'count_below_shift': count,
                        'pivots': [endpoints(p) for p in pivots]})
    return s-coupling-tail, counts, records


def close_cluster(lower, ritz, target, rank, upper, shift):
    """Exactly rank levels below any t between upper and outside_lower."""
    if type(rank) is not int or rank < 1:
        raise ValueError('positive cluster rank required')
    U = arb(upper)
    if not U.is_finite():
        raise ValueError('finite Ritz upper shift required')
    b, low_counts, low_records = lower_counts(lower, target, shift)
    high_counts, high_records = check_ritz(ritz, target, U)
    if sum(low_counts) != rank or high_counts != low_counts or not U < b:
        raise ArithmeticError('cluster rank, parity counts, or outer gap did not close')
    return {'C': target, 'rank': rank, 'parity_ranks': dict(zip(('even', 'odd'), low_counts)),
            'cluster_top_upper': endpoints(U), 'outside_lower': endpoints(b),
            'outer_gap_lower': endpoints(b-U),
            'separator': endpoints((U+b)/2), 'comparison_shift': shift,
            'lower_inertia': low_records, 'ritz_inertia': high_records,
            'scope': 'Full operator via written min--max, form identity and infinite-complement bounds; not a counting law or positivity of the cluster.'}


def energy_cluster_mass(mu, lower, outside):
    """For a unit trial: ||(I-P_cluster)f||^2 <= (mu-ell)/(b-ell)."""
    mu, ell, b = map(arb, (mu, lower, outside))
    if not all(x.is_finite() for x in (mu, ell, b)):
        raise ValueError('finite energy and spectral bounds required')
    mu, ell, b = arb(mu.upper()), arb(ell.lower()), arb(b.lower())
    if not ell <= mu < b:
        raise ArithmeticError('lower <= energy < outside lower required')
    return (mu-ell)/(b-ell)


def ground_trial(matrix):
    """Select exact decimal coefficients, then certify the full form quotient."""
    with mp.workdps(85):
        def mid(x):
            q = x.mid().fmpq()
            return mp.mpf(str(q.numerator))/mp.mpf(str(q.denominator))
        _, V = mp.eigsy(mp.matrix([[mid(x) for x in row] for row in matrix]))
        exact = [mp.nstr(V[j, 0], 75) for j in range(len(matrix))]
    v = [arb(x) for x in exact]
    norm = sum((x*x for x in v), arb(0))
    if not norm > 0:
        raise ArithmeticError('nonzero witness required')
    mu = sum((v[i]*matrix[i][j]*v[j] for i in range(len(v)) for j in range(len(v))), arb(0))/norm
    if not mu.is_finite():
        raise ArithmeticError('witness quotient unresolved')
    return {'exact_even_cosine_coefficients': exact, 'norm_squared': endpoints(norm),
            'full_form_rayleigh': endpoints(mu),
            'interpretation': 'Rayleigh quotient of an explicit finite trial in the full form domain; an upper bound, not a full ground eigenvalue enclosure.'}


def residual_cluster_angle(residual_hs, cluster_top_upper, outside_lower):
    """Hilbert--Schmidt subspace bound eps/(b-U), independent of internal gaps.

    Requires orthonormal trial columns V, Hermitian B with B<=UI and the full
    residual AV-VB, not its compression. The output may exceed one.
    """
    eps, U, b = map(arb, (residual_hs, cluster_top_upper, outside_lower))
    if not all(x.is_finite() for x in (eps, U, b)) or not eps >= 0 or not U < b:
        raise ValueError('nonnegative full residual and positive outer separation required')
    return arb(eps.upper())/(arb(b.lower())-arb(U.upper()))


def ritz_input(cutoff):
    """Cache generated integration balls; certificate records their file hash."""
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT/f'ritz_C{cutoff.replace("/", "_")}.json'
    if path.exists():
        data = json.loads(path.read_text())
        check_ritz(data, cutoff, arb('1/2'))
        return data, path
    even, odd, powers = actual_ritz(cutoff, 16)
    data = {'status': 'geometric_ritz_blocks', 'C': cutoff, 'modes': 16, 'bits': 512,
            'active_prime_powers': [list(x) for x in powers],
            'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                            ('full_cluster_certificate.py', 'certified_weil.py', 'weil_matrix.py')},
            'sectors': [{'parity': parity, 'matrix': [[endpoints(x) for x in row] for row in matrix]}
                        for parity, matrix in zip(('even', 'odd'), (even, odd))]}
    path.write_text(json.dumps(data, indent=2)+'\n')
    return data, path


def generate():
    OUT.mkdir(parents=True, exist_ok=True)
    configs = [('2', 'two', 3, '67/100', '9/10'),
               ('3', 'three', 5, '7/10', '37/50'),
               ('16/5', None, 5, '2/5', '37/50')]
    results = []
    with ctx.workprec(512):
        for C, name, rank, upper, shift in configs:
            comparison = BASE/f'band128_{name}_lower_operator.json' if name else OUT/'C3p2_lower_operator.json'
            replay = BASE/f'band128_{name}_replay.json' if name else OUT/'C3p2_replay.json'
            require_replay(replay, comparison)
            if name is None and json.loads(replay.read_text()).get('wrapper_sha256') != sha256(Path(__file__).with_name('cluster_comparison_replay.py')):
                raise ValueError('512-bit replay wrapper provenance mismatch')
            ritz, path = ritz_input(C)
            even = [[box(x) for x in row] for row in ritz['sectors'][0]['matrix']]
            checked = close_cluster(json.loads(comparison.read_text()), ritz, C, rank, upper, shift)
            checked.update({'proposed_rank': proposed_rank(C), 'rank_proposal_assumed': False,
                            'input_sha256': {str(p): sha256(p) for p in (comparison, replay, path)}})
            checked['small_rayleigh_witness'] = ground_trial(even)
            results.append(checked)
            print('full cluster closed:', C, rank, checked['parity_ranks'], flush=True)
    return {'status': 'certified_fixed_support_full_clusters', 'results': results,
            'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                             ('full_cluster_certificate.py', 'certified_weil.py', 'weil_matrix.py',
                              'compact_window_certificate.py', 'full_ground_fourier.py', 'verify_window_positivity.py',
                              'cluster_comparison_replay.py')},
            'rh_proved': False, 'counting_law_proved': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    result = generate()
    (OUT/'full_clusters.json').write_text(json.dumps(result, indent=2)+'\n')
