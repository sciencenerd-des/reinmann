"""Cost and matched-coordinate diagnostics; never a full-window certificate."""
import json
from pathlib import Path
import time
import mpmath as mp
from flint import arb, ctx
from certified_weil import endpoints, entry, inertia
from closed_weil import entry_closed, tail_bound
from compact_window_certificate import bounds
from full_ground_fourier import sha256
from weil_matrix import prime_powers

OUT = Path('research/prime_spectral/verification_2026_10_12_sector')


def matrix(C, modes=64):
    c = arb(2).exp() if C == 'exp(2)' else arb(C)
    L = c.log()
    pp = [(q, p) for q, p in prime_powers(int(c.ceil().fmpq())) if arb(q) < c]
    cell = lambda m, n: entry_closed(m, n, L, pp, 200)
    b = [arb(0)]+[n*cell(n, 0) for n in range(1, modes+1)]
    E = [[arb(0) for _ in range(modes+1)] for _ in range(modes+1)]
    O = [[arb(0) for _ in range(modes)] for _ in range(modes)]
    E[0][0] = cell(0, 0)
    for n in range(1, modes+1):
        E[0][n] = E[n][0] = arb(2).sqrt()*b[n]/n
        d, e = cell(n, n), cell(n, -n)
        E[n][n], O[n-1][n-1] = d+e, d-e
        for m in range(1, n):
            E[m][n] = E[n][m] = 2*(n*b[n]-m*b[m])/(n*n-m*m)
            O[m-1][n-1] = O[n-1][m-1] = 2*(m*b[n]-n*b[m])/(n*n-m*m)
    # Independent integration checks catch both parity and normalization errors.
    checks = []
    for m, n in [(0, 0), (7, 0), (7, 7), (7, -7)]:
        direct, closed = entry(m, n, L, pp, c), cell(m, n)
        if not direct.overlaps(closed):
            raise ArithmeticError('closed entry disagrees with direct integration')
        checks.append({'indices': [m, n], 'direct': endpoints(direct), 'closed': endpoints(closed)})
    return c, L, pp, E, O, checks


def midpoint(A):
    def f(x):
        q = x.mid().fmpq()
        return mp.mpf(str(q.numerator))/mp.mpf(str(q.denominator))
    return mp.matrix([[f(x) for x in row] for row in A])


def schur(A, k, t):
    H, B, D = A[:k, :k], A[k:, :k], A[k:, k:]
    for j in range(k):
        H[j, j] -= t
    for j in range(D.rows):
        D[j, j] -= t
    return H-B.T*mp.lu_solve(D, B) if B.cols == 1 else H-B.T*(D**-1)*B


def run():
    OUT.mkdir(parents=True, exist_ok=True)
    data, matrices, eigensystems = [], {}, {}
    with ctx.workprec(768), mp.workdps(180):
        for C in ['13/2', '7', 'exp(2)', '19/2', '10']:
            start = time.monotonic()
            c, L, pp, E, O, checks = matrix(C)
            sectors = []
            matrices[C], eigensystems[C] = [], []
            for parity, A in [('even', E), ('odd', O)]:
                count, pivots = inertia(A, '3/10')
                positive_count, positive_pivots = inertia(A, 0)
                M = midpoint(A)
                vals, vecs = mp.eigsy(M)
                matrices[C].append(M)
                eigensystems[C].append((vals, vecs))
                sectors.append({'parity': parity, 'count_below_0p3': count,
                    'finite_negative_count': positive_count,
                    'finite_positive_pivots': [endpoints(x) for x in positive_pivots],
                    'threshold_pivots': [endpoints(x) for x in pivots],
                    'approximate_eigenvalues': [mp.nstr(x, 30) for x in vals]})
            mass = sum((2*arb(p).log()/arb(q).sqrt() for q, p in pp), arb(0))
            cutoff = 4
            while not (arb(cutoff)/(2*arb.pi())).log()-1/arb(cutoff)-mass > arb('1/2'):
                cutoff *= 2
            count = 2
            while count < 16384:
                beta, quad, coupling, tail, _ = bounds(L/2, cutoff, count, 160, pp)
                if coupling+tail < arb('1e-10'):
                    break
                count += 2
            if count == 16384:
                count -= 2  # Last dimension actually evaluated at the cap.
            result = {'C': C, 'C_ball': endpoints(c), 'modes': 64, 'bits': 768,
                'sectors': sectors, 'entry_checks': checks,
                'active_prime_powers': pp, 'closed_entry_tail': endpoints(tail_bound(L, 200)),
                'existing_comparison_cost': {'frequency_cutoff': cutoff, 'polynomial_count': count,
                    'target_coupling_plus_tail': '1e-10',
                    'coupling_budget_closed': bool(coupling+tail < arb('1e-10')),
                    'beta': endpoints(beta), 'coupling': endpoints(coupling),
                    'tail': endpoints(tail), 'quadrature_error_order160': endpoints(quad)},
                'seconds': time.monotonic()-start,
                'scope': 'Inertia is certified only for the finite Fourier section. Eigenvalues are midpoint diagnostics. Full omitted-mode control and exact spectral-cluster positivity are not supplied.'}
            data.append(result)
            print(C, 'finite counts', [s['count_below_0p3'] for s in sectors],
                  'comparison dimensions', count, 'seconds', result['seconds'], flush=True)
            (OUT/'window_block_pilot.json').write_text(json.dumps({'status': 'finite_sections_and_cost_pilot', 'windows': data}, indent=2)+'\n')
        matched = []
        for left, right in [('13/2', '7'), ('19/2', '10')]:
            for p, parity in enumerate(['even', 'odd']):
                vals, V = eigensystems[left][p]
                k = sum(x < mp.mpf('.3') for x in vals)
                # Fixed dilation coordinates on [-1/2,1/2], then the complete
                # spectral basis of the LEFT finite section for both windows.
                A, B = V.T*matrices[left][p]*V, V.T*matrices[right][p]*V
                t = mp.mpf(-1)  # Uniformly stable finite complement, explicit shift.
                S, T = schur(A, k, t), schur(B, k, t)
                delta = T-S
                _, singular, _ = mp.svd(delta)
                matched.append({'left_C': left, 'right_C': right, 'parity': parity,
                    'retained_dimension': k, 'shift': '-1',
                    'correction_singular_values': [mp.nstr(x, 30) for x in singular],
                    'relative_correction_Frobenius': mp.nstr(mp.norm(delta)/mp.norm(S), 30),
                    'scope': 'Numerical finite-section Schur diagnostic in the fixed left spectral basis. No conclusion about the exact full effective operator or every possible adapted basis.'})
        payload = {'status': 'finite_sections_and_matched_Schur_diagnostics',
            'windows': data, 'matched_blocks': matched,
            'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                ['window_block_pilot.py', 'closed_weil.py', 'compact_window_certificate.py', 'certified_weil.py']}}
        (OUT/'window_block_pilot.json').write_text(json.dumps(payload, indent=2)+'\n')
    return payload


if __name__ == '__main__':
    run()
