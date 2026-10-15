"""Full residual and subspace angle for the C=3 rank-four trial cluster.

Both inversion parities, the complete cosine/sine prefix and all infinite
tails are included. Floating/multiprecision eigenvectors select exact decimal
columns only. A Gram gate and Arb residuals supply the certificate.
"""
import json
from pathlib import Path

import mpmath as mp
from flint import arb, ctx

from adjoint_fourier_certificate import sequence_bound, payload_hash
from certified_weil import endpoints, inertia
from full_cluster_certificate import OUT, residual_cluster_angle
from full_ground_fourier import sha256
from threshold_ground_gap import box


def tail_column(parity, v, b, prefix, B):
    """Triangle bound on the actual infinite action, not a finite projection."""
    N = len(v)-1 if parity == 'even' else len(v)
    if not prefix > N or not B > 0:
        raise ValueError('prefix above trial degree and positive sequence bound required')
    rho = 1-(arb(N)/(prefix+1))**2
    W = lambda power: 1/((2*power-1)*arb(prefix)**(2*power-1)).sqrt()
    if parity == 'even':
        boundary = v[0]+arb(2).sqrt()*sum(v[1:], arb(0))
        signed = sum((n*b[n]*v[n] for n in range(1, N+1)), arb(0))
        s2 = sum((n*n*abs(v[n]) for n in range(1, N+1)), arb(0))
        t3 = sum((n**3*abs(b[n]*v[n]) for n in range(1, N+1)), arb(0))
        # A_m v = sqrt(2) E_v b_m/m -2 T_1/m^2 + remainder.
        value = arb(2).sqrt()*abs(boundary)*B*W(1)+2*abs(signed)*W(2)
        value += 2*B*s2/rho*W(3)+2*t3/rho*W(4)
    elif parity == 'odd':
        signed = sum((b[n]*v[n-1] for n in range(1, N+1)), arb(0))
        s1 = sum((n*abs(v[n-1]) for n in range(1, N+1)), arb(0))
        t2 = sum((n*n*abs(b[n]*v[n-1]) for n in range(1, N+1)), arb(0))
        # A_m v = -2 T_0/m + b_m sum 2n v_n/[m^2(1-n^2/m^2)]
        #         - sum 2n^2 b_n v_n/[m^3(1-n^2/m^2)].
        value = 2*abs(signed)*W(1)+2*B*s1/rho*W(2)+2*t2/rho*W(3)
    else:
        raise ValueError('even or odd parity required')
    return value


def select_columns(A, retained):
    with mp.workdps(85):
        def mid(x):
            q = x.mid().fmpq()
            return mp.mpf(str(q.numerator))/mp.mpf(str(q.denominator))
        vals, V = mp.eigsy(mp.matrix([[mid(x) for x in row] for row in A]))
        return [mp.nstr(vals[j], 75) for j in range(retained)], [
            [mp.nstr(V[i,j], 75) for i in range(len(A))] for j in range(retained)]


def certify_columns(A, action_prefix, parity, exact, shifts, b, prefix, B, upper):
    v = [[arb(x) for x in col] for col in exact]
    n, k = len(A), len(v)
    if (not k or any(len(col) != n for col in v) or len(shifts) != k
            or any(len(row) != n for row in action_prefix)):
        raise ValueError('consistent trial columns and full action prefix required')
    G = [[sum((v[i][m]*v[j][m] for m in range(n)), arb(0)) for j in range(k)] for i in range(k)]
    H = [[sum((v[i][m]*A[m][l]*v[j][l] for m in range(n) for l in range(n)), arb(0))
          for j in range(k)] for i in range(k)]
    gram_error = max(sum((abs(G[i][j]-(1 if i == j else 0)) for j in range(k)), arb(0)).upper() for i in range(k))
    gram_lower = 1-arb(gram_error)
    if not gram_lower > 0:
        raise ArithmeticError('trial Gram lower bound failed')
    count, pivots = inertia([[arb(upper)*G[i][j]-H[i][j] for j in range(k)] for i in range(k)])
    if count:
        raise ArithmeticError('trial subspace Rayleigh upper gate failed')
    rows, hs_sq = [], arb(0)
    start = 0 if parity == 'even' else 1
    for col, shift in zip(v, shifts, strict=True):
        residual = [sum((row[j]*col[j] for j in range(n)), arb(0))
                    -(arb(shift)*col[m-start] if m-start < n else 0)
                    for m, row in enumerate(action_prefix, start=start)]
        prefix_sq = sum((x*x for x in residual), arb(0))
        tail = tail_column(parity, col, b, prefix, B)
        hs_sq += prefix_sq+tail*tail
        rows.append({'full_residual_prefix_squared': endpoints(prefix_sq),
                     'infinite_residual_tail_norm_upper': endpoints(tail)})
    return {'parity': parity, 'retained': k, 'exact_columns': exact, 'exact_shifts': shifts,
            'gram_lower': endpoints(gram_lower), 'rayleigh_upper_shift': upper,
            'rayleigh_upper_pivots': [endpoints(p) for p in pivots],
            'full_residual_HS_squared_upper': endpoints(hs_sq), 'columns': rows}


def generate():
    ritz_path = OUT/'ritz_C3.json'
    block_path = OUT/'alternative_rank_four.json'
    seq_path = Path('research/prime_spectral/verification_2026_10_11_boundary_moment/matrix_C3_N32_M256.json')
    ritz, seq = json.loads(ritz_path.read_text()), json.loads(seq_path.read_text())
    if seq['payload_sha256'] != payload_hash(seq):
        raise ValueError('sequence payload mismatch')
    for name, h in seq['source_sha256'].items():
        if h != sha256(Path(__file__).with_name(name)):
            raise ValueError('sequence provenance mismatch')
    for name, h in ritz['source_sha256'].items():
        if h != sha256(Path(__file__).with_name(name)):
            raise ValueError('Ritz provenance mismatch')
    block = next(x for x in json.loads(block_path.read_text())['results'] if x['C'] == '3')
    for path, h in block['input_sha256'].items():
        if sha256(Path(path)) != h:
            raise ValueError('full cluster provenance mismatch')
    results = []
    with ctx.workprec(512):
        b = [box(x) for x in seq['b_sequence']]
        P = seq['prefix']; B = sequence_bound(3)
        if any(not abs(x) < B for x in b):
            raise ArithmeticError('all-mode sequence bound failed a known entry')
        for sector in ritz['sectors']:
            parity = sector['parity']
            A = [[box(x) for x in row] for row in sector['matrix']]
            n = len(A); N = n-1 if parity == 'even' else n
            prefix = [row[:] for row in A]
            for m in range(N+1, P+1):
                if parity == 'even':
                    row = [arb(2).sqrt()*b[m]/m]+[
                        2*(m*b[m]-j*b[j])/(m*m-j*j) for j in range(1, N+1)]
                else:
                    row = [2*(j*b[m]-m*b[j])/(m*m-j*j) for j in range(1, N+1)]
                prefix.append(row)
            shifts, exact = select_columns(A, 2)
            results.append(certify_columns(A, prefix, parity, exact, shifts, b, P, B, '11/100'))
        lower = min(arb(box(row['gram_lower']).lower()) for row in results)
        residual = sum((box(row['full_residual_HS_squared_upper']) for row in results), arb(0)).sqrt()/lower.sqrt()
        outside = arb(box(block['outside_lower']).lower())
        angle = residual_cluster_angle(residual, '11/100', outside)
        return {'status': 'certified_C3_rank_four_full_residual_and_angle', 'C': 3,
                'rank': 4, 'bits': 512, 'trial_modes': 16, 'action_prefix': P,
                'sectors': results, 'orthonormalized_full_residual_HS_upper': endpoints(residual),
                'outside_lower': endpoints(outside), 'trial_block_upper': '11/100',
                'projection_norm_distance_upper': endpoints(angle),
                'input_sha256': {str(p): sha256(p) for p in [ritz_path, block_path, seq_path]},
                'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                                 ['full_cluster_residual.py','full_cluster_certificate.py',
                                  'adjoint_fourier_certificate.py','certified_weil.py']},
                'scope': 'Actual full residual and rank-four projector angle via written operator/domain and spectral arguments; no internal ground gap, Xi identification or RH proof.'}


if __name__ == '__main__':
    result = generate()
    (OUT/'C3_rank_four_full_residual.json').write_text(json.dumps(result, indent=2)+'\n')
    print('full rank-four projection angle:', box(result['projection_norm_distance_upper']))
