"""Replay C=3 degree-32 full cluster residual and fixed-threshold count."""
import json
from pathlib import Path

from flint import arb, ctx

from adjoint_fourier_certificate import payload_hash, sequence_bound
from certified_weil import endpoints
from full_cluster_certificate import BASE, actual_ritz, close_cluster, check_ritz, residual_cluster_angle
from full_cluster_residual import certify_columns, select_columns
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT = Path('research/prime_spectral/verification_2026_10_12_remaining')
SEQUENCE = Path('research/prime_spectral/verification_2026_10_11_boundary_moment/matrix_C3_N32_M256.json')


def generate():
    ritz_path = OUT/'ritz_C3_N32.json'
    lower_path = BASE/'band128_three_lower_operator.json'
    if not ritz_path.exists():
        OUT.mkdir(parents=True, exist_ok=True)
        with ctx.workprec(512):
            even, odd, powers = actual_ritz('3', 32)
            data = {'status': 'geometric_ritz_blocks', 'C': '3', 'modes': 32,
                    'bits': 512, 'active_prime_powers': powers,
                    'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                                     ['full_cluster_certificate.py', 'certified_weil.py', 'weil_matrix.py']},
                    'sectors': [{'parity': parity,
                                 'matrix': [[endpoints(x) for x in row] for row in A]}
                                for parity, A in [('even', even), ('odd', odd)]]}
        ritz_path.write_text(json.dumps(data, indent=2)+'\n')
    ritz = json.loads(ritz_path.read_text())
    seq = json.loads(SEQUENCE.read_text())
    if seq['payload_sha256'] != payload_hash(seq):
        raise ValueError('sequence payload mismatch')
    for n, h in seq['source_sha256'].items():
        if sha256(Path(__file__).with_name(n)) != h:
            raise ValueError('sequence source mismatch')
    with ctx.workprec(512):
        check_ritz(ritz, '3', '1/10')
        block = close_cluster(json.loads(lower_path.read_text()), ritz,
                              '3', 4, '1/10', '63/100')
        b = list(map(box, seq['b_sequence']))
        P, N = seq['prefix'], ritz['modes']
        if (N != 32 or P != 256 or len(b) != P+1
                or any(not abs(x) < sequence_bound(3) for x in b)):
            raise ValueError('expected validated C3 degree32 sequence')
        sectors = []
        for sector in ritz['sectors']:
            parity = sector['parity']
            A = [[box(x) for x in row] for row in sector['matrix']]
            prefix = [row[:] for row in A]
            for m in range(N+1, P+1):
                if parity == 'even':
                    row = [arb(2).sqrt()*b[m]/m]+[
                        2*(m*b[m]-n*b[n])/(m*m-n*n) for n in range(1, N+1)]
                else:
                    row = [2*(n*b[m]-m*b[n])/(m*m-n*n) for n in range(1, N+1)]
                prefix.append(row)
            shifts, exact = select_columns(A, 2)
            sectors.append(certify_columns(A, prefix, parity, exact, shifts,
                                           b, P, sequence_bound(3), '1/10'))
        g = min(arb(box(s['gram_lower']).lower()) for s in sectors)
        residual = sum((box(s['full_residual_HS_squared_upper'])
                        for s in sectors), arb(0)).sqrt()/g.sqrt()
        outside = arb(box(block['outside_lower']).lower())
        angle = residual_cluster_angle(residual, '1/10', outside)
        if not angle < arb('426/1000'):
            raise ArithmeticError('refined full angle did not close')
        return {'status': 'certified_C3_rank4_degree32_full_residual',
                'C': 3, 'rank': 4, 'trial_modes': N, 'action_prefix': P,
                'bits': 512, 'block': block, 'sectors': sectors,
                'full_normalized_residual_HS_upper': endpoints(residual),
                'projection_norm_distance_upper': endpoints(angle),
                'threshold_count': {'threshold': '1/10', 'count': 4,
                                    'proposed_staircase_count': 5},
                'input_sha256': {str(p): sha256(p) for p in
                                 [ritz_path, lower_path, SEQUENCE]},
                'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                                 ['refine_cluster.py', 'full_cluster_residual.py',
                                  'full_cluster_certificate.py', 'adjoint_fourier_certificate.py']},
                'scope': 'Full operator min-max plus actual action and infinite tail. The exact staircase fails at threshold 0.1; no all-support asymptotic is proved.'}


if __name__ == '__main__':
    result = generate()
    (OUT/'C3_N32_full_cluster.json').write_text(json.dumps(result, indent=2)+'\n')
    print('full projector angle', box(result['projection_norm_distance_upper']))
    print('N_3(0.1)=4, proposed count=5')
