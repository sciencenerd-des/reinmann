"""Replay condensation and check selected high ranks by complementary minors."""
import json
from pathlib import Path
from flint import arb, arb_mat, ctx
from certified_weil import endpoints
from dh_high_rank_scan import OUT, condensate
from full_ground_fourier import sha256
from threshold_ground_gap import box


def replay():
    path = OUT/'dh_rank430-520_shift0-200_32768bits.json'
    data = json.loads(path.read_text())
    coeff_path = Path(data['coefficient_file'])
    if sha256(coeff_path) != data['coefficient_sha256']:
        raise ValueError('coefficient provenance mismatch')
    with ctx.workprec(32768):
        mu = [box(x) for x in json.loads(coeff_path.read_text())['coefficients']]
        mu[0] = arb(1)
        scaled = [x*arb(100)**n for n, x in enumerate(mu)]
        result = condensate(scaled, 520, 200, 430)
        if result['sign_digest_sha256'] != data['sign_digest_sha256']:
            raise ArithmeticError('condensation replay sign digest mismatch')
        # If h_n=[z^n]1/f(-z), Jacobi's complementary-minor identity gives
        # det(a_{s+i-j})_(r x r) = det(h_{r+i-j})_(s x s).
        # This computes the selected high-rank minors by a different recurrence
        # and determinants of size at most 20, with no condensation divisions.
        h = [arb(1)]
        for n in range(1, 541):
            h.append(sum(((-1)**(j+1)*scaled[j]*h[n-j] for j in range(1, n+1)), arb(0)))
        checks = []
        for rank in [430, 435, 436, 437, 480, 520]:
            for shift in [1, 2, 5, 20]:
                d = arb_mat([[h[rank+i-j] for j in range(shift)] for i in range(shift)]).det()
                if not d > 0:
                    raise ArithmeticError('independent high-rank complementary-minor sign failed')
                checks.append({'rank': rank, 'shift': shift,
                               'complementary_determinant': endpoints(d)})
        payload = {'status': 'condensation_replayed_and_24_high_rank_complementary_minors_positive',
            'bits': 32768, 'scan_sha256': sha256(path),
            'sign_digest_sha256': result['sign_digest_sha256'], 'checks': checks,
            'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                ['replay_dh_high_rank.py', 'dh_high_rank_scan.py']},
            'scope': 'Same Arb coefficient input and backend; different determinant identity for selected cells. No global first failure, arbitrary-minor enumeration, or unbounded-shift claim.'}
    (OUT/'high_rank_replay.json').write_text(json.dumps(payload, indent=2)+'\n')
    print(payload['status'], flush=True)


if __name__ == '__main__':
    replay()
