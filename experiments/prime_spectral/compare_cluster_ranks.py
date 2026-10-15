"""Test alternative cluster boundaries instead of assuming a staircase."""
import json
from pathlib import Path
from flint import ctx
from full_cluster_certificate import OUT, BASE, close_cluster
from full_ground_fourier import require_replay, sha256


def generate():
    rows = []
    with ctx.workprec(512):
        for C, name, U, s in [('3', 'three', '11/100', '63/100'),
                              ('16/5', None, '1/40', '3/10')]:
            low = BASE/f'band128_{name}_lower_operator.json' if name else OUT/'C3p2_lower_operator.json'
            replay = BASE/f'band128_{name}_replay.json' if name else OUT/'C3p2_replay.json'
            ritz = OUT/f'ritz_C{C.replace("/", "_")}.json'
            require_replay(replay, low)
            row = close_cluster(json.loads(low.read_text()), json.loads(ritz.read_text()), C, 4, U, s)
            row['input_sha256'] = {str(p): sha256(p) for p in [low, replay, ritz]}
            rows.append(row)
    return {'status': 'certified_alternative_rank_four_clusters', 'results': rows,
            'source_sha256': {n: sha256(Path(__file__).with_name(n)) for n in
                             ['compare_cluster_ranks.py', 'full_cluster_certificate.py']},
            'interpretation': 'Ranks depend on the chosen separator. At C=3 the fifth full eigenvalue is >0.629, so the proposed rank-five block is not entirely near zero at a 0.1 threshold.'}


if __name__ == '__main__':
    (OUT/'alternative_rank_four.json').write_text(json.dumps(generate(), indent=2)+'\n')
