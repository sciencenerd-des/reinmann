"""Fail-closed provenance and outcome check for the 13 October calibration round.

Numerical replay is in test_control_calibration.py and replay_control_atlases.py.
This verifier binds those results to the compact data and paper artifacts.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXPERIMENTS = ROOT/'experiments/prime_spectral'
OUT = ROOT/'research/prime_spectral/verification_2026_10_13_calibration'
MANIFEST = OUT/'manifest.json'


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024*1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def resolve(path, source=False):
    p = Path(path)
    return (EXPERIMENTS if source else ROOT)/p if not p.is_absolute() else p


def run():
    hashes = {}
    declarations = 0

    def bind(path, expected):
        nonlocal declarations
        path = path.resolve()
        if path not in hashes:
            if not path.is_file():
                raise ValueError(f'missing declared input: {path}')
            hashes[path] = sha(path)
        if hashes[path] != expected:
            raise ValueError(f'hash mismatch: {path}')
        declarations += 1

    def visit(node):
        if isinstance(node, list):
            for child in node:
                visit(child)
        elif isinstance(node, dict):
            for key in ['source_sha256', 'input_sha256']:
                for name, expected in node.get(key, {}).items():
                    bind(resolve(name, key == 'source_sha256'), expected)
            if 'file' in node and 'sha256' in node:
                bind(resolve(node['file']), node['sha256'])
            if 'compacted_mathematical_core_sha256' in node:
                core = json.dumps(node['sectors'], sort_keys=True, separators=(',', ':')).encode()
                if hashlib.sha256(core).hexdigest() != node['compacted_mathematical_core_sha256']:
                    raise ValueError('compacted mathematical core changed')
            for child in node.values():
                visit(child)

    files = sorted(p for p in OUT.rglob('*.json') if p != MANIFEST)
    for path in files:
        visit(json.loads(path.read_text()))
    compaction = json.loads((OUT/'storage_compaction.json').read_text())
    for event in compaction['events']:
        bind(resolve(event['file']), event['compacted_sha256'])
    snapshot = OUT/'source_snapshots/control_window_calibration_initial.py'
    bind(snapshot, compaction['snapshot_sha256'])

    dataset = json.loads((OUT/'calibration_dataset.json').read_text())
    if len(dataset['controls']) != 7 or not dataset['q17_prediction_assessment']['negative_endpoint_in_prediction_interval']:
        raise ValueError('calibration or recorded prediction assessment incomplete')
    for row in dataset['controls']:
        summary = next(r for r in files if r.name == 'search_N192_2048bits.json'
                       and json.loads(r.read_text())['negative_certificate_C'] == row['negative_certificate_C'])
        if json.loads(summary.read_text())['status'] != 'finite_family_search_with_certified_negative_endpoint':
            raise ValueError('negative witness summary unresolved')
    replay = json.loads((OUT/'atlas_replays.json').read_text())
    if replay['status'] != 'seven_new_atlases_replayed' or len(replay['controls']) != 7:
        raise ValueError('new atlas replay incomplete')
    if any(r['status'] != 'all_contours_and_root_gates_replayed' for r in replay['controls']):
        raise ValueError('failed atlas replay')
    attribution = json.loads((OUT/'zero_attribution.json').read_text())
    if len(attribution['controls']) != 7:
        raise ValueError('finite attribution incomplete')
    symbol = json.loads((OUT/'symbol_comparison.json').read_text())
    if symbol['status'] != 'certified_oscillatory_symbol_tails_and_actual_dips' or len(symbol['windows']) != 4:
        raise ValueError('symbol comparison incomplete')
    test_log = (OUT/'tests.log').read_text()
    if 'Ran 9 tests' not in test_log or not test_log.rstrip().endswith('OK'):
        raise ValueError('nine-test suite not recorded as passing')
    build_log = (OUT/'paper_build.log').read_text()
    if 'Writing' not in build_log or 'dh_controls_paper.pdf' not in build_log or 'error:' in build_log.lower():
        raise ValueError('paper build did not complete')

    artifacts = files + [
        p for p in OUT.rglob('*') if p.is_file() and p.suffix != '.json'
    ] + [
        ROOT/'paper/dh_controls_paper.tex', ROOT/'paper/dh_controls_paper.pdf',
        ROOT/'paper/dh_controls_tables.tex', ROOT/'paper/dh_controls_attribution_table.tex',
        ROOT/'paper/figures/dh_controls_calibration.pdf',
        ROOT/'paper/figures/dh_controls_calibration.png',
        ROOT/'paper/DH_CONTROLS_READINESS.md',
        ROOT/'research/prime_spectral/CALIBRATION_AND_SYMBOL_ROUND_2026_10_13.md',
        ROOT/'research/RESEARCH_STATUS_2026_10_11.md', Path(__file__),
    ]
    result = {'status': 'calibration_round_provenance_and_outcomes_verified',
              'json_records_checked': len(files), 'hash_declarations_checked': declarations,
              'distinct_declared_inputs': len(hashes), 'new_tests_passed': 9,
              'new_atlases_replayed': 7, 'calibration_controls': 7,
              'certified_symbol_tails': 4, 'compacted_cores_checked': len(compaction['events']),
              'artifacts_sha256': {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(artifacts))},
              'declared_inputs_sha256': {str(p.relative_to(ROOT)): digest for p, digest in sorted(hashes.items())},
              'scope': 'Provenance and recorded outcome check, supplementary to numerical replay. No full-window positivity, universal exchange theorem, independent backend validation, submission, or RH proof.'}
    MANIFEST.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], len(files), 'JSON records;', declarations, 'hash declarations;',
          len(compaction['events']), 'unchanged compacted cores', flush=True)


if __name__ == '__main__':
    run()
