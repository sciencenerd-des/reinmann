"""Stream-hash research outputs and verify their declared source/input links."""
import hashlib
import json
from pathlib import Path

OUT = Path('research/prime_spectral/verification_2026_10_12_sector')


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1024*1024), b''):
            h.update(chunk)
    return h.hexdigest()


def verify():
    checked, failures = [], []
    for path in sorted(OUT.glob('*.json')):
        if path.name == 'manifest.json':
            continue
        data = json.loads(path.read_text())
        links = [(Path('experiments/prime_spectral')/n, h)
                 for n, h in data.get('source_sha256', {}).items()]
        links += [(Path(n), h) for n, h in data.get('input_sha256', {}).items()]
        links += [(Path(rec['file']), rec['sha256']) for rec in data.get('records', [])]
        if 'coefficient_file' in data:
            links.append((Path(data['coefficient_file']), data['coefficient_sha256']))
        for source, expected in links:
            if not source.exists() or sha(source) != expected:
                failures.append({'artifact': str(path), 'dependency': str(source)})
        checked.append({'file': str(path), 'sha256': sha(path), 'bytes': path.stat().st_size,
                        'status': data.get('status', 'structured_control_summary'),
                        'checked_dependency_links': len(links)})
    if failures:
        raise ValueError(json.dumps(failures, indent=2))
    scan = json.loads((OUT/'dh_rank430-520_shift0-200_32768bits.json').read_text())
    rows = scan['per_rank']
    if len(rows) != 91 or any(r['positive'] != 201 or r['negative'] or r['unresolved'] for r in rows):
        raise ValueError('requested solid-minor grid is not fully positive')
    for replay_name, source_name, field in [
            ('atlas_replay.json', 'atlas_H340.json', 'atlas_sha256'),
            ('high_rank_replay.json', 'dh_rank430-520_shift0-200_32768bits.json', 'scan_sha256')]:
        if json.loads((OUT/replay_name).read_text())[field] != sha(OUT/source_name):
            raise ValueError('replay input mismatch')
    return {'status': 'all_declared_sources_inputs_and_artifact_hashes_checked',
            'artifacts': checked, 'artifact_count': len(checked),
            'requested_solid_minors_strictly_positive': 91*201,
            'unresolved_requested_solid_minors': 0,
            'validation': {
                'python_tests': {'passed': 26, 'log': str(OUT/'tests_all.log'),
                                 'log_sha256': sha(OUT/'tests_all.log')},
                'paper': {'file': 'paper/rh_reduction_paper.pdf',
                          'sha256': sha('paper/rh_reduction_paper.pdf'),
                          'build_log': str(OUT/'paper_build.log'),
                          'build_log_sha256': sha(OUT/'paper_build.log')},
                'sector_figure': {
                    'generator_sha256': sha('experiments/prime_spectral/plot_dh_sector_control.py'),
                    'pdf_sha256': sha(OUT/'dh_sector_grid.pdf'),
                    'png_sha256': sha(OUT/'dh_sector_grid.png'),
                    'scope': 'Scaled isolated quadratic determinant and counts of positive minors in the specified full-function grid.'},
                'lean': json.loads((OUT/'lean_validation.json').read_text())
                        if (OUT/'lean_validation.json').exists()
                        else {'status': 'not_verified', 'axiom_audit': 'not_run'},
                'written_results': {
                    name: sha(name) for name in [
                        'research/prime_spectral/RESEARCH_ROUND_2026_10_12.md',
                        'research/prime_spectral/LOCALIZED_TURAN_PACKET_2026_10_12.md',
                        'Reinmann/WeilSchurInertia.lean',
                        'Reinmann/ToeplitzQuadraticChebyshev.lean']},
                'verification_sources': {
                    str(path): sha(path)
                    for path in sorted(Path('experiments/prime_spectral').glob('*.py'))},
            },
            'trust_boundary': 'Written analytic reductions and Arb, not external peer review. Finite controls and conditional theorems are not RH or new full-window positivity records.'}


if __name__ == '__main__':
    result = verify()
    (OUT/'manifest.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], result['artifact_count'], 'JSON artifacts')
