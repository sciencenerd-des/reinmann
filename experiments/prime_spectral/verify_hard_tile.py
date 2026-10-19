"""Check the single hard-tile evidence closure; Lean replay is separate."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from time_hard_tile import SHARED, CENTRE

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'research/prime_spectral/verification_2026_10_19_hard_tile'
BASE = ROOT / 'research/prime_spectral/verification_2026_10_18_degree8/manifest.json'
PIN = '12697383ca3164e206ac9d8a71738bcbdf9bac07'
REFRESHED = ('Reinmann.lean', 'Reinmann/AxiomAudit.lean', 'scripts/verify_axiom_clean.sh')
MODULES = ('CertifiedScalarExp', 'CertifiedTaylorInputs', 'HardTilePowerInputs',
           'HardTileFiniteIdentities', 'HardTileFiniteJets', 'TaylorDerivativeTail',
           'HardTileXi')
SCRIPTS = ('degree8_scalar_certificates', 'degree8_model_generator',
           'generate_hard_tile_xi', 'time_hard_tile', 'test_axiom_guard_allowlist',
           'verify_hard_tile')
REPORT = ROOT / 'research/prime_spectral/XI_HARD_TILE_2026_10_19.md'


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def check(record):
    bound = {}
    base = json.loads(BASE.read_text())
    assert len(base['artifacts_sha256']) == 1223
    for name, expected in base['artifacts_sha256'].items():
        path = OUT / 'historical_1269738' / name if name in REFRESHED else ROOT / name
        assert sha(path) == expected, name
        bound[path] = expected
    for name in REFRESHED:
        historical = OUT / 'historical_1269738' / name
        assert hashlib.sha256(subprocess.check_output(
            ['git', 'show', PIN + ':' + name], cwd=ROOT)).hexdigest() == sha(historical)
        bound[ROOT / name] = sha(ROOT / name)
    umbrella = (ROOT / 'Reinmann.lean').read_text()
    declarations = []
    for module in MODULES:
        path = ROOT / 'Reinmann' / (module + '.lean')
        source = path.read_text()
        assert 'import Reinmann.' + module in umbrella
        assert not re.search(r'\b(native_decide|sorry|admit|sorryAx|axiom)\b', source)
        declarations += ['Reinmann.' + module + '.' + name for name in
                         re.findall(r'^theorem\s+(\w+)', source, re.M)]
        bound[path] = sha(path)
    root_audit = (ROOT / 'Reinmann/AxiomAudit.lean').read_text()
    assert len(re.findall(r'^#print axioms', root_audit, re.M)) == 1203
    assert all('#print axioms ' + name in root_audit for name in declarations)
    audit_source = (OUT / 'AllNewAxioms.lean').read_text()
    assert re.findall(r'^#print axioms (.+)$', audit_source, re.M) == declarations
    audit_output = (OUT / 'all_new_axioms.log').read_text()
    assert 'error:' not in audit_output
    flat = re.sub(r'\n\s+', ' ', audit_output)
    lists = re.findall(r'depends on axioms: \[([^\]]*)\]', flat)
    empty = re.findall(r'does not depend on any axioms', flat)
    assert len(lists) + len(empty) == len(declarations)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert all(set(s.strip() for s in names.split(',')) <= allowed for names in lists)
    regressions = json.loads((OUT / 'guard_regressions/results.json').read_text())
    assert regressions['status'] == 'actual_guard_allowlist_regressions_passed'
    assert regressions['guard_sha256'] == sha(ROOT / 'scripts/verify_axiom_clean.sh')
    assert len(regressions['rows']) == 7
    assert all(row['actual'] == row['expected'] for row in regressions['rows'])
    guard = (OUT / 'axiom_guard.log').read_text()
    assert 'AXIOM-CLEAN:' in guard and 'FAIL:' not in guard
    assert 'all 1203 audited theorems depend only on' in guard
    build = (OUT / 'full_build.log').read_text()
    assert re.search(r'Build completed successfully \(\d+ jobs\)\.', build)
    assert 'error:' not in build
    assert not any(re.search(r'^import Reinmann$', p.read_text(), re.M)
                   for p in (ROOT / 'Reinmann').glob('*.lean'))
    timing = json.loads((OUT / 'replay/timings.json').read_text())
    assert timing['status'] == 'complete_single_hard_tile_proofs_replayed'
    assert timing['degree'] == 8 and timing['radius'] == '1/16'
    assert timing['centre'] == ['1/2', '14']
    assert [r['module'] for r in timing['rows']] == list(SHARED + CENTRE)
    shared = sum(r['seconds'] for r in timing['rows'] if r['kind'] == 'shared')
    centre = sum(r['seconds'] for r in timing['rows'] if r['kind'] == 'centre_specific')
    assert timing['shared_seconds'] == shared and timing['centre_specific_seconds'] == centre
    assert timing['complete_single_tile_seconds'] == shared + centre
    assert timing['conditional_35_centre_projection_seconds'] == shared + 35 * centre
    assert 'version 4.30.0' in timing['lean_version']
    assert 'XiAdaptiveTiles.adaptive_cover_nonzero' in (ROOT / 'Reinmann/HardTileXi.lean').read_text()
    for row in timing['rows']:
        assert row['returncode'] == 0 and row['seconds'] > 0
        assert row['source_sha256'] == sha(ROOT / 'Reinmann' / (row['module'] + '.lean'))
    assert not timing['zero_free_rectangle_certified'] and not timing['RH_proved']
    # Generators only propose rational disks; these read-only checks bind them
    # to the exact tables that Lean has checked.
    subprocess.run(['python3', 'experiments/prime_spectral/degree8_scalar_certificates.py',
                    '--all', '--check'], cwd=ROOT, check=True)
    subprocess.run(['uv', 'run', '--offline', '--with', 'python-flint==0.8.0',
                    '--python', '3.12', 'python',
                    'experiments/prime_spectral/degree8_model_generator.py',
                    '--both', '--check'], cwd=ROOT, check=True)
    subprocess.run(['python3', 'experiments/prime_spectral/generate_hard_tile_xi.py',
                    '--check'], cwd=ROOT, check=True)
    for script in SCRIPTS:
        path = ROOT / 'experiments/prime_spectral' / (script + '.py')
        bound[path] = sha(path)
    for path in OUT.rglob('*'):
        if path.is_file() and path.name != 'manifest.json':
            bound[path] = sha(path)
    for path in (BASE, REPORT):
        bound[path] = sha(path)
    result = {
        'status': 'actual_Xi_single_hard_tile_verified', 'base_commit': PIN,
        'centre': ['1/2', '14'], 'closed_disk_radius': '1/16', 'degree': 8,
        'derivative_bound': '9/5000', 'centre_error': '255423/1125899906842624',
        'certified_function': 'Reinmann.xiCompleted',
        'new_public_declarations': declarations,
        'total_audited_declarations': 1203,
        'new_public_declarations_standard_axioms_only': True,
        'adaptive_cover_nonzero_instantiated': True,
        'zero_free_rectangle_certified': False, 'RH_proved': False,
        'complete_single_tile_seconds': timing['complete_single_tile_seconds'],
        'artifacts_sha256': {str(p.relative_to(ROOT)): value
                             for p, value in sorted(bound.items())},
    }
    manifest = OUT / 'manifest.json'
    if record:
        if manifest.exists():
            raise FileExistsError('Immutable manifest already exists')
        manifest.write_text(json.dumps(result, indent=2) + '\n')
    else:
        assert json.loads(manifest.read_text()) == result
    print(result['status'], len(declarations), 'new public declarations;',
          len(bound), 'bound artifacts')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true')
    check(parser.parse_args().record)
