"""Verify the degree-eight arithmetic/shifted-Log checkpoint evidence closure.

This verifies bindings and recorded outcomes; it does not replace Lean replay.
The complete Xi hard tile is deliberately absent from the certified claims.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'research/prime_spectral/verification_2026_10_18_degree8'
BASE = ROOT/'research/prime_spectral/verification_2026_10_18_proved_jet_remainders/manifest.json'
PIN = '7a04cefc8c4c4e7641fb0c30fc830a1d3a29a43a'
ROOT_FILES = ('Reinmann.lean', 'Reinmann/AxiomAudit.lean')
MODULES = ('CertifiedTaylorModel', 'CertifiedComplexInputs', 'CertifiedTaylorComposition',
           'CertifiedHorner', 'HardTileLogInputs', 'HardTileGammaLog', 'HardTileGammaLogJet')
SCRIPTS = ('xi_degree8_probe', 'generate_hard_tile_log_inputs', 'generate_hard_tile_gamma_log',
           'generate_hard_tile_gamma_log_jet', 'time_degree8_components', 'verify_degree8_round')
REPORT = ROOT/'research/prime_spectral/XI_DEGREE8_ARITHMETIC_2026_10_18.md'


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def check(record=False):
    bound = {}
    base = json.loads(BASE.read_text())
    assert len(base['artifacts_sha256']) == 1195
    for name, expected in base['artifacts_sha256'].items():
        path = OUT/'historical_7a04cef'/name if name in ROOT_FILES else ROOT/name
        assert sha(path) == expected, name
        bound[path] = expected
    for name in ROOT_FILES:
        historical = OUT/'historical_7a04cef'/name
        assert hashlib.sha256(subprocess.check_output(['git','show',PIN+':'+name], cwd=ROOT)).hexdigest() == sha(historical)
    audit = (ROOT/ROOT_FILES[1]).read_text()
    umbrella = (ROOT/ROOT_FILES[0]).read_text()
    declarations = []
    for module in MODULES:
        path = ROOT/'Reinmann'/(module+'.lean')
        source = path.read_text()
        names = re.findall(r'^theorem\s+(\w+)', source, re.M)
        assert names and not re.search(r'\bnative_decide\b', source)
        declarations += ['Reinmann.'+module+'.'+name for name in names]
        assert 'import Reinmann.'+module in umbrella and 'import Reinmann.'+module in audit
        bound[path] = sha(path)
    assert len(declarations) == 78
    assert all('#print axioms '+name in audit for name in declarations)
    assert len(re.findall(r'^#print axioms', audit, re.M)) == 568
    assert not any(re.search(r'^import Reinmann$', p.read_text(), re.M)
                   for p in (ROOT/'Reinmann').glob('*.lean'))
    build = (OUT/'full_build.log').read_text()
    assert re.search(r'Build completed successfully \(\d+ jobs\)\.',build) and 'error:' not in build
    axiom = (OUT/'axiom_audit.log').read_text()
    assert 'all 568 audited theorems depend only on [propext, Classical.choice, Quot.sound]' in axiom
    assert 'AXIOM-CLEAN:' in axiom and 'FAIL:' not in axiom
    probe = json.loads((OUT/'arb_probe.json').read_text())
    assert probe['degree'] == 8 and probe['centre'] == ['1/2','14']
    assert [row['precision_bits'] for row in probe['rows']] == [64,80,96]
    for name, expected in probe['source_sha256'].items():
        assert sha(ROOT/name) == expected
    for row in probe['rows']:
        assert row['all_nine_overlap_independent_reference'] and len(row['dyadic_centres']) == 9
        assert float(re.match(r'\[?([\d.eE+-]+)',row['tile_margin_lower']).group(1)) > 0
    timings = json.loads((OUT/'component_replay/timings.json').read_text())
    assert timings['status'] == 'component_proofs_replayed' and len(timings['rows']) == 7
    for row in timings['rows']:
        assert row['returncode'] == 0 and row['seconds'] > 0
        assert row['source_sha256'] == sha(ROOT/'Reinmann'/(row['module']+'.lean'))
    assert not timings['complete_hard_tile_certified']
    assert timings['complete_hard_tile_seconds'] is None and timings['thirty_five_tiles_seconds'] is None
    for script in SCRIPTS:
        path = ROOT/'experiments/prime_spectral'/(script+'.py');bound[path] = sha(path)
    for script in SCRIPTS[1:4]:
        subprocess.run(['python3',str(ROOT/'experiments/prime_spectral'/(script+'.py')),'--check'],cwd=ROOT,check=True)
    for name in ROOT_FILES:
        bound[ROOT/name] = sha(ROOT/name)
    for path in OUT.rglob('*'):
        if path.is_file() and path.name != 'manifest.json': bound[path] = sha(path)
    for path in (BASE, REPORT): bound[path] = sha(path)
    result = {'status': 'degree8_arithmetic_and_actual_shifted_Log_jet_verified',
              'base_commit': PIN, 'new_audited_declarations': declarations,
              'total_audited_declarations': 568,
              'Lean_degree8_add_multiply_scale_round_sound': True,
              'Lean_exp_inverse_Log_recurrences_sound': True,
              'Lean_actual_shifted_Log_nine_coefficients_certified': True,
              'Lean_actual_shifted_Log_coefficient_radius_upper': '1e-12',
              'Lean_complete_Xi_finite_model_jet_certified': False,
              'Lean_complete_hard_tile_certified': False, 'Lean_complete_hard_tile_seconds': None,
              'thirty_five_Lean_tiles_seconds': None, 'zero_free_rectangle_certified': False,
              'RH_proved': False, 'published_files_unchanged': True,
              'artifacts_sha256': {str(p.relative_to(ROOT)): v for p,v in sorted(bound.items())}}
    manifest = OUT/'manifest.json'
    if record:
        if manifest.exists(): raise FileExistsError('Immutable manifest already exists')
        manifest.write_text(json.dumps(result,indent=2)+'\n')
    else:
        assert json.loads(manifest.read_text()) == result
    print(result['status'],len(declarations),'new theorems;',len(bound),'bound artifacts')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',action='store_true')
    check(parser.parse_args().record)
