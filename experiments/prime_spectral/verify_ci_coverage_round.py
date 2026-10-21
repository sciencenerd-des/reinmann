"""Check the default-import/audit correction and its immutable predecessor replay."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'research/prime_spectral/verification_2026_10_21_ci_coverage'
MODULES = ['CornerPowerSumCounterexample', 'FiniteHeightPFCalibration']
HEADLINES = {
    'Reinmann.CornerPowerSumCounterexample.powerSum_ge_third',
    'Reinmann.CornerPowerSumCounterexample.shift_two_rank_three',
    'Reinmann.CornerPowerSumCounterexample.not_finitePF_three',
    'Reinmann.FiniteHeightPFCalibration.angleBound_of_two_bands',
    'Reinmann.FiniteHeightPFCalibration.finitePF97_of_low_height_width',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(record=False):
    ci = json.loads((OUT/'ci_run_39512801397.json').read_text())
    assert ci['headSha'] == '04964c00590d9cd8a697d95186470b6c698d56b2'
    expected = {'build-and-verify', 'xi-rectangle-deps', 'xi-rectangle-certificate'}
    expected |= {f'xi-rectangle-shard ({i})' for i in range(11)}
    assert ci['conclusion'] == 'success' and ci['status'] == 'completed'
    assert len(ci['jobs']) == 14 and {j['name'] for j in ci['jobs']} == expected
    assert all(j['conclusion'] == 'success' for j in ci['jobs'])
    root = (ROOT/'Reinmann.lean').read_text()
    audit_source = (ROOT/'Reinmann/AxiomAudit.lean').read_text()
    root_imports = set(re.findall(r'^import (\S+)', root, re.M))
    for module in MODULES:
        assert f'import Reinmann.{module}' in root
        assert f'import Reinmann.{module}' in audit_source
        assert f'm == `Reinmann.{module}' in audit_source
        imports = set(re.findall(r'^import (Reinmann\.\S+)',
                                 (ROOT/f'Reinmann/{module}.lean').read_text(), re.M))
        assert imports <= root_imports, (module, imports-root_imports)
    audit = (OUT/'full_axiom_audit.log').read_text()
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
    new = [(name, axioms) for name, axioms in rows
           if any(name.startswith('Reinmann.'+m+'.') for m in MODULES)]
    assert len(new) == 11 and HEADLINES <= {name for name, _ in new}
    assert all(set(a.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
               for _, a in rows)
    assert 'all 2619 audited theorems' in (OUT/'root_guard.log').read_text()
    assert 'AXIOM-CLEAN:' in (OUT/'root_guard.log').read_text()
    assert 'Build completed successfully' in (OUT/'default_build.log').read_text()
    checks = json.loads((OUT/'checks.json').read_text())
    assert len(checks) == 5 and all(c['exit_code'] == 0 for c in checks)
    for check in checks:
        assert sha(OUT/check['log']) == check['log_sha256']
    register = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    control = register['finite_strengthening_controls'][0]
    assert control['id'] == 'quasi_rh_seven_eighths'
    failure = control['failure']
    assert failure['kind'] == 'classical_theorem_not_a_located_numerical_witness'
    assert failure['first_height'] is None and failure['explicit_zero_ball'] is None
    assert failure['globally_first'] is False
    reference = json.loads((OUT/'literature_check.json').read_text())
    assert failure['reference']['download_sha256'] == reference['source_pdf_sha256']
    assert reference['visually_checked_definition_and_kappa']
    assert not reference['explicit_zero_ball_certified']
    assert sha(ROOT/reference['coefficient_formula_matched_to']) == reference['coefficient_source_sha256']
    inventory = OUT/'tile_object_eviction_inventory.json'
    before = json.loads(inventory.read_text())
    after = json.loads((OUT/'tile_object_eviction_result.json').read_text())
    assert after['inventory_sha256'] == sha(inventory)
    assert len(before['objects']) == after['objects_removed'] == 2464
    assert sum(x['allocated_bytes'] for x in before['objects']) == after['allocated_bytes_removed']
    assert all(re.fullmatch(r'\.lake/build/(lib/lean|ir)/XiRectangle/Tile[^/]+', x['path'])
               for x in before['objects'])
    for name, wanted in before['source_files_sha256'].items():
        assert name.startswith('XiRectangle') and sha(ROOT/name) == wanted
    assert after['source_files_preserved'] == len(before['source_files_sha256']) == 312
    with tempfile.TemporaryDirectory(prefix='rh-ci-coverage-check-') as tmp:
        receipt = Path(tmp)/'replay.json'
        subprocess.run(['python3', 'experiments/prime_spectral/replay_ci_coverage_predecessors.py',
                        '--output', str(receipt)], cwd=ROOT, check=True, stdout=subprocess.PIPE)
        assert json.loads(receipt.read_text()) == json.loads((OUT/'predecessor_replay.json').read_text())
    owned = ['Reinmann.lean', 'Reinmann/AxiomAudit.lean',
             'research/RH_DH_DISCRIMINATOR_REGISTER.json', 'research/RH_DH_DISCRIMINATOR_REGISTER.md',
             'experiments/prime_spectral/replay_ci_coverage_predecessors.py',
             'experiments/prime_spectral/verify_ci_coverage_round.py',
             'research/prime_spectral/CI_COVERAGE_AND_DH_HALFPLANE_2026_10_21.md']
    bindings = {name: sha(ROOT/name) for name in owned}
    bindings.update({str(p.relative_to(ROOT)): sha(p) for p in OUT.rglob('*')
                     if p.is_file() and p.name != 'manifest.json'})
    result = dict(status='default_coverage_and_DH_reference_corrected_locally_verified',
                  current_root_audit_rows=2619, newly_audited_public_theorems=5,
                  newly_audited_generated_helpers=6, previous_successful_ci_run=39512801397,
                  previous_ci_commit=ci['headSha'], this_round_CI_verified=False,
                  external_seven_eighths_proved_by_this_receipt=False,
                  unconditional_PF58=False, artifacts_sha256=bindings)
    path = OUT/'manifest.json'
    if record:
        with path.open('x') as stream:
            stream.write(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result
    print('Verified two default-root modules, five headline/6 generated theorem audits,',
          'classical DH half-plane reference and preserved historical receipts;',
          len(bindings), 'bindings. New remote CI and external 7/8 proof not claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true')
    verify(parser.parse_args().record)
