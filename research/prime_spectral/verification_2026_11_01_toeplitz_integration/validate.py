"""Check root/audit integration and replay the six earlier packets historically."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def historical_replay():
    previous = Path('research/prime_spectral/verification_2026_11_01_toeplitz_kernel')
    manifest = json.loads((ROOT/previous/'manifest.json').read_text())
    old = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    snapshots = json.loads((PACKET/'changed_source_snapshots.json').read_text())
    with tempfile.TemporaryDirectory(prefix='reinmann-historical-toeplitz-') as directory:
        shadow = Path(directory)
        for name in old:
            target = shadow/name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(ROOT/name)
        source_dir = shadow/'experiments/prime_spectral'
        source_dir.mkdir(parents=True, exist_ok=True)
        for source in (ROOT/'experiments/prime_spectral').glob('*.py'):
            target = source_dir/source.name
            if not target.exists():
                target.symlink_to(source)
        for suffix in ('refined_architecture', 'direct_endpoint', 'closure_interface',
                       'correction_threshold', 'other_directions', 'toeplitz_kernel'):
            prior = ROOT/'research/prime_spectral'/('verification_2026_11_01_'+suffix)/'manifest.json'
            for name in json.loads(prior.read_text())['sha256']:
                target = shadow/name
                if not target.exists():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.symlink_to(ROOT/name)
        for name, digest in manifest['sha256'].items():
            source = PACKET/snapshots[name] if name in snapshots else ROOT/name
            assert sha(source) == digest, name
            target = shadow/name
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.is_symlink():
                target.unlink()
            shutil.copyfile(source, target)
        run = subprocess.run([sys.executable, str(shadow/previous/'validate.py')], cwd=shadow,
                             capture_output=True, text=True)
        assert run.returncode == 0, run.stdout+run.stderr
        return run.stdout.strip()


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    manifest = json.loads((PACKET/'manifest.json').read_text())
    for name, digest in manifest['sha256'].items():
        assert sha(ROOT/name) == digest, name
    old = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    for name, digest in old.items():
        assert sha(ROOT/name) == digest, name
    root = set(re.findall(r'^import\s+(\S+)', (ROOT/'Reinmann.lean').read_text(), re.M))
    audit_text = (ROOT/'Reinmann/AxiomAudit.lean').read_text()
    audit = set(re.findall(r'^import\s+(\S+)', audit_text, re.M))
    assert {n for n in audit if n.startswith('Reinmann.')} <= root
    assert 'Reinmann.ToeplitzKernel' in root & audit
    closure = json.loads((ROOT/'research/prime_spectral/verification_2026_11_01_toeplitz_kernel/compiled_imports.json').read_text())
    assert audit-root <= set(closure)
    result = json.loads((PACKET/'integration.json').read_text())
    assert len(result['four_audited_constants']) == 4
    for name in result['four_audited_constants']:
        assert audit_text.count('#print axioms '+name+'\n') == 1
    assert json.loads((PACKET/'root_build.json').read_text())['exit_code'] == 0
    assert json.loads((PACKET/'axiom_clean.json').read_text())['exit_code'] == 0
    assert 'Build completed successfully' in (PACKET/'root_build.log').read_text()
    log = (PACKET/'axiom_clean.log').read_text()
    assert 'AXIOM-CLEAN: 0 sorry, 0 custom axioms' in log
    assert 'all 2647 audited theorems' in log
    register = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    entry = register['toeplitz_kernel_formalization_2026_11_01']
    assert entry['classification'] == 'shared_prerequisite'
    assert not entry['arithmetic_route_active'] and entry['separating_inequality'] is None
    assert entry['outcome']['root_import_changed']
    assert not entry['outcome']['general_atomic_representation_formalized']
    assert not register['active_RH_strategy_with_proved_discriminator']
    print(historical_replay())
    print(f'PASS: root import and four axiom audits integrated; {len(old)} earlier verification '
          'files unchanged; six preceding packets replayed historically')
    print('Local default build and axiom-clean receipts only; no remote CI or arithmetic separator claimed.')


if __name__ == '__main__':
    main()
