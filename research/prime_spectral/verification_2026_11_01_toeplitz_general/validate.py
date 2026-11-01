"""Read-only check of general Toeplitz representation, local receipts and historical packets."""
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
PREVIOUS = Path('research/prime_spectral/verification_2026_11_01_toeplitz_simple_roots')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def historical_replay():
    manifest = json.loads((ROOT/PREVIOUS/'manifest.json').read_text())
    old = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    snapshots = json.loads((PACKET/'changed_source_snapshots.json').read_text())
    with tempfile.TemporaryDirectory(prefix='reinmann-historical-atomic-') as directory:
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
                       'correction_threshold', 'other_directions', 'toeplitz_kernel',
                       'toeplitz_integration', 'toeplitz_simple_roots'):
            earlier = ROOT/'research/prime_spectral'/('verification_2026_11_01_'+suffix)/'manifest.json'
            for name in json.loads(earlier.read_text())['sha256']:
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
        run = subprocess.run([sys.executable, str(shadow/PREVIOUS/'validate.py')], cwd=shadow,
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
    for name in ('Reinmann/ToeplitzExtension.lean', 'Reinmann/ToeplitzDowndate.lean',
                 'Reinmann/ToeplitzRepresentation.lean'):
        assert not re.search(r'\b(sorry|admit|axiom)\b', (ROOT/name).read_text())
    root = set(re.findall(r'^import\s+(\S+)', (ROOT/'Reinmann.lean').read_text(), re.M))
    audit_text = (ROOT/'Reinmann/AxiomAudit.lean').read_text()
    audit = set(re.findall(r'^import\s+(\S+)', audit_text, re.M))
    assert {n for n in audit if n.startswith('Reinmann.')} <= root
    assert {'Reinmann.ToeplitzExtension', 'Reinmann.ToeplitzDowndate', 'Reinmann.ToeplitzRepresentation'} <= root & audit
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", (PACKET/'axioms.log').read_text())
    expected = set(re.findall(r'^#print axioms (\S+)', (PACKET/'Probe.lean').read_text(), re.M))
    assert len(rows) == 5 and {name for name, _ in rows} == expected
    for name, axioms in rows:
        assert set(axioms.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert audit_text.count('#print axioms '+name+'\n') == 1
    for command in json.loads((PACKET/'commands.json').read_text()):
        assert command['exit_code'] == 0
    assert 'Build completed successfully' in (PACKET/'root_build.log').read_text()
    audit_log = (PACKET/'axiom_clean.log').read_text()
    assert 'all 2660 audited theorems' in audit_log and 'AXIOM-CLEAN' in audit_log
    replay = json.loads((PACKET/'kernel_replay.json').read_text())
    assert replay['exit_code'] == 0 and replay['bound_inputs_unchanged']
    for name, digest in replay['source_sha256'].items():
        assert sha(ROOT/name) == digest, name
    for name in ('compiled_inputs', 'compiled_imports'):
        delta = json.loads((PACKET/(name+'_delta.json')).read_text())
        assert sha(ROOT/delta['baseline']) == delta['baseline_sha256']
        baseline = json.loads((ROOT/delta['baseline']).read_text())
        assert not baseline.keys() & delta['added'].keys()
        assert len(baseline)+len(delta['added']) == delta['total_entries']
    register = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    entry = register['toeplitz_general_representation_2026_11_01']
    assert entry['classification'] == 'shared_prerequisite'
    assert not entry['arithmetic_route_active'] and entry['separating_inequality'] is None
    outcome = entry['outcome']
    assert outcome['general_arbitrary_rank_representation_proved']
    assert outcome['singular_arbitrary_rank_representation_proved']
    assert outcome['full_rank_representation_proved'] and outcome['exact_rank_atom_count']
    assert outcome['strictly_positive_real_weights'] and outcome['distinct_unit_circle_support']
    assert not outcome['extra_kernel_or_rank_input_required']
    assert not outcome['arithmetic_PSD_input_proved']
    assert not outcome['representation_uniqueness_proved']
    assert outcome['root_and_audit_integrated']
    assert not register['active_RH_strategy_with_proved_discriminator']
    print(historical_replay())
    print(f'PASS: general-rank positive finite Toeplitz atomic representation; '
          f'{len(old)} earlier verification files unchanged; eight earlier packets replayed historically')
    print('Default root build, five axiom checks and Lean own-kernel replay are recorded; '
          'representation uniqueness and arithmetic positivity are not claimed.')


if __name__ == '__main__':
    main()
