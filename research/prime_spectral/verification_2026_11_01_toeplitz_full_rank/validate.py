"""Read-only check of full-rank Toeplitz nonuniqueness and exact criterion, local receipts and historical packets."""
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
PREVIOUS = Path('research/prime_spectral/verification_2026_11_01_toeplitz_uniqueness')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def active_lean_source(source):
    """Blank nested block and line comments, retaining active-code tokens."""
    result, depth, i = [], 0, 0
    while i < len(source):
        pair = source[i:i+2]
        if pair == '/-':
            depth += 1
            i += 2
        elif depth and pair == '-/':
            depth -= 1
            i += 2
        elif not depth and pair == '--':
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            result.append(source[i] if not depth else ('\n' if source[i] == '\n' else ' '))
            i += 1
    assert depth == 0, 'Unclosed Lean block comment'
    return ''.join(result)


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
                       'toeplitz_integration', 'toeplitz_simple_roots', 'toeplitz_general',
                       'toeplitz_uniqueness'):
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
    # Regression checks for the comment false positive that triggered this repair.
    assert not re.search(r'\b(sorry|admit|axiom)\b', active_lean_source(
        '/- outer /- admit -/ axiom -/ theorem x := by trivial -- sorry\n'))
    assert re.search(r'\bsorry\b', active_lean_source('/- comment -/ theorem x := by sorry'))
    manifest = json.loads((PACKET/'manifest.json').read_text())
    for name, digest in manifest['sha256'].items():
        assert sha(ROOT/name) == digest, name
    old = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    for name, digest in old.items():
        assert sha(ROOT/name) == digest, name
    for name in ('Reinmann/ToeplitzPrescribedAtom.lean', 'Reinmann/ToeplitzFullRank.lean'):
        assert not re.search(r'\b(sorry|admit|sorryAx|axiom)\b', active_lean_source((ROOT/name).read_text()))
    root = set(re.findall(r'^import\s+(\S+)', (ROOT/'Reinmann.lean').read_text(), re.M))
    audit_text = (ROOT/'Reinmann/AxiomAudit.lean').read_text()
    audit = set(re.findall(r'^import\s+(\S+)', audit_text, re.M))
    assert {n for n in audit if n.startswith('Reinmann.')} <= root
    assert {'Reinmann.ToeplitzPrescribedAtom', 'Reinmann.ToeplitzFullRank'} <= root & audit
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", (PACKET/'axioms.log').read_text())
    expected = set(re.findall(r'^#print axioms (\S+)', (PACKET/'Probe.lean').read_text(), re.M))
    assert len(rows) == 4 and {name for name, _ in rows} == expected
    for name, axioms in rows:
        assert set(axioms.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert audit_text.count('#print axioms '+name+'\n') == 1
    for command in json.loads((PACKET/'commands.json').read_text()):
        assert command['exit_code'] == 0
    assert 'Build completed successfully' in (PACKET/'root_build.log').read_text()
    audit_log = (PACKET/'axiom_clean.log').read_text()
    assert 'all 2671 audited theorems' in audit_log and 'AXIOM-CLEAN' in audit_log
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
    entry = register['toeplitz_full_rank_2026_11_01']
    assert entry['classification'] == 'shared_prerequisite'
    assert not entry['arithmetic_route_active'] and entry['separating_inequality'] is None
    outcome = entry['outcome']
    assert outcome['prescribed_unit_circle_node_representation_proved']
    assert outcome['every_full_rank_PSD_Toeplitz_matrix_nonunique_proved']
    assert outcome['two_rank_sized_distinct_supports_proved']
    assert outcome['supported_finite_data_unique_iff_singular_proved']
    assert not outcome['off_support_weight_values_compared']
    assert not outcome['arbitrary_measure_uniqueness_proved']
    assert not outcome['arithmetic_PSD_input_proved']
    assert outcome['root_and_audit_integrated']
    assert not register['active_RH_strategy_with_proved_discriminator']
    print(historical_replay())
    print(f'PASS: prescribed atoms, universal full-rank nonuniqueness and exact uniqueness criterion; '
          f'{len(old)} earlier verification files unchanged; ten earlier packets replayed historically')
    print('Default root build, four axiom checks and Lean own-kernel replay are recorded; '
          'off-support function equality, arbitrary-measure uniqueness and arithmetic positivity are not claimed.')


if __name__ == '__main__':
    main()
