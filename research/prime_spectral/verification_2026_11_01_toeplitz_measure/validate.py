"""Read-only check of finite Borel representing measures, exact uniqueness, local receipts and historical packets."""
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
PREVIOUS = Path('research/prime_spectral/verification_2026_11_01_toeplitz_full_rank')


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
                       'toeplitz_uniqueness', 'toeplitz_full_rank'):
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
    # Retain the comment-aware no-placeholder regression checks.
    assert not re.search(r'\b(sorry|admit|axiom)\b', active_lean_source(
        '/- outer /- admit -/ axiom -/ theorem x := by trivial -- sorry\n'))
    assert re.search(r'\bsorry\b', active_lean_source('/- comment -/ theorem x := by sorry'))
    manifest = json.loads((PACKET/'manifest.json').read_text())
    for name, digest in manifest['sha256'].items():
        assert sha(ROOT/name) == digest, name
    old = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    for name, digest in old.items():
        assert sha(ROOT/name) == digest, name
    for name in ('Reinmann/ToeplitzMeasure.lean', 'Reinmann/ToeplitzMeasureUniqueness.lean'):
        assert not re.search(r'\b(sorry|admit|sorryAx|axiom)\b', active_lean_source((ROOT/name).read_text()))
    root = set(re.findall(r'^import\s+(\S+)', (ROOT/'Reinmann.lean').read_text(), re.M))
    audit_text = (ROOT/'Reinmann/AxiomAudit.lean').read_text()
    audit = set(re.findall(r'^import\s+(\S+)', audit_text, re.M))
    assert {n for n in audit if n.startswith('Reinmann.')} <= root
    assert {'Reinmann.ToeplitzMeasure', 'Reinmann.ToeplitzMeasureUniqueness'} <= root & audit
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", (PACKET/'axioms.log').read_text())
    expected = set(re.findall(r'^#print axioms (\S+)', (PACKET/'Probe.lean').read_text(), re.M))
    assert len(rows) == 9 and {name for name, _ in rows} == expected
    for name, axioms in rows:
        assert set(axioms.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert audit_text.count('#print axioms '+name+'\n') == 1
    for command in json.loads((PACKET/'commands.json').read_text()):
        assert command['exit_code'] == 0
    assert 'Build completed successfully' in (PACKET/'root_build.log').read_text()
    audit_log = (PACKET/'axiom_clean.log').read_text()
    assert 'all 2680 audited theorems' in audit_log and 'AXIOM-CLEAN' in audit_log
    replay = json.loads((PACKET/'kernel_replay.json').read_text())
    assert replay['exit_code'] == 0 and replay['bound_inputs_unchanged']
    assert replay['runner_sha256'] == sha(PACKET/'kernel_replay.py')
    assert 'DH gate:' in (PACKET/'DH_gate.log').read_text()
    assert not (PACKET/'diff_check.log').read_text().strip()
    for name, digest in replay['source_sha256'].items():
        assert sha(ROOT/name) == digest, name
    for name in ('compiled_inputs', 'compiled_imports'):
        delta = json.loads((PACKET/(name+'_delta.json')).read_text())
        assert sha(ROOT/delta['baseline']) == delta['baseline_sha256']
        baseline = json.loads((ROOT/delta['baseline']).read_text())
        assert not baseline.keys() & delta['added'].keys()
        assert len(baseline)+len(delta['added']) == delta['total_entries']
    register = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    entry = register['toeplitz_measure_2026_11_01']
    assert entry['classification'] == 'shared_prerequisite'
    assert not entry['arithmetic_route_active'] and entry['separating_inequality'] is None
    assert not entry['RH_claim'] and not entry['novelty_claim']
    outcome = entry['outcome']
    for key in ('finite_Borel_representing_measure_exists', 'kernel_polynomial_vanishes_ae',
                'arbitrary_competitor_confined_to_reference_support', 'singleton_masses_recovered',
                'singular_unique_among_all_finite_circle_measures', 'full_rank_distinct_measures',
                'measure_uniqueness_iff_singular', 'root_and_audit_integrated'):
        assert outcome[key], key
    for key in ('competitor_assumed_atomic', 'infinite_moment_sequence_representation_proved',
                'arithmetic_PSD_input_proved', 'remote_CI_run'):
        assert not outcome[key], key
    assert not register['active_RH_strategy_with_proved_discriminator']
    print(historical_replay())
    print(f'PASS: finite Borel representing measures and exact uniqueness among all finite circle measures; '
          f'{len(old)} earlier verification files unchanged; eleven earlier packets replayed historically')
    print('Default root build, nine axiom checks and Lean own-kernel replay are recorded; '
          'infinite moment-sequence representation and arithmetic positivity are not claimed.')


if __name__ == '__main__':
    main()
