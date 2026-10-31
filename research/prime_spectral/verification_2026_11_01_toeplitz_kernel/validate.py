"""Read-only integrity, scope and historical-source replay for the Toeplitz theorem.

Use --replay-lean to rebuild/re-elaborate the current target as well.
Use --compiled-inputs to check the local compiled closure bound by kernel_replay.py.
Use --replay-kernel for another read-only fresh kernel replay.
"""
import argparse
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
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def historical_replay():
    previous = Path('research/prime_spectral/verification_2026_11_01_other_directions')
    manifest = json.loads((ROOT/previous/'manifest.json').read_text())
    old = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    snapshots = json.loads((PACKET/'changed_source_snapshots.json').read_text())
    with tempfile.TemporaryDirectory(prefix='reinmann-historical-directions-') as directory:
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
        # Nested validators also need unchanged note/source dependencies that
        # the immediately preceding packet did not itself bind.
        for suffix in ('refined_architecture', 'direct_endpoint', 'closure_interface',
                       'correction_threshold', 'other_directions'):
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
        result = subprocess.run([sys.executable, str(shadow/previous/'validate.py')],
                                capture_output=True, text=True, cwd=shadow)
        if result.returncode:
            raise AssertionError(result.stdout+result.stderr)
        return result.stdout.strip()


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay-lean', action='store_true')
    parser.add_argument('--compiled-inputs', action='store_true')
    parser.add_argument('--replay-kernel', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((PACKET/'manifest.json').read_text())
    for name, digest in manifest['sha256'].items():
        assert sha(ROOT/name) == digest, name
    old = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    for name, digest in old.items():
        assert sha(ROOT/name) == digest, name
    register = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    entry = register['toeplitz_kernel_formalization_2026_11_01']
    assert entry['classification'] == 'shared_prerequisite'
    assert entry['separating_inequality'] is None
    assert not entry['arithmetic_route_active'] and not entry['RH_claim']
    assert not register['active_RH_strategy_with_proved_discriminator']
    result = entry['outcome']
    assert result['kernel_root_corollary_formalized'] and result['full_degree_formalized']
    assert not result['general_atomic_representation_formalized']
    assert not result['arithmetic_positivity_proved'] and not result['root_import_changed']
    source = (ROOT/'Reinmann/ToeplitzKernel.lean').read_text()
    assert not re.search(r'\b(sorry|admit|axiom)\b', source)
    audit = (PACKET/'axioms.log').read_text()
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
    expected = {'Reinmann.ToeplitzKernel.'+n for n in
                ('root_norm_eq_one', 'kernel_polynomial_roots_unit_circle', 'natDegree_eq_of_kernel')}
    assert len(rows) == 3 and {name for name, _ in rows} == expected
    for name, axioms in rows:
        assert set(axioms.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}, name
    assert 'Build completed successfully' in (PACKET/'build.log').read_text()
    replay = json.loads((PACKET/'kernel_replay.json').read_text())
    assert replay['exit_code'] == 0 and replay['compiled_inputs_unchanged']
    assert (ROOT/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.30.0'
    assert 'ToeplitzKernel' not in (ROOT/'Reinmann.lean').read_text()
    if args.compiled_inputs or args.replay_kernel:
        bindings = json.loads((PACKET/'compiled_inputs.json').read_text())
        for name, record in bindings.items():
            assert sha(Path(name)) == record['sha256'], name
        print(f'PASS: {len(bindings)} local compiled/metadata inputs unchanged')
    if args.replay_lean:
        for command in (['lake', 'build', 'Reinmann.ToeplitzKernel'],
                        ['lake', 'env', 'lean', str(PACKET/'Probe.lean')]):
            run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            assert run.returncode == 0, run.stdout+run.stderr
            if command[-1].endswith('Probe.lean'):
                assert run.stdout == audit, 'Axiom/theorem probe output drift'
        print('PASS: current Lean target and standard-axiom probe replayed')
    if args.replay_kernel:
        command = ['lake', 'env', 'leanchecker', '--fresh', '--verbose', 'Reinmann.ToeplitzKernel']
        run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=600)
        assert run.returncode == 0, run.stdout+run.stderr
        for name, record in bindings.items():
            assert sha(Path(name)) == record['sha256'], name
        print('PASS: fresh Lean own-kernel replay; bound compiled inputs unchanged')
    print(historical_replay())
    print(f'PASS: finite Toeplitz kernel theorem and shared-prerequisite scope; '
          f'{len(old)} earlier non-cache verification files unchanged; five earlier packets replayed historically')
    print('No general atomic moment representation, arithmetic positivity, root build or CI is claimed.')


if __name__ == '__main__':
    main()
