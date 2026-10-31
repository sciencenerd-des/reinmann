"""Read-only replay of the B certificate and all preceding historical packets."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]
sys.path.insert(0, str(ROOT/'experiments/prime_spectral'))
from liu_refined_localized import certificate


def historical_replay():
    previous = Path('research/prime_spectral/verification_2026_11_01_correction_threshold')
    manifest = json.loads((ROOT/previous/'manifest.json').read_text())
    old = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    snapshots = json.loads((PACKET/'changed_source_snapshots.json').read_text())
    with tempfile.TemporaryDirectory(prefix='reinmann-historical-threshold-') as directory:
        shadow = Path(directory)
        for name in old:
            target = shadow/name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(ROOT/name)
        # Nested validators materialize their own bound historical sources;
        # make unchanged working-source dependencies available for those copies.
        source_dir = shadow/'experiments/prime_spectral'
        source_dir.mkdir(parents=True, exist_ok=True)
        for source in (ROOT/'experiments/prime_spectral').glob('*.py'):
            target = source_dir/source.name
            if not target.exists():
                target.symlink_to(source)
        for name, digest in manifest['sha256'].items():
            source = PACKET/snapshots[name] if name in snapshots else ROOT/name
            assert hashlib.sha256(source.read_bytes()).hexdigest() == digest, name
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
    manifest = json.loads((PACKET/'manifest.json').read_text())
    for name, digest in manifest['sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    old = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    for name, digest in old.items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    recorded = json.loads((PACKET/'refined_localized_certificate.json').read_text())
    assert certificate() == recorded
    assert F(recorded['conditional_B']) == F(34993, 40000)
    assert not recorded['arithmetic_moment_proved'] and not recorded['DH_family_instantiated']
    assert not recorded['improves_older_conditional_B_0_874793']
    register = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    route = next(r for r in register['routes'] if r['id'] == 'metaplectic_bootstrap_endpoint')
    assert route['classification'] == 'uninstantiated' and route['separating_inequality'] is None
    assert not register['active_RH_strategy_with_proved_discriminator']
    outcome = route['other_directions_preregistration_2026_11_01']['outcome']
    assert not outcome['arithmetic_route_active']
    assert not outcome['D']['toolchain_upgrade_performed']
    assert not outcome['E']['full_CF_formalization_completed']
    assert (ROOT/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.30.0'
    print(historical_replay())
    print(f'PASS: band-only refined certificate and scope; {len(old)} earlier '
          'non-cache verification files unchanged; four preceding packets replayed historically')
    print('Lean build/probe results are bound receipts, not repeated by this Python validator.')


if __name__ == '__main__':
    main()
