"""Validate a documentation refinement without changing sealed older packets."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]


def historical_replay():
    previous = Path('research/prime_spectral/verification_2026_11_01_closure_interface')
    manifest = json.loads((ROOT/previous/'manifest.json').read_text())
    old = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    snapshots = json.loads((PACKET/'changed_source_snapshots.json').read_text())
    with tempfile.TemporaryDirectory(prefix='reinmann-historical-closure-') as directory:
        shadow = Path(directory)
        for name in old:
            target = shadow/name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(ROOT/name)
        # Materialize previously bound sources, with historical contents for
        # the four documents that evolved. This also keeps __file__.resolve()
        # inside the historical tree when running the preceding validator.
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
    register = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    route = next(r for r in register['routes'] if r['id'] == 'metaplectic_bootstrap_endpoint')
    assert route['classification'] == 'uninstantiated' and route['separating_inequality'] is None
    refinement = route['closure_interface_preregistration_2026_11_01']['outcome']['noncancellation_threshold_refinement']
    assert refinement['possible_correction_zero_region'] == '1/2<Re(s)<2/3'
    assert not refinement['arithmetic_route_active']
    assert not refinement['actual_DH_metaplectic_probe_instantiated']
    assert not register['active_RH_strategy_with_proved_discriminator']
    print(historical_replay())
    print(f'PASS: threshold documentation and register scope; {len(old)} earlier '
          'non-cache verification files unchanged; three preceding packets replayed historically')


if __name__ == '__main__':
    main()
