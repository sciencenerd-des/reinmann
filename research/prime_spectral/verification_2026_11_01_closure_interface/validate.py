"""Read-only scalar replay and nested historical-source packet validation."""
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
from liu_closure_interface import certificate


def historical_replay():
    snapshot = PACKET/'previous_direct_source_snapshot'
    paths = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    previous = Path('research/prime_spectral/verification_2026_11_01_direct_endpoint')
    with tempfile.TemporaryDirectory(prefix='reinmann-historical-direct-') as directory:
        shadow = Path(directory)
        for name in paths:
            target = shadow/name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(ROOT/name)
        for source in snapshot.rglob('*'):
            if source.is_file():
                target = shadow/source.relative_to(snapshot)
                target.parent.mkdir(parents=True, exist_ok=True)
                if target.is_symlink():
                    target.unlink()
                shutil.copyfile(source, target)
        # The preceding validator's imported core depends on these unchanged
        # source modules, which its own manifest does not bind individually.
        for name in ['liu_conditional_moment.py', 'liu_localized_target.py',
                     'liu_refined_architecture.py']:
            target = shadow/'experiments/prime_spectral'/name
            if not target.exists():
                target.symlink_to(ROOT/'experiments/prime_spectral'/name)
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
    assert certificate() == json.loads((PACKET/'closure_interface_certificate.json').read_text())
    d = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    route = next(r for r in d['routes'] if r['id'] == 'metaplectic_bootstrap_endpoint')
    assert route['classification'] == 'uninstantiated' and route['separating_inequality'] is None
    assert not d['active_RH_strategy_with_proved_discriminator']
    outcome = route['closure_interface_preregistration_2026_11_01']['outcome']
    assert not outcome['GRH_implication_for_actual_probe_proved']
    assert not outcome['actual_absolute_remainder_disproved']
    assert not outcome['correction_global_nonvanishing_on_half_plane']
    print(historical_replay())
    print(f'PASS: closure algebra and register scope; {len(old)} earlier non-cache '
          'verification files unchanged; both preceding packets replayed historically')
    print('Standard Hecke analytic theory and the full theta identity are not machine proved.')


if __name__ == '__main__':
    main()
