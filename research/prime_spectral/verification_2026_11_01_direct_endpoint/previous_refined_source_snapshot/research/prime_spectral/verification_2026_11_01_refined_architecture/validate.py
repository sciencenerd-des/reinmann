"""Offline replay of the bound scalar packet; never edits receipts."""
import hashlib
import json
from pathlib import Path
import sys

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]
sys.path.insert(0, str(ROOT/'experiments/prime_spectral'))
from liu_refined_architecture import certificate


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    manifest = json.loads((PACKET/'manifest.json').read_text())
    for name, digest in manifest['sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    old = json.loads((PACKET/'existing_verification_hashes.json').read_text())
    for name, digest in old.items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    recorded = json.loads((PACKET/'scalar_certificate.json').read_text())
    assert certificate() == recorded
    assert recorded['direct_relaxation']['floor'] == '13/15'
    assert recorded['direct_relaxation']['full_idealized_system_exact_optimum'] is None
    register = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    route = next(r for r in register['routes'] if r['id'] == 'metaplectic_bootstrap_endpoint')
    assert route['classification'] == 'uninstantiated'
    assert route['separating_inequality'] is None
    result = route['architecture_floor_preregistration_2026_11_01']['outcome']
    assert result['direct_only_relaxation_exact_minimum'] == '13/15'
    assert result['full_idealized_system_exact_optimum'] is None
    assert not result['RH_claim'] and not result['new_arithmetic_estimate']
    print(f'PASS: {len(manifest["sha256"])} bound files; {len(old)} earlier '
          'verification files unchanged; four stages, quartic and direct dual replayed')


if __name__ == '__main__':
    main()
