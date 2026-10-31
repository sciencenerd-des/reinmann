"""Replay pricing, DH control and historical sources without changing receipts."""
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
from liu_direct_endpoint import certificate


def historical_replay():
    """The prior validator checks the prior source state, never today's registry."""
    snapshot = PACKET/'previous_refined_source_snapshot'
    old_paths = json.loads((PACKET/'earlier_verification_hashes.json').read_text())
    old_packet = Path('research/prime_spectral/verification_2026_11_01_refined_architecture')
    with tempfile.TemporaryDirectory(prefix='reinmann-historical-refined-') as directory:
        shadow = Path(directory)
        # Immutable earlier artifacts can be read through links; source inputs
        # with historical contents are then overlaid as real files.
        for name in old_paths:
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
        result = subprocess.run([sys.executable, str(shadow/old_packet/'validate.py')],
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
    recorded = json.loads((PACKET/'direct_endpoint_certificate.json').read_text())
    core = {k: v for k, v in recorded.items() if k not in ['DH_zero_replay', 'DH_Gaussian_value']}
    assert certificate() == core
    zero = recorded['DH_zero_replay']
    assert F(zero['rouche_left']['hi']) < F(zero['rouche_right']['lo'])
    assert F(zero['center_real']['lo'])-F(zero['radius']) > F(1, 2)
    assert F(zero['Gaussian_weight_abs']['lo']) > 0
    assert zero['nonzero_model_pole_residue']
    assert not zero['actual_DH_metaplectic_probe_instantiated']
    model = recorded['DH_Gaussian_value']
    assert model['terms'] == 91 and model['Z'] == '1/100'
    assert F(model['absolute_tail_bound']['lo']) > 0
    assert F(model['infinite_sum_enclosure']['lo']) < F(model['infinite_sum_enclosure']['hi'])
    assert not model['large_Z_growth_tested']
    register = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    route = next(r for r in register['routes'] if r['id'] == 'metaplectic_bootstrap_endpoint')
    outcome = route['direct_endpoint_preregistration_2026_11_01']['outcome']
    assert route['classification'] == 'uninstantiated' and route['separating_inequality'] is None
    assert not register['active_RH_strategy_with_proved_discriminator']
    assert not outcome['actual_probe_GRH_equivalence_proved']
    assert not outcome['whole_method_family_closed']
    assert not outcome['actual_DH_metaplectic_probe_instantiated']
    print(historical_replay())
    print(f'PASS: direct pricing and DH model checks; {len(old)} earlier verification '
          'files unchanged; prior refined validator replayed against its historical sources')
    print('Numerical certificate evaluation is replayed separately with --replay-dh-zero and Arb.')


if __name__ == '__main__':
    main()
