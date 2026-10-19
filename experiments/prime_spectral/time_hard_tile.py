"""Fresh, serial Lean elaboration of the complete hard-tile proof inputs.

Mathlib and analytic foundation dependencies must already be built. Every
listed source is re-elaborated, including its rational numerical checks; this
does not time a clean Mathlib build or merely the cached final tile theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
SHARED = (
    'CertifiedTaylorModel', 'CertifiedComplexInputs', 'CertifiedTaylorComposition',
    'CertifiedHorner', 'CertifiedScalarExp', 'CertifiedTaylorInputs',
    'HardTileFiniteIdentities', 'TaylorDerivativeTail',
    'EulerMaclaurinAnalytic', 'XiLocalCauchy',
)
CENTRE = ('StirlingAnalytic', 'ZetaJetRemainder', 'HardTileLogInputs', 'HardTileGammaLog', 'HardTileGammaLogJet',
          'HardTileFiniteJets', 'HardTileXi')


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    if (output / 'timings.json').exists():
        raise FileExistsError('Preserve the earlier timing receipt')
    rows = []
    for module in SHARED + CENTRE:
        path = ROOT / 'Reinmann' / (module + '.lean')
        source_hash = hashlib.sha256(path.read_bytes()).hexdigest()
        start = time.monotonic()
        result = subprocess.run(['lake', 'env', 'lean', str(path.relative_to(ROOT))],
                                cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, timeout=3600)
        elapsed = time.monotonic() - start
        log = output / (module + '.log')
        log.write_text(result.stdout)
        assert hashlib.sha256(path.read_bytes()).hexdigest() == source_hash
        if result.returncode:
            raise RuntimeError(f'{module} failed; see {log}')
        rows.append({'module': module, 'seconds': elapsed,
                     'kind': 'shared' if module in SHARED else 'centre_specific',
                     'returncode': result.returncode, 'source_sha256': source_hash})
        print(module, f'{elapsed:.3f}s', flush=True)
    shared = sum(r['seconds'] for r in rows if r['kind'] == 'shared')
    centre = sum(r['seconds'] for r in rows if r['kind'] == 'centre_specific')
    receipt = {
        'status': 'complete_single_hard_tile_proofs_replayed',
        'centre': ['1/2', '14'], 'radius': '1/16', 'degree': 8,
        'lean_version': subprocess.check_output(
            ['lake', 'env', 'lean', '--version'], cwd=ROOT, text=True).strip(),
        'mathlib': 'v4.30.0', 'rows': rows,
        'timing_scope': 'fresh serial source elaboration with built dependencies',
        'shared_seconds': shared, 'centre_specific_seconds': centre,
        'complete_single_tile_seconds': shared + centre,
        'conditional_35_centre_projection_seconds': shared + 35 * centre,
        'projection_assumption': 'each other centre costs as much as this one; untested',
        'zero_free_rectangle_certified': False, 'RH_proved': False,
    }
    (output / 'timings.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k.endswith('seconds')}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    run(parser.parse_args().output)
