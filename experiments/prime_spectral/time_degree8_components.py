"""Replay selected degree-eight component proofs and record fresh elapsed times.

Dependencies must be built first. These are component elaboration measurements,
not the complete Xi hard tile and not a cost estimate for 35 tiles.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
MODULES = ('CertifiedTaylorModel', 'CertifiedTaylorComposition', 'CertifiedComplexInputs',
           'CertifiedHorner', 'HardTileLogInputs', 'HardTileGammaLog', 'HardTileGammaLogJet')


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    rows = []
    for module in MODULES:
        path = ROOT/'Reinmann'/(module+'.lean')
        start = time.monotonic()
        result = subprocess.run(['lake', 'env', 'lean', str(path.relative_to(ROOT))],
                                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, timeout=300)
        elapsed = time.monotonic()-start
        (output/(module+'.log')).write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f'{module} failed; see {output/(module+".log")}')
        rows.append({'module': module, 'seconds': elapsed, 'returncode': result.returncode,
                     'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
        print(module, f'{elapsed:.3f}s', flush=True)
    receipt = {'status': 'component_proofs_replayed', 'lean_version':
               subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT, text=True).strip(),
               'mathlib': 'v4.30.0', 'rows': rows,
               'timing_scope': 'fresh component elaboration with built dependencies',
               'complete_hard_tile_certified': False, 'complete_hard_tile_seconds': None,
               'thirty_five_tiles_seconds': None}
    (output/'timings.json').write_text(json.dumps(receipt, indent=2)+'\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    run(parser.parse_args().output)
