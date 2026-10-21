"""Build optional finite-band tiles in bounded batches with timing receipts."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]


def run(rank, jobs, output, indices=None):
    assert rank in (58, 97) and 1 <= jobs <= 4
    library = f'XiBand{rank}'
    tiles = sorted((ROOT / library).glob('Tile[0-9][0-9][0-9].lean'))
    if indices is not None:
        tiles = [p for p in tiles if int(p.stem[4:]) in indices]
        assert {int(p.stem[4:]) for p in tiles} == indices
    assert tiles
    output.mkdir(parents=True, exist_ok=True)
    batches = [['Reinmann.FiniteBandModel', 'Reinmann.FiniteBandTileRules', library+'.Cover']]
    # Degree-16 Gamma modules use several GB each. Serialize them per runner.
    batches += [[library+'.'+p.stem+'Gamma'] for p in tiles]
    for i in range(0, len(tiles), jobs):
        selected = tiles[i:i+jobs]
        for suffix in ('Terms0', 'Terms1', 'Terms2', 'Terms3', 'Zeta', ''):
            batches.append([library+'.'+p.stem+suffix for p in selected])
    if indices is None:
        batches.append([library])
    rows = []
    start = time.monotonic()
    for i, targets in enumerate(batches):
        before = time.monotonic()
        log = output / f'batch_{i:03}.log'
        with log.open('w') as stream:
            result = subprocess.run(['lake', 'build', *targets], cwd=ROOT,
                                    stdout=stream, stderr=subprocess.STDOUT)
        rows.append({'targets': targets, 'seconds': time.monotonic()-before,
                     'returncode': result.returncode, 'log': str(log),
                     'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()})
        receipt = {'status': ('failed' if result.returncode else
                             ('complete' if i+1 == len(batches) else 'in_progress')),
                   'rank': rank, 'jobs': jobs, 'Gamma_jobs': 1,
                   'wall_seconds': time.monotonic()-start, 'rows': rows,
                   'tiles_source_sha256': {str(p.relative_to(ROOT)):
                                          hashlib.sha256(p.read_bytes()).hexdigest() for p in tiles}}
        (output / 'timings.json').write_text(json.dumps(receipt, indent=2)+'\n')
        print(json.dumps(rows[-1]), flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int, choices=(58, 97), required=True)
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--tiles', help='comma-separated subset; omits final assembly')
    args = parser.parse_args()
    run(args.rank, args.jobs, args.output.resolve(),
        None if args.tiles is None else set(map(int, args.tiles.split(','))))
