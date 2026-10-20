"""Build numerical tile modules in bounded concurrent batches, retaining receipts."""
import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]


def run(jobs,output,indices=None):
    if not 1<=jobs<=12: raise ValueError('Choose 1..12 concurrent tile modules')
    output.mkdir(parents=True,exist_ok=True)
    tiles=sorted((ROOT/'XiRectangle').glob('Tile[0-9][0-9][0-9].lean'))
    if indices is not None: tiles=[p for p in tiles if int(p.stem[4:]) in indices]
    rows=[];start=time.monotonic()
    batches=[['Reinmann.RectangleModel','XiRectangle.Cover']]
    for i in range(0,len(tiles),jobs):
        selected=tiles[i:i+jobs]
        for suffix in ('Gamma','Terms0','Terms1','Terms2','Terms3','Zeta',''):
            batches.append(['XiRectangle.'+p.stem+suffix for p in selected])
    if indices is None: batches.append(['XiRectangle'])
    for i,targets in enumerate(batches):
        before=time.monotonic();log=output/f'batch_{i:03}.log'
        with log.open('w') as stream:
            result=subprocess.run(['lake','build',*targets],cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
        rows.append({'targets':targets,'seconds':time.monotonic()-before,'returncode':result.returncode,
                     'log':str(log.relative_to(ROOT)) if log.is_relative_to(ROOT) else str(log)})
        receipt={'status':'complete' if result.returncode==0 and i+1==len(batches) else 'in_progress',
                 'jobs':jobs,'wall_seconds':time.monotonic()-start,'rows':rows,
                 'tiles_source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in tiles}}
        if result.returncode: receipt['status']='failed'
        (output/'timings.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(rows[-1]),flush=True)
        if result.returncode: raise SystemExit(result.returncode)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--jobs',type=int,default=2)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--tiles',help='optional comma-separated pilot subset; skips final theorem')
    a=p.parse_args()
    run(a.jobs,a.output.resolve(),None if a.tiles is None else set(map(int,a.tiles.split(','))))
