"""Wait for the complete tile replay, then check final imports and all axioms."""
import hashlib
import json
from pathlib import Path
import subprocess
import time

OUT=Path('research/prime_spectral/verification_2026_10_19_rectangle')
result_path=OUT/'postbuild_replay.json'
if result_path.exists():raise FileExistsError(result_path)
while True:
    try:receipt=json.loads((OUT/'parallel/timings.json').read_text())
    except json.JSONDecodeError:
        time.sleep(1)
        continue
    if receipt['status']=='failed':raise SystemExit('Tile replay failed; no final audit attempted')
    if receipt['status']=='complete':break
    time.sleep(10)
assert len(receipt['tiles_source_sha256'])==44
assert receipt['rows'][-1]['targets']==['XiRectangle']
assert all(row['returncode']==0 for row in receipt['rows'])
result={'full_build_receipt_sha256':hashlib.sha256((OUT/'parallel/timings.json').read_bytes()).hexdigest(),
        'audit_source_sha256':hashlib.sha256((OUT/'AllNewAxioms.lean').read_bytes()).hexdigest(),
        'rows':[]}
for command,filename in [(['lake','build','XiRectangle'],'rectangle_build.log'),
                         (['lake','env','lean',str(OUT/'AllNewAxioms.lean')],'all_new_axioms.log')]:
    start=time.monotonic()
    with (OUT/filename).open('w') as stream:
        completed=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT)
    row={'command':command,'log':str(OUT/filename),'returncode':completed.returncode,
         'active_seconds':time.monotonic()-start}
    result['rows'].append(row)
    result_path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(row),flush=True)
    if completed.returncode:raise SystemExit(completed.returncode)
