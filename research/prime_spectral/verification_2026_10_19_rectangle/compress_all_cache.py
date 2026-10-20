"""Lossless APFS compression of completed, reproducible certificate cache files.
Run from the repository root on macOS. This does not change proof source or bytes.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess

OUT=Path('research/prime_spectral/verification_2026_10_19_rectangle')
if (OUT/'cache_compression_complete.json').exists():raise FileExistsError('Final compression receipt already exists')
receipt=json.loads((OUT/'parallel/timings.json').read_text())
completed=[]
for row in receipt['rows']:
    for target in row['targets']:
        name=target.rsplit('.',1)[-1]
        if target.startswith('XiRectangle.Tile') and name[4:].isdigit() and row['returncode']==0:
            completed.append(name)
rows=[]
for top in (Path('.lake/build/lib/lean/XiRectangle'),Path('.lake/build/ir/XiRectangle')):
    for stem in completed:
        for p in sorted(top.glob(stem+'*')):
            if not p.is_file() or p.suffix not in ('.olean','.c','.json'):continue
            before=p.stat()
            if before.st_size<1000000 or before.st_flags & 0x20:continue
            h=hashlib.sha256(p.read_bytes()).hexdigest()
            q=p.with_name(p.name+'.apfs-compress-verified')
            if q.exists():raise FileExistsError(q)
            subprocess.run(['ditto','--noclone','--hfsCompression',str(p),str(q)],check=True)
            after=q.stat()
            assert hashlib.sha256(q.read_bytes()).hexdigest()==h,(p,'byte mismatch')
            assert before.st_mtime_ns==after.st_mtime_ns,(p,'mtime mismatch')
            os.replace(q,p)
            rows.append({'file':str(p),'logical_bytes':before.st_size,
                         'allocated_before':before.st_blocks*512,'allocated_after':after.st_blocks*512,
                         'sha256_before_and_after':h,'mtime_preserved':True})
result={'scope':'only completed generated cache files; no source edits',
        'completed_tiles':completed,'rows':rows,
        'bytes_saved':sum(r['allocated_before']-r['allocated_after'] for r in rows)}
target=OUT/'cache_compression_complete.json'
if target.exists():raise FileExistsError(target)
target.write_text(json.dumps(result,indent=2)+'\n')
print('Verified cache files',len(rows),'allocated bytes saved',result['bytes_saved'])
