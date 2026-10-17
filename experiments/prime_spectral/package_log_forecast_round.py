"""Deterministic local capsule of the current verified scientific closure."""
import gzip,hashlib,io,json,tarfile
from pathlib import Path
from verify_log_forecast_round import ROOT,OUT,MANIFEST,run,sha


def package():
    m=run(False);files={ROOT/n for n in m['artifacts_sha256']}|{MANIFEST}
    prefix='dh-log-forecast-2026-10-17';target=ROOT/'tmp/log-forecast'/f'{prefix}.tar.gz';target.parent.mkdir(parents=True,exist_ok=True)
    readme=(ROOT/OUT/'REPRODUCTION.md').read_bytes();expected={prefix+'/'+str(p.relative_to(ROOT)):sha(p) for p in files};expected[prefix+'/REPRODUCTION_CAPSULE.md']=hashlib.sha256(readme).hexdigest()
    with target.open('wb') as raw,gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=6) as zipped,tarfile.open(fileobj=zipped,mode='w') as a:
        for p in sorted(files):
            info=tarfile.TarInfo(prefix+'/'+str(p.relative_to(ROOT)));info.size=p.stat().st_size;info.mode=0o644
            with p.open('rb') as f:a.addfile(info,f)
        info=tarfile.TarInfo(prefix+'/REPRODUCTION_CAPSULE.md');info.size=len(readme);info.mode=0o644;a.addfile(info,io.BytesIO(readme))
    with tarfile.open(target,'r:gz') as a:
        members=a.getmembers();assert len(members)==len(expected) and {x.name for x in members}==set(expected)
        for x in members:assert x.isfile() and hashlib.file_digest(a.extractfile(x),'sha256').hexdigest()==expected[x.name]
    d={'status':'local_log_forecast_capsule_all_members_verified','file':str(target),'bytes':target.stat().st_size,'sha256':sha(target),'members':len(expected),'scope':'Local capsule only; no public upload or publication. Private correspondence remains outside the scientific closure.'}
    (ROOT/'tmp/log-forecast/capsule_receipt.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))


if __name__=='__main__':package()
