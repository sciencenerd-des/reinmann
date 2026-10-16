"""Create a deterministic supplement from the verified manifest closure."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile
from verify_split_pair_round import ROOT,MANIFEST,run,sha


def package(destination):
    manifest=run(False)
    files={ROOT/n for n in manifest['artifacts_sha256']}
    files.add(MANIFEST)
    prefix='dh-controls-2026-10-15'
    destination.parent.mkdir(parents=True,exist_ok=True)
    with destination.open('wb') as raw,gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=6) as zipped,tarfile.open(fileobj=zipped,mode='w',format=tarfile.PAX_FORMAT) as archive:
        for p in sorted(files):
            info=tarfile.TarInfo(prefix+'/'+str(p.relative_to(ROOT)))
            info.size=p.stat().st_size;info.mtime=0;info.mode=0o644;info.uid=info.gid=0;info.uname=info.gname=''
            with p.open('rb') as f:archive.addfile(info,f)
        content=(ROOT/'paper/DH_CONTROLS_REPRODUCTION.md').read_bytes()
        info=tarfile.TarInfo(prefix+'/README.md');info.size=len(content);info.mtime=0;info.mode=0o644
        archive.addfile(info,io.BytesIO(content))
    inventory=verify_bundle(destination,manifest)
    result={'status':'deterministic_supplement_built_and_every_member_verified','file':str(destination),
            'sha256':sha(destination),'bytes':destination.stat().st_size,'members':inventory['members'],
            'scope':'Own source/data and hash-bound fresh Liu receipts. Frozen foreign archive/source are obtained upstream, not redistributed.'}
    print(json.dumps(result,indent=2));return result


def verify_bundle(destination,manifest=None):
    """Read-only check: an old or arbitrary supplied archive must fail closed."""
    if manifest is None:manifest=run(False)
    files={ROOT/n for n in manifest['artifacts_sha256']};files.add(MANIFEST)
    prefix='dh-controls-2026-10-15'
    expected={prefix+'/'+str(p.relative_to(ROOT)):sha(p) for p in files}
    content=(ROOT/'paper/DH_CONTROLS_REPRODUCTION.md').read_bytes()
    expected[prefix+'/README.md']=hashlib.sha256(content).hexdigest()
    with tarfile.open(destination,'r:gz') as archive:
        members=archive.getmembers()
        if len(members)!=len(expected) or set(m.name for m in members)!=set(expected):
            raise ValueError('archive inventory mismatch')
        for m in members:
            if not m.isfile() or Path(m.name).is_absolute() or '..' in Path(m.name).parts:
                raise ValueError('unsafe archive member')
            digest=hashlib.file_digest(archive.extractfile(m),'sha256').hexdigest()
            if digest!=expected[m.name]:raise ValueError('archive byte mismatch: '+m.name)
    return {'status':'current_manifest_bundle_verified','members':len(expected),'sha256':sha(destination)}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=ROOT/'tmp/release/dh-controls-2026-10-15.tar.gz')
    package(p.parse_args().output)
