"""Private zip-stdlib runtime for unmodified Windows-audited frozen drivers.

Copies an existing CPython 3.12 installation. Does not patch scientific or
driver code, disable audits, or mutate the existing interpreter.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import zipfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(source,destination,receipt):
    source=source.resolve()
    if destination.exists():
        raise ValueError('fresh private destination required')
    shutil.copytree(source,destination,symlinks=True)
    stdlib=destination/'lib/python3.12'
    archive=destination/'python312.zip'
    members={}
    with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
        for p in sorted(stdlib.rglob('*.py')):
            relative=p.relative_to(stdlib)
            if 'site-packages' in relative.parts or '__pycache__' in relative.parts:
                continue
            original=source/'lib/python3.12'/relative
            if sha(p)!=sha(original):
                raise ValueError('copied stdlib byte mismatch')
            z.write(p,relative.as_posix())
            members[relative.as_posix()]=sha(p)
    link=destination/'lib/python312.zip'
    if link.exists() or link.is_symlink():
        raise ValueError('unexpected existing runtime zip path')
    os.symlink('../python312.zip',link)
    data={'status':'private_runtime_with_byte_identical_zipped_stdlib',
          'base_interpreter':str(source),'private_interpreter':str(destination/'bin/python3.12'),
          'stdlib_zip_sha256':sha(archive),'stdlib_member_count':len(members),
          'stdlib_members_sha256':members,
          'scope':'Runtime packaging only. Frozen scientific modules, driver bytes and audit rules remain unchanged. Python version and operating system still differ from the documented original Windows environment.'}
    receipt.write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,required=True)
    p.add_argument('--destination',type=Path,required=True)
    p.add_argument('--receipt',type=Path,required=True)
    a=p.parse_args();run(a.source,a.destination,a.receipt)
