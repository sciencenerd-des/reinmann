#!/usr/bin/env python3
"""Reassemble the published supplement only after checking every part."""
import argparse,hashlib,json
from pathlib import Path

def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--parts-dir',type=Path,default=Path('.'));ap.add_argument('--output',type=Path);a=ap.parse_args();m=json.loads((a.parts_dir/'DH_SUPPLEMENT_PARTS.json').read_text())
 name=m['archive'];assert Path(name).name==name,'unsafe archive name';target=a.output or a.parts_dir/name
 parts=[]
 for item in m['parts']:
  name=item['filename'];assert Path(name).name==name,'unsafe part name';p=a.parts_dir/name
  assert p.stat().st_size==item['bytes'],'part size mismatch: '+name
  assert digest(p)==item['sha256'],'part checksum mismatch: '+name
  parts.append(p)
 if target.exists():
  assert target.stat().st_size==m['archive_bytes'] and digest(target)==m['archive_sha256'],'existing output mismatch; refusing overwrite'
 else:
  temporary=target.with_name(target.name+'.assembling')
  with temporary.open('xb') as out:
   for p in parts:
    with p.open('rb') as src:
     for block in iter(lambda:src.read(1024*1024),b''):out.write(block)
  assert temporary.stat().st_size==m['archive_bytes'],'archive size mismatch'
  assert digest(temporary)==m['archive_sha256'],'archive checksum mismatch'
  temporary.rename(target)
 print('Verified archive:',target);print('SHA256:',m['archive_sha256']);print('Bytes:',m['archive_bytes'])
if __name__=='__main__':main()
