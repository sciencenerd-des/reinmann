"""Verify the complete scientific base plus its publication-only update."""
import argparse,hashlib,json
from pathlib import Path

def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify(root):
 root=root.resolve();m=json.loads((root/'DH_PUBLICATION_UPDATE.json').read_text())
 def path(name):
  p=(root/name).resolve()
  if not p.is_relative_to(root):raise ValueError('unsafe path: '+name)
  return p
 base=path(m['base_manifest']);assert sha(base)==m['base_manifest_sha256']
 previous=json.loads(base.read_text());updates=m['publication_only_replacements']
 allowed={'paper/dh_controls_paper.tex','paper/dh_controls_paper.pdf','paper/zenodo_dh_controls.json','paper/DH_CONTROLS_REPRODUCTION.md'}
 assert set(updates)==allowed
 for name,old_hash in previous['artifacts_sha256'].items():
  if name in updates:
   item=updates[name];assert item['old_sha256']==old_hash and sha(path(item['historical_path']))==old_hash,name
   assert sha(path(name))==item['new_sha256'],name
  else:assert sha(path(name))==old_hash,name
 for name,digest in m['release_artifacts_sha256'].items():assert sha(path(name))==digest,name
 auth=json.loads(path(m['authorization_file']).read_text());assert auth['human_review_prerequisite_waived'] and not auth['human_review_completed']
 text=path('paper/dh_controls_paper.tex').read_text();assert 'unreviewed preprint' in text and 'is required before the' not in text
 print('Complete scientific base and publication-only update verified:',len(previous['artifacts_sha256']),'base artifacts;',len(m['release_artifacts_sha256']),'release artifacts')
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=Path.cwd());verify(p.parse_args().root)
