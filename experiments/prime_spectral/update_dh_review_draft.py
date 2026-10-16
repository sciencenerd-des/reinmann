"""Replace checked draft files; human-review and Publish gates remain closed."""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.parse import urlparse
import requests
from verify_second_band_round import ROOT,OUT,MANIFEST,run,sha
from package_second_band_revision import verify_bundle


def update(bundle):
    manifest=run(False);verify_bundle(bundle,manifest)
    old=ROOT/'research/prime_spectral/verification_2026_10_15_split_pair/zenodo_draft_receipt.json'
    identity=json.loads(old.read_text());identifier=int(identity['id']);base=f'https://zenodo.org/api/deposit/depositions/{identifier}'
    session=requests.Session();session.headers.update({'Authorization':'Bearer '+Path.home().joinpath('.config/zenodo/token').read_text().strip(),'Connection':'close'})
    def request(method,url,**kwargs):
        if urlparse(url).hostname!='zenodo.org':raise ValueError('unexpected host')
        try:r=session.request(method,url,timeout=(30,300),**kwargs)
        except requests.RequestException as e:raise RuntimeError(type(e).__name__) from None
        if r.status_code not in (200,201,202):raise RuntimeError(f'Zenodo HTTP {r.status_code}')
        return r.json()
    draft=request('GET',base)
    if draft['submitted'] or draft['state']!='unsubmitted':raise ValueError('draft is not unpublished')
    draft=request('PUT',base,json={'metadata':json.loads((ROOT/'paper/zenodo_dh_controls.json').read_text())})
    files=[ROOT/'paper/dh_controls_paper.pdf',bundle];rows=[]
    for p in files:
        with p.open('rb') as f:md5=hashlib.file_digest(f,'md5').hexdigest()
        with p.open('rb') as f:d=request('PUT',draft['links']['bucket']+'/'+p.name,data=f)
        if d['checksum'].removeprefix('md5:')!=md5 or int(d['size'])!=p.stat().st_size:raise ValueError('upload mismatch')
        rows.append({'name':p.name,'bytes':p.stat().st_size,'sha256':sha(p),'server_md5':md5});print('checksum-verified upload',p.name,flush=True)
    final=request('GET',base)
    if final['submitted'] or final['state']!='unsubmitted':raise ValueError('unexpected publication state')
    if {f['filename'] for f in final['files']}!={p.name for p in files}:raise ValueError('draft inventory mismatch')
    for row in rows:
        f=next(x for x in final['files'] if x['filename']==row['name'])
        if f['checksum'].removeprefix('md5:')!=row['server_md5'] or int(f['filesize'])!=row['bytes']:raise ValueError('final remote mismatch')
    receipt={'status':'revised_files_verified_on_unpublished_draft','id':identifier,'submitted':False,'state':final['state'],
             'draft_url':identity['draft_url'],'reserved_doi':identity['reserved_doi'],'files':rows,'local_manifest_sha256':sha(MANIFEST),
             'publication_gate':'Required human read has not occurred. No publish endpoint called; author controls publication.'}
    (OUT/'zenodo_draft_update_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt['status'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--bundle',type=Path,default=ROOT/'tmp/release-round2/dh-controls-2026-10-15.tar.gz')
    update(p.parse_args().bundle)
