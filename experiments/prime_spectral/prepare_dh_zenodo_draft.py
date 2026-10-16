"""Upload the checked preprint/supplement to the existing UNPUBLISHED draft.

No publish endpoint exists in this script. Credentials stay in headers and
are never included in receipts, arguments, URLs or error output.
"""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.parse import urlparse
import requests
from verify_split_pair_round import ROOT,OUT,run,sha
from package_dh_controls import verify_bundle


def upload(bundle):
    manifest=run(False)
    verify_bundle(bundle,manifest)
    receipt_path=OUT/'zenodo_draft_receipt.json'
    receipt=json.loads(receipt_path.read_text());identifier=int(receipt['id'])
    base=f'https://zenodo.org/api/deposit/depositions/{identifier}'
    session=requests.Session()
    session.headers['Authorization']='Bearer '+Path.home().joinpath('.config/zenodo/token').read_text().strip()
    def checked(method,url,**kwargs):
        if urlparse(url).hostname!='zenodo.org':raise ValueError('unexpected upload host')
        try:r=session.request(method,url,timeout=60,**kwargs)
        except requests.RequestException as error:raise RuntimeError(type(error).__name__) from None
        if r.status_code not in (200,201,202):raise RuntimeError(f'Zenodo HTTP {r.status_code}')
        return r.json()
    d=checked('GET',base)
    if d['submitted'] or d['state']!='unsubmitted':raise ValueError('draft is no longer unpublished')
    metadata=json.loads((ROOT/'paper/zenodo_dh_controls.json').read_text())
    d=checked('PUT',base,json={'metadata':metadata})
    bucket=d['links']['bucket'];records=[]
    for p in [ROOT/'paper/dh_controls_paper.pdf',bundle]:
        md5=hashlib.file_digest(p.open('rb'),'md5').hexdigest()
        with p.open('rb') as f:r=checked('PUT',bucket+'/'+p.name,data=f)
        actual=r.get('checksum','').removeprefix('md5:')
        if actual!=md5 or int(r['size'])!=p.stat().st_size:raise ValueError('uploaded bytes/checksum mismatch')
        records.append({'name':p.name,'bytes':p.stat().st_size,'sha256':sha(p),'server_md5':actual})
        print('uploaded and checksum-verified',p.name,flush=True)
    final=checked('GET',base)
    if final['submitted'] or final['state']!='unsubmitted':raise ValueError('unexpected publication state')
    receipt.update(status='checked_files_uploaded_to_unpublished_draft',submitted=False,state=final['state'],files=records,
                   reserved_doi=final['metadata']['prereserve_doi']['doi'])
    receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
    print('Unpublished draft ready:',receipt['draft_url'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--bundle',type=Path,default=ROOT/'tmp/release/dh-controls-2026-10-15.tar.gz')
    upload(p.parse_args().bundle)
