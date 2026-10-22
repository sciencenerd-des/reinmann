"""Publish v3 only after exact proof, complete supplement and remote-file gates."""
import argparse
import hashlib
import json
from pathlib import Path
import time
from urllib.parse import urlparse, quote

from prepare_formal_pf97_release import ROOT, OUT, PIN, PDF, ARCHIVE, sha, gate, check_archive

OLD = 23516924
CONCEPT = '23449489'
TITLE = 'Split-pair oscillation, the Toeplitz–Jacobi bridge, and Lean-verified finite-order positivity for xi'
RECEIPT = OUT/'publication_receipt.json'


def release_files():
    r=json.loads((OUT/'package_receipt.json').read_text())
    assert r['source_commit']==PIN and r['all_archive_members_read_back_and_verified']
    paths={p.name:p for p in (OUT/'release').iterdir() if p.is_file()}
    assert set(paths)==set(r['files']) and len(paths)==4
    for name,p in paths.items():
        data=p.read_bytes();assert len(data)==r['files'][name]['bytes'] and sha(data)==r['files'][name]['sha256'],name
    assert paths[PDF].read_bytes()==(ROOT/'paper/formal_split_pair/v3/main.pdf').read_bytes()
    visual=json.loads((OUT/'paper_visual_review.json').read_text())
    assert visual['pdf_sha256']==sha(paths[PDF].read_bytes())
    assert visual['tex_sha256']==sha((ROOT/'paper/formal_split_pair/v3/main.tex').read_bytes())
    assert visual['pages_rendered_and_inspected']==10 and not visual['external_human_review_completed']
    check_archive(paths[ARCHIVE].read_bytes())
    return paths


def main(mode):
    import requests
    paths=release_files();gate()
    authed=requests.Session();authed.trust_env=False
    authed.headers.update({'Authorization':'Bearer '+(Path.home()/'.config/zenodo/token').read_text().strip(),'Connection':'close'})
    anonymous=requests.Session();anonymous.trust_env=False;anonymous.headers['Connection']='close'

    def request(method,url,public=False,**kwargs):
        assert urlparse(url).scheme=='https' and urlparse(url).hostname=='zenodo.org'
        session=anonymous if public else authed
        for attempt in range(3 if method in ('GET','PUT','DELETE') else 1):
            try:
                r=session.request(method,url,timeout=(10,180),allow_redirects=False,**kwargs)
            except requests.RequestException as e:
                if method in ('GET','PUT','DELETE') and attempt<2:
                    time.sleep(2**attempt);continue
                raise RuntimeError('Zenodo '+method+' '+type(e).__name__) from None
            if r.status_code in (301,302,303,307,308):
                target=r.headers['Location'];assert urlparse(target).scheme=='https' and urlparse(target).hostname=='zenodo.org'
                return request('GET' if r.status_code==303 else method,target,public=public,**kwargs)
            if public:assert not r.request.headers.get('Authorization')
            if r.status_code in (429,500,502,503,504) and method in ('GET','PUT','DELETE') and attempt<2:
                time.sleep(2**attempt);continue
            if r.status_code not in (200,201,202,204):raise RuntimeError(f'Zenodo {method} HTTP {r.status_code}')
            return r

    def save(receipt):RECEIPT.write_text(json.dumps(receipt,indent=2)+'\n')

    if RECEIPT.exists():receipt=json.loads(RECEIPT.read_text())
    else:
        old=request('GET',f'https://zenodo.org/api/deposit/depositions/{OLD}').json()
        assert old['submitted'] and str(old['conceptrecid'])==CONCEPT
        latest=request('GET',f'https://zenodo.org/api/records/{OLD}/versions/latest',public=True).json()
        assert latest['id']==OLD,'A newer public version exists; do not create a competing branch'
        link=old['links']['latest_draft'];identifier=int(link.rstrip('/').split('/')[-1])
        if identifier==OLD:
            r=request('POST',f'https://zenodo.org/api/deposit/depositions/{OLD}/actions/newversion').json()
            identifier=int(r['links']['latest_draft'].rstrip('/').split('/')[-1])
        assert identifier not in (OLD,23449490,23401370)
        receipt={'id':identifier,'previous_id':OLD,'conceptrecid':CONCEPT,'source_commit':PIN,
                 'status':'new_formalization_version_created_or_resumed','publication_authorized':True}
        save(receipt)
    identifier=receipt['id'];assert identifier not in (OLD,23449490,23401370)
    assert receipt['previous_id']==OLD and receipt['conceptrecid']==CONCEPT
    base=f'https://zenodo.org/api/deposit/depositions/{identifier}'
    draft=request('GET',base).json();assert str(draft['conceptrecid'])==CONCEPT

    def verify_public():
        record=request('GET',f'https://zenodo.org/api/records/{identifier}',public=True).json()
        assert record['metadata']['title']==TITLE and record['metadata']['version']=='3.0.0'
        assert str(record['conceptrecid'])==CONCEPT
        assert {x['key'] for x in record['files']}==set(paths)
        checks=[];downloads=OUT/'public-downloads';downloads.mkdir(exist_ok=True)
        for item in record['files']:
            name=item['key'];data=request('GET',item['links']['self'],public=True).content
            assert sha(data)==sha(paths[name].read_bytes()),name
            if name==ARCHIVE:check_archive(data)
            (downloads/name).write_bytes(data)
            checks.append({'name':name,'bytes':len(data),'sha256':sha(data),'anonymous_download_sha256':sha(data)})
            print('Anonymous public SHA256 verified:',name,flush=True)
        receipt.update(status='published_and_all_anonymous_public_files_verified',doi=record['doi'],
            record_url=f'https://zenodo.org/records/{identifier}',public_files=checks,
            complete_downloaded_source_manifest_verified=True,unreviewed_preprint=True)
        (OUT/'public_record.json').write_text(json.dumps(record,indent=2)+'\n');save(receipt)
        print('Published and anonymously verified:',receipt['doi'],receipt['record_url'],flush=True)

    if draft['submitted']:
        verify_public();return
    assert mode!='verify','Requested public verification of an unpublished draft'
    assert draft['state']=='unsubmitted'
    metadata=dict(upload_type='publication',publication_type='preprint',title=TITLE,
        creators=[dict(name='Mondal, Biswajit')],version='3.0.0',publication_date='2026-10-22',
        access_right='open',license='cc-by-4.0',prereserve_doi=True,
        description='<p><strong>Unreviewed formalization preprint, version 3. No completed external human peer review is claimed.</strong></p><p>Lean formalizations of finite and analytic split-pair oscillation and the Toeplitz–Jacobi bridge, together with an evaluator of the actual completed xi function. The full closed strip rectangle is certified through height 14.1. Finite right-hand boxes [7/8,1] through height 19 and [29/40,1] through height 32 give unconditional nonnegativity of every ordered Toeplitz minor through ranks 58 and 97 for ordinary folded-xi coefficients; PF43 is also retained. Critical-line zeros above 14.1 are allowed.</p><p>These ranks measure formal coverage, not new mathematical information about zeta zeros. Platt–Trudgian (Bull. LMS 53, 2021, doi:10.1112/blms.12460) verified RH through height 3·10^12; the same two-band argument already gives PF order about 9.42·10^12 from that published computation. No Lean certificate at that scale is claimed. No RH proof, unbounded-rank PF, Green budget or Lean DH zero atlas is claimed.</p><p>The split-pair theorem retains its simple selected zeros and isolated boundary-pair assumptions. The separate actual-Xi product and sector application retains multiplicities and preserves attribution to the Apache-2.0 PNT+ Hadamard development. OpenAI’s unrefereed seven-eighths preprint and its separate Lean 4.34.1 replay are cited but are not inputs to these Lean 4.30 finite-PF theorems.</p><p>Proof source b4ec4a3920973faae02d4d9f3a56456886df49c9, Lean/Mathlib v4.30.0. All 34 jobs of GitHub Actions run 39733278869 passed, including no-rebuild final assembly and actual public-theorem audits. The root guard covers 2643 declarations. Separate audits cover 47896 and 363579 implementation theorem constants, including private generated declarations; these are not counts of new mathematical results. Only standard foundational axioms occur in the claimed proof chain. The complete supplement contains all 840 numerical tile part modules, every pinned Lean source/configuration binding, dependency pins, upstream attribution, audit inputs, raw CI receipts and SHA256 manifests. AI assistance is disclosed.</p>',
        keywords=['Toeplitz minors','total positivity','entire functions','certified evaluation','finite-order positivity','Lean','formal verification'],
        related_identifiers=[dict(identifier='https://github.com/sciencenerd-des/reinmann/tree/'+PIN,relation='isSupplementedBy',resource_type='software'),
            dict(identifier='10.1112/blms.12460',relation='references',resource_type='publication-article'),
            dict(identifier='10.5281/zenodo.23401370',relation='references',resource_type='publication-preprint')])
    draft=request('PUT',base,json={'metadata':metadata}).json()
    old_dir=ROOT/'research/prime_spectral/verification_2026_10_20_target_b_closeout/release'
    old_receipt=json.loads((old_dir.parent/'formalization_v2_publication_receipt.json').read_text())
    old_hashes={x['name']:x['sha256'] for x in old_receipt['public_files']}
    bucket=draft['links']['bucket'];backup=OUT/'inherited-backups';backup.mkdir(exist_ok=True)
    for item in draft['files']:
        name=item['filename'];data=request('GET',bucket+'/'+quote(name,safe='')).content
        if name in paths and sha(data)==sha(paths[name].read_bytes()):continue
        assert name in old_hashes and sha(data)==old_hashes[name], 'Unexpected draft content: preserve for author review'
        assert sha((old_dir/name).read_bytes())==old_hashes[name],name
        (backup/name).write_bytes(data)
        request('DELETE',base+'/files/'+item['id'])
    checks=[]
    for name,p in paths.items():
        data=p.read_bytes();current=request('GET',base).json()
        existing=next((x for x in current['files'] if x['filename']==name),None)
        if existing is None:
            uploaded=request('PUT',bucket+'/'+quote(name,safe=''),data=data).json()
            assert uploaded['checksum'].removeprefix('md5:')==hashlib.md5(data).hexdigest(),name
        downloaded=request('GET',bucket+'/'+quote(name,safe='')).content
        assert sha(downloaded)==sha(data),name
        if name==ARCHIVE:check_archive(downloaded)
        checks.append({'name':name,'bytes':len(data),'sha256':sha(data),'download_sha256':sha(downloaded)})
        print('Draft upload/download SHA256 verified:',name,flush=True)
    draft=request('GET',base).json()
    assert not draft['submitted'] and draft['metadata']['title']==TITLE and draft['metadata']['version']=='3.0.0'
    assert {x['filename'] for x in draft['files']}==set(paths)
    receipt.update(status='all_four_draft_files_download_verified',files=checks,
        reserved_doi=draft['metadata']['prereserve_doi']['doi'],
        inherited_files_backed_up_and_original_public_records_preserved=True)
    save(receipt)
    if mode=='publish':
        release_files();gate()
        request('POST',base+'/actions/publish')
        for _ in range(10):
            current=request('GET',base).json()
            if current['submitted']:break
            time.sleep(2)
        assert current['submitted'] and current['state']=='done'
        verify_public()
    else:print('Draft fully verified; reserved DOI:',receipt['reserved_doi'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('stage','publish','verify'))
    main(p.parse_args().mode)
