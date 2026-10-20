"""Stage and optionally publish version two after exact CI and file verification.

Only a new version of the formalization record is modified. The original
formalization and DH-controls public records are never edited.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'research/prime_spectral/verification_2026_10_20_target_b_closeout'
RELEASE = OUT/'release'
OLD = 23449490
CONCEPT = '23449489'
PIN = '150537bf1d94eced1c22db7660f9c32936372831'
TITLE = 'Split-pair oscillation, the Toeplitz–Jacobi bridge, and a Lean-verified low zero-free rectangle'


def digest(data, algorithm='sha256'):
    return hashlib.new(algorithm, data).hexdigest()


def check_supplement(data):
    with tarfile.open(fileobj=io.BytesIO(data), mode='r:gz') as archive:
        manifest = json.loads(archive.extractfile('SOURCE_MANIFEST.json').read())
        assert manifest['source_commit'] == PIN and manifest['tile_source_modules'] == 308
        assert len(archive.getnames()) == len(set(archive.getnames()))
        assert set(archive.getnames()) == set(manifest['files_sha256']) | {'SOURCE_MANIFEST.json'}
        for name, expected in manifest['files_sha256'].items():
            assert digest(archive.extractfile(name).read()) == expected, name


def gate():
    ci = json.loads(subprocess.check_output(['gh', 'run', 'view', '39470397281',
        '--repo', 'sciencenerd-des/reinmann', '--json', 'headSha,status,conclusion,jobs'], cwd=ROOT))
    expected = {'build-and-verify', 'xi-rectangle-deps', 'xi-rectangle-certificate'}
    expected |= {f'xi-rectangle-shard ({i})' for i in range(11)}
    assert ci['headSha'] == PIN and ci['status'] == 'completed' and ci['conclusion'] == 'success'
    assert len(ci['jobs']) == 14 and {j['name'] for j in ci['jobs']} == expected
    assert all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in ci['jobs'])
    visual = json.loads((OUT/'paper_visual_review.json').read_text())
    paper = ROOT/'paper/formal_split_pair/v2'
    assert visual['pdf_sha256'] == digest((paper/'main.pdf').read_bytes())
    assert visual['tex_sha256'] == digest((paper/'main.tex').read_bytes())
    assert visual['pages_rendered_and_inspected'] == 7
    assert 'pending' not in (paper/'main.tex').read_text().lower()
    receipt = json.loads((RELEASE/'FORMAL_RECTANGLE_RELEASE.json').read_text())
    assert receipt['source_commit'] == PIN
    for name, info in receipt['files'].items():
        b = (RELEASE/name).read_bytes()
        assert len(b) == info['bytes'] and digest(b) == info['sha256']
    assert (RELEASE/'formal-split-pair-rectangle.pdf').read_bytes() == (paper/'main.pdf').read_bytes()
    check_supplement((RELEASE/'formal-split-pair-rectangle-source-150537b.tar.gz').read_bytes())


def main(do_publish):
    import requests
    gate()
    paths = sorted(RELEASE.iterdir())
    assert len(paths) == 4 and all(p.is_file() for p in paths)
    session = requests.Session()
    session.headers['Authorization'] = 'Bearer '+(Path.home()/'.config/zenodo/token').read_text().strip()

    def request(method, url, **kwargs):
        assert urlparse(url).scheme == 'https' and urlparse(url).hostname == 'zenodo.org'
        try:
            r = session.request(method, url, timeout=(10, 180), **kwargs)
        except requests.RequestException as error:
            raise RuntimeError(type(error).__name__) from None
        if r.status_code not in (200, 201, 202, 204):
            raise RuntimeError(f'Zenodo {method} HTTP {r.status_code}')
        return r

    receipt_path = OUT/'formalization_v2_publication_receipt.json'
    if receipt_path.exists():
        receipt = json.loads(receipt_path.read_text())
    else:
        old = request('GET', f'https://zenodo.org/api/deposit/depositions/{OLD}').json()
        assert old['submitted'] and str(old['conceptrecid']) == CONCEPT
        link = old['links']['latest_draft']
        if int(link.rstrip('/').split('/')[-1]) == OLD:
            new = request('POST', f'https://zenodo.org/api/deposit/depositions/{OLD}/actions/newversion').json()
            link = new['links']['latest_draft']
        identifier = int(link.rstrip('/').split('/')[-1])
        assert identifier not in (OLD, 23401370)
        receipt = dict(id=identifier, previous_id=OLD, conceptrecid=CONCEPT,
                       status='created_or_resumed_unpublished_new_version', source_commit=PIN)
        receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
    identifier = receipt['id']
    assert identifier not in (OLD, 23401370) and receipt['previous_id'] == OLD
    base = f'https://zenodo.org/api/deposit/depositions/{identifier}'
    draft = request('GET', base).json()
    assert str(draft['conceptrecid']) == CONCEPT

    def verify_public():
        r = requests.get(f'https://zenodo.org/api/records/{identifier}', timeout=(10, 90))
        assert r.status_code == 200
        public = r.json()
        assert public['metadata']['title'] == TITLE and public['metadata']['version'] == '2.0.0'
        assert {x['key'] for x in public['files']} == {p.name for p in paths}
        checks = []
        for item in public['files']:
            p = next(p for p in paths if p.name == item['key'])
            url = item['links']['self']
            assert urlparse(url).hostname == 'zenodo.org'
            r = requests.get(url, timeout=(10, 180)); assert r.status_code == 200
            assert digest(r.content) == digest(p.read_bytes())
            if p.name.endswith('.tar.gz'):
                check_supplement(r.content)
            checks.append(dict(name=p.name, bytes=len(r.content), sha256=digest(r.content),
                               anonymous_download_sha256=digest(r.content)))
        receipt.update(status='published_and_anonymous_public_files_verified', doi=public['doi'],
                       record_url=f'https://zenodo.org/records/{identifier}', public_files=checks,
                       complete_downloaded_source_manifest_verified=True, unreviewed_preprint=True)
        receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
        print('Published and anonymously verified:', receipt['doi'], receipt['record_url'], flush=True)

    if draft['submitted']:
        verify_public()
        return
    assert draft['state'] == 'unsubmitted'
    metadata = dict(upload_type='publication', publication_type='preprint',
        title=TITLE, creators=[dict(name='Mondal, Biswajit')], version='2.0.0',
        publication_date='2026-10-21', access_right='open', license='cc-by-4.0', prereserve_doi=True,
        description='<p><strong>Unreviewed formalization preprint, version 2. No completed external human peer review is claimed.</strong></p><p>Lean formalizations of finite and analytic split-pair oscillation and the Toeplitz–Jacobi bridge, together with an evaluator of the actual completed xi function, a closed zero-free rectangle 0 ≤ Re(s) ≤ 1, |Im(s)| ≤ 14.1, and unconditional Pólya-frequency nonnegativity through rank 43 for ordinary folded-xi coefficients. These finite conclusions formalize classical facts and do not prove RH.</p><p>The split-pair theorem retains simple selected zeros and an isolated boundary-pair modulus tie. The separate actual-Xi sector application retains multiplicities. Its normalized genus-zero product and inverse-zero summability use an attributed Apache-2.0 backport of the PNT+ Hadamard development; upstream proof credit is retained. No Lean-certified DH zero atlas or unconditional local PF58 is claimed.</p><p>Proof source commit 150537bf1d94eced1c22db7660f9c32936372831, Lean/Mathlib v4.30.0. All fourteen jobs of GitHub Actions run 39470397281 succeeded: main build and 2,608-row root axiom guard, shared dependencies, eleven tile shards and final assembly with separate 1,700-declaration rectangle and explicit PF43 audits. Only the standard foundational axioms are used. The complete source supplement includes all 308 numerical tile source modules, dependency pins, upstream attribution, audit inputs, CI receipts and SHA256 bindings. AI assistance is disclosed.</p>',
        keywords=['Toeplitz minors','total positivity','entire functions','certified evaluation','zero-free rectangle','Lean','formal verification'],
        related_identifiers=[dict(identifier='https://github.com/sciencenerd-des/reinmann/tree/'+PIN,
                                  relation='isSupplementedBy', resource_type='software'),
                             dict(identifier='10.5281/zenodo.23401370', relation='references',
                                  resource_type='publication-preprint')])
    draft = request('PUT', base, json=dict(metadata=metadata)).json()
    # Inherited files belong to this new draft only. Verify their recoverable
    # original-release copies before removing obsolete copies or a name collision.
    old_release = ROOT/'research/prime_spectral/verification_2026_10_18_evaluator_comparison/release'
    old_receipt = json.loads((ROOT/'research/prime_spectral/verification_2026_10_18_evaluator_comparison/formalization_publication_receipt.json').read_text())
    old_hashes = {x['name']: x['sha256'] for x in old_receipt['files']}
    for item in draft['files']:
        name = item['filename']
        local_new = next((p for p in paths if p.name == name), None)
        remote_md5 = item['checksum'].removeprefix('md5:')
        if local_new is not None and remote_md5 == digest(local_new.read_bytes(), 'md5'):
            continue
        assert name in old_hashes, 'Unexpected draft file; preserve for author review'
        original = (old_release/name).read_bytes()
        assert digest(original) == old_hashes[name] and digest(original, 'md5') == remote_md5
        request('DELETE', base+'/files/'+item['id'])
    checks = []
    bucket = draft['links']['bucket']
    for p in paths:
        data = p.read_bytes()
        current = request('GET', base).json()
        existing = next((x for x in current['files'] if x['filename'] == p.name), None)
        if existing is None:
            item = request('PUT', bucket+'/'+p.name, data=data).json()
            assert item['checksum'].removeprefix('md5:') == digest(data, 'md5')
        downloaded = request('GET', bucket+'/'+p.name).content
        assert digest(downloaded) == digest(data)
        if p.name.endswith('.tar.gz'):
            check_supplement(downloaded)
        checks.append(dict(name=p.name, bytes=len(data), sha256=digest(data), download_sha256=digest(downloaded)))
        print('Draft upload/download SHA256 verified:', p.name, flush=True)
    draft = request('GET', base).json()
    assert not draft['submitted'] and draft['metadata']['title'] == TITLE
    assert draft['metadata']['version'] == '2.0.0'
    assert {x['filename'] for x in draft['files']} == {p.name for p in paths}
    receipt.update(status='new_version_draft_all_files_download_verified', files=checks,
                   reserved_doi=draft['metadata']['prereserve_doi']['doi'],
                   inherited_old_files_backed_up_and_original_public_record_preserved=True)
    receipt_path.write_text(json.dumps(receipt, indent=2)+'\n')
    if do_publish:
        gate()
        result = request('POST', base+'/actions/publish').json()
        assert result['submitted'] and result['state'] == 'done'
        verify_public()
    else:
        print('Verified unpublished new version:', identifier, flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publish', action='store_true')
    main(parser.parse_args().publish)
