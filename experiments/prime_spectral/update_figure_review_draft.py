"""Replace the checked unpublished figure revision; never invoke Publish."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from urllib.parse import urlparse
import requests
from verify_figure_revision import ROOT, OUT, MANIFEST, run, sha
from package_figure_revision import verify_bundle


def update(bundle):
    manifest = run(False)
    verify_bundle(bundle, manifest)
    identity = json.loads((ROOT/'research/prime_spectral/verification_2026_10_15_split_pair/zenodo_draft_receipt.json').read_text())
    identifier = int(identity['id'])
    base = f'https://zenodo.org/api/deposit/depositions/{identifier}'
    token = Path.home().joinpath('.config/zenodo/token').read_text().strip()
    session = requests.Session()
    session.headers.update({'Authorization': 'Bearer '+token, 'Connection': 'close'})

    def request(method, url, **kwargs):
        if urlparse(url).hostname != 'zenodo.org':
            raise ValueError('unexpected host')
        try:
            response = session.request(method, url, timeout=(30, 120), **kwargs)
        except requests.RequestException as exc:
            raise RuntimeError(type(exc).__name__) from None
        if response.status_code not in (200, 201, 202):
            raise RuntimeError(f'Zenodo HTTP {response.status_code}')
        return response.json()

    draft = request('GET', base)
    if draft['submitted'] or draft['state'] != 'unsubmitted':
        raise ValueError('draft is not unpublished')
    draft = request('PUT', base, json={'metadata': json.loads((ROOT/'paper/zenodo_dh_controls.json').read_text())})
    files = [ROOT/'paper/dh_controls_paper.pdf', bundle]
    rows = []
    response_path = ROOT/'tmp/release-figures-2026-10-16/upload_response.json'
    for path in files:
        url = draft['links']['bucket']+'/'+path.name
        if urlparse(url).hostname != 'zenodo.org':
            raise ValueError('unexpected bucket host')
        with path.open('rb') as stream:
            md5 = hashlib.file_digest(stream, 'md5').hexdigest()
        # Credentials are passed only through stdin, never argv, a URL or logs.
        config = 'header = '+json.dumps('Authorization: Bearer '+token)+'\nurl = '+json.dumps(url)+'\n'
        result = subprocess.run(['/usr/bin/curl', '--config', '-', '--http1.1', '--silent', '--show-error',
            '--fail-with-body', '--retry', '3', '--retry-all-errors', '--retry-delay', '3',
            '--connect-timeout', '30', '--max-time', '480', '--upload-file', str(path),
            '--output', str(response_path), '--write-out', '%{http_code}'],
            input=config, text=True, capture_output=True)
        if result.returncode or result.stdout.strip() not in ('200', '201'):
            raise RuntimeError(f'upload failed: curl exit {result.returncode}, HTTP {result.stdout.strip()}')
        uploaded = json.loads(response_path.read_text())
        if uploaded['checksum'].removeprefix('md5:') != md5 or int(uploaded['size']) != path.stat().st_size:
            raise ValueError('upload mismatch')
        rows.append({'name': path.name, 'bytes': path.stat().st_size, 'sha256': sha(path), 'server_md5': md5})
        print('checksum-verified upload', path.name, flush=True)
    final = request('GET', base)
    if final['submitted'] or final['state'] != 'unsubmitted':
        raise ValueError('unexpected publication state')
    if {f['filename'] for f in final['files']} != {p.name for p in files}:
        raise ValueError('draft inventory mismatch')
    for row in rows:
        remote = next(x for x in final['files'] if x['filename'] == row['name'])
        if remote['checksum'].removeprefix('md5:') != row['server_md5'] or int(remote['filesize']) != row['bytes']:
            raise ValueError('final remote mismatch')
    run(False)
    receipt = {'status': 'figure_revision_verified_on_unpublished_draft', 'id': identifier,
        'submitted': False, 'state': final['state'], 'draft_url': identity['draft_url'],
        'reserved_doi': identity['reserved_doi'], 'files': rows, 'local_manifest_sha256': sha(MANIFEST),
        'publication_gate': 'Required human read is pending. No publish endpoint called; author controls publication.'}
    (OUT/'zenodo_draft_update_receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(receipt['status'], flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--bundle', type=Path, default=ROOT/'tmp/release-figures-2026-10-16/dh-controls-2026-10-15.tar.gz')
    update(parser.parse_args().bundle)
