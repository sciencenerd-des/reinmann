"""Verify the CI-gated closeout and checksum-bound formalization publication."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'research/prime_spectral/verification_2026_10_20_target_b_closeout'
PIN = '150537bf1d94eced1c22db7660f9c32936372831'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def verify(record=False):
    ci = json.loads((OUT/'ci_run_39470397281.json').read_text())
    expected = {'build-and-verify', 'xi-rectangle-deps', 'xi-rectangle-certificate'}
    expected |= {f'xi-rectangle-shard ({i})' for i in range(11)}
    assert ci['headSha'] == PIN and ci['status'] == 'completed' and ci['conclusion'] == 'success'
    assert len(ci['jobs']) == 14 and {j['name'] for j in ci['jobs']} == expected
    assert all(j['conclusion'] == 'success' and j['status'] == 'completed' for j in ci['jobs'])
    log = gzip.decompress((OUT/'ci_run_39470397281.log.gz').read_bytes())
    binding = json.loads((OUT/'ci_log_receipt.json').read_text())
    assert len(log) == binding['raw_bytes']
    assert hashlib.sha256(log).hexdigest() == binding['raw_sha256']
    assert sha(OUT/'ci_run_39470397281.log.gz') == binding['gzip_sha256']
    assert b'--no-build' in log and b'Reinmann.XiFinitePFCertified.finitePF43' in log
    previous = json.loads((ROOT/'research/prime_spectral/verification_2026_10_19_rectangle/manifest.json').read_text())
    historical = OUT/'historical_40d4803/README.md'
    assert sha(historical) == previous['artifacts_sha256']['README.md']
    assert historical.read_bytes() == subprocess.check_output([
        'git', 'show', '40d48033f14842c88486c257d6cfe39c496bbf66:README.md'], cwd=ROOT)
    with tempfile.TemporaryDirectory(prefix='rh-closeout-replay-') as tmp:
        receipt = Path(tmp)/'receipt.json'
        subprocess.run(['python3', 'experiments/prime_spectral/replay_frozen_research_checkpoints.py',
                        '--output', str(receipt)], cwd=ROOT, check=True, stdout=subprocess.PIPE)
        assert json.loads(receipt.read_text()) == json.loads((OUT/'historical_replay.json').read_text())
    subprocess.run(['python3', 'experiments/prime_spectral/verify_research_gates_round.py'],
                   cwd=ROOT, check=True, stdout=subprocess.PIPE)
    checks = json.loads((OUT/'checks.json').read_text())
    assert len(checks) == 4 and all(x['exit_code'] == 0 for x in checks)
    assert 'all 2608 audited theorems' in (OUT/'root_guard.log').read_text()
    audit = (OUT/'headline_types.log').read_text()
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
    assert len(rows) == 5
    assert all(set(a.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
               for _, a in rows)
    assert any(n == 'Reinmann.XiFinitePFCertified.finitePF43' for n, _ in rows)
    publication = json.loads((OUT/'formalization_v2_publication_receipt.json').read_text())
    assert publication['status'] == 'published_and_anonymous_public_files_verified'
    assert publication['previous_id'] == 23449490 and publication['id'] not in (23449490, 23401370)
    assert publication['complete_downloaded_source_manifest_verified']
    assert publication['source_commit'] == PIN and publication['unreviewed_preprint']
    release = OUT/'release'
    assert len(publication['public_files']) == 4
    for item in publication['public_files']:
        p = release/item['name']
        assert p.stat().st_size == item['bytes']
        assert sha(p) == item['sha256'] == item['anonymous_download_sha256']
    archive = release/'formal-split-pair-rectangle-source-150537b.tar.gz'
    with tarfile.open(fileobj=io.BytesIO(archive.read_bytes()), mode='r:gz') as tar:
        manifest = json.loads(tar.extractfile('SOURCE_MANIFEST.json').read())
        assert manifest['source_commit'] == PIN and manifest['tile_source_modules'] == 308
        for n, h in manifest['files_sha256'].items():
            assert hashlib.sha256(tar.extractfile(n).read()).hexdigest() == h, n
    visual = json.loads((OUT/'paper_visual_review.json').read_text())
    paper = ROOT/'paper/formal_split_pair/v2'
    assert visual['pdf_sha256'] == sha(paper/'main.pdf')
    assert visual['tex_sha256'] == sha(paper/'main.tex')
    assert visual['pages_rendered_and_inspected'] == 7 and not visual['external_human_review_completed']
    assert (release/'formal-split-pair-rectangle.pdf').read_bytes() == (paper/'main.pdf').read_bytes()
    owned = ['README.md', 'research/pseudo_hermitian/RESEARCH_OBJECTIVE.md',
             'paper/formal_split_pair/v2/main.tex', 'paper/formal_split_pair/v2/main.pdf',
             'paper/formal_split_pair/v2/RELEASE_GATE.md',
             'research/prime_spectral/TARGET_B_CI_CLOSEOUT_2026_10_21.md',
             'experiments/prime_spectral/publish_formal_rectangle_version.py',
             'experiments/prime_spectral/verify_target_b_closeout.py']
    bound = {n: sha(ROOT/n) for n in owned}
    bound.update({str(p.relative_to(ROOT)): sha(p) for p in OUT.rglob('*')
                  if p.is_file() and p.name != 'manifest.json'})
    result = dict(status='Target_B_PF43_CI_closeout_and_formalization_v2_publication_verified',
                  proof_source_commit=PIN, ci_run='39470397281', successful_jobs=14,
                  height='141/10', unconditional_finitePF_rank=43,
                  local_PF58_still_has_external_input=True, RH_proved=False,
                  published_doi=publication['doi'], artifacts_sha256=bound)
    p = OUT/'manifest.json'
    if record:
        with p.open('x') as f:
            f.write(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(p.read_text()) == result, 'Closeout differs from immutable receipt'
    print('Verified fourteen-job CI gate, historical replay, current audits and public-file checks;',
          len(bound), 'bindings; DOI', publication['doi'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true')
    verify(parser.parse_args().record)
