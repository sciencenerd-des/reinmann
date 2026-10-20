"""Package the formalization revision only after its exact hosted gate passes.

This prepares local files. It neither creates a Zenodo version nor publishes.
The historical five-page release and its immutable receipts are never changed.
"""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[2]
PIN = '150537bf1d94eced1c22db7660f9c32936372831'
RUN = '39470397281'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--visual-receipt', required=True, type=Path)
    args = p.parse_args()
    ci_bytes = subprocess.check_output([
        'gh', 'run', 'view', RUN, '--repo', 'sciencenerd-des/reinmann',
        '--json', 'headSha,status,conclusion,jobs,url,createdAt,updatedAt'], cwd=ROOT)
    ci = json.loads(ci_bytes)
    expected = {'build-and-verify', 'xi-rectangle-deps', 'xi-rectangle-certificate'}
    expected |= {f'xi-rectangle-shard ({i})' for i in range(11)}
    if (ci['headSha'] != PIN or ci['status'] != 'completed'
            or ci['conclusion'] != 'success'
            or {j['name'] for j in ci['jobs']} != expected or len(ci['jobs']) != 14
            or any(j['status'] != 'completed' or j['conclusion'] != 'success'
                   for j in ci['jobs'])):
        raise SystemExit('Release gate closed: exact main/deps/eleven shards/final run not all successful')
    paper = ROOT/'paper/formal_split_pair/v2'
    tex, pdf = (paper/'main.tex').read_bytes(), (paper/'main.pdf').read_bytes()
    if b'pending' in tex.lower() or PIN.encode() not in tex:
        raise SystemExit('Rebuild the manuscript with the actual successful CI receipt first')
    visual = json.loads(args.visual_receipt.read_text())
    if (visual['pdf_sha256'] != sha(pdf) or visual['tex_sha256'] != sha(tex)
            or visual['pages_rendered_and_inspected'] < 7
            or visual['external_human_review_completed']):
        raise SystemExit('Need a current checksum-bound visual review; do not invent external peer review')
    paths = subprocess.check_output([
        'git', 'ls-tree', '-r', '--name-only', PIN, '--', 'Reinmann', 'Reinmann.lean',
        'XiRectangle', 'XiRectangle.lean', 'LICENSE', 'lean-toolchain', 'lakefile.toml',
        'lake-manifest.json', 'scripts/verify_axiom_clean.sh',
        'experiments/prime_spectral/build_xi_rectangle.py', '.github/workflows/ci.yml'],
        cwd=ROOT, text=True).splitlines()
    files = {'source/'+name: subprocess.check_output(['git', 'show', PIN+':'+name], cwd=ROOT)
             for name in paths}
    assert sum(name.startswith('source/XiRectangle/Tile') and name.endswith('.lean')
               for name in files) == 308
    assert 'source/Reinmann/PNTPlus/LICENSE' in files
    audit_path = 'research/prime_spectral/verification_2026_10_19_rectangle/AllNewAxioms.lean'
    files['source/scripts/RectangleAxioms.lean'] = subprocess.check_output(
        ['git', 'show', PIN+':'+audit_path], cwd=ROOT)
    files['source/scripts/PF43Axioms.lean'] = (
        'import Reinmann.XiFinitePFCertified\n'
        '#print axioms Reinmann.XiFinitePFCertified.finitePF43\n'
        '#check Reinmann.XiFinitePFCertified.finitePF43\n').encode()
    readme = f'''Unreviewed formalization preprint, second version.
Source pin: {PIN}; Lean/Mathlib v4.30.0.
CI: {ci['url']} (main, dependencies, eleven shards and final assembly successful).
Paper CC-BY-4.0; code Apache-2.0, with PNT+ authorship and attribution retained.

Check public file hashes, extract the source archive, then check every extracted
file against SOURCE_MANIFEST.json. In source/ run:
  lake exe cache get
  lake build
  bash scripts/verify_axiom_clean.sh
  python3 experiments/prime_spectral/build_xi_rectangle.py --jobs 2 --output rectangle-build
  lake build Reinmann.XiFinitePFCertified
  lake env lean scripts/RectangleAxioms.lean
  lake env lean scripts/PF43Axioms.lean
The optional tile build is substantial; all 308 numerical tile source modules
are included. Dependency versions are pinned by lake-manifest.json. The root
guard audits 2608 theorem rows; the numerical and PF43 audits are separate.

The split-pair theorem assumes simple selected zeros and an isolated boundary
modulus tie. The independent actual-Xi product/sector application retains
analytic multiplicities. The closed height-14.1 rectangle and unconditional
PF43 formalize classical facts. PF58 retains the external seven-eighths input.
No RH proof, unbounded-rank positivity or Lean DH zero atlas is claimed.
AI assistance is disclosed; completed external human peer review is not claimed.
The earlier version remains DOI 10.5281/zenodo.23449490; this package is a new
version candidate until actual publication and public downloads are verified.
'''.encode()
    files.update({'paper/main.tex': tex, 'paper/main.pdf': pdf,
                  'verification/ci_150537b.json': ci_bytes,
                  'verification/paper_visual_review.json': args.visual_receipt.read_bytes(),
                  'README_RELEASE.txt': readme})
    inner = dict(source_commit=PIN, toolchain='leanprover/lean4:v4.30.0',
                 root_audit_rows=2608, tile_source_modules=308,
                 files_sha256={name: sha(data) for name, data in sorted(files.items())})
    files['SOURCE_MANIFEST.json'] = (json.dumps(inner, indent=2)+'\n').encode()
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode='w', format=tarfile.PAX_FORMAT) as archive:
        for name, data in sorted(files.items()):
            info = tarfile.TarInfo(name)
            info.size, info.mtime = len(data), 0
            info.mode = 0o755 if name.endswith('.sh') else 0o644
            archive.addfile(info, io.BytesIO(data))
    zipped = gzip.compress(buffer.getvalue(), mtime=0)
    with tarfile.open(fileobj=io.BytesIO(zipped), mode='r:gz') as archive:
        assert set(archive.getnames()) == set(files)
        for name, expected_hash in inner['files_sha256'].items():
            assert sha(archive.extractfile(name).read()) == expected_hash, name
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    public = {'formal-split-pair-rectangle.pdf': pdf,
              'formal-split-pair-rectangle-source-150537b.tar.gz': zipped,
              'README_RELEASE.txt': readme}
    outer = dict(status='local_release_files_verified_not_uploaded_or_published',
                 source_commit=PIN, ci_run=RUN,
                 files={n: dict(bytes=len(b), sha256=sha(b)) for n, b in public.items()})
    public['FORMAL_RECTANGLE_RELEASE.json'] = (json.dumps(outer, indent=2)+'\n').encode()
    for name, data in public.items():
        (output/name).write_bytes(data)
    print(json.dumps(outer, indent=2))


if __name__ == '__main__':
    main()
