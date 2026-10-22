"""Prepare and check the complete v3 release; no remote mutation is performed."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

from capture_finite_band_ci import check_gate, verify

ROOT = Path(__file__).resolve().parents[2]
PIN = 'b4ec4a3920973faae02d4d9f3a56456886df49c9'
RUN = 39733278869
OUT = ROOT/'research/prime_spectral/verification_2026_10_22_formal_pf97_release'
PACKET = ROOT/'research/prime_spectral/verification_2026_10_22_pf97_closeout'
PDF = 'formal-split-pair-finite-pf.pdf'
ARCHIVE = 'formal-split-pair-finite-pf-source-b4ec4a3.tar.gz'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def blob(name):
    return subprocess.check_output(['git', 'show', PIN+':'+name], cwd=ROOT)


def check_archive(data):
    with tarfile.open(fileobj=io.BytesIO(data), mode='r:gz') as ar:
        names = ar.getnames()
        assert len(names) == len(set(names)) and all(m.isfile() for m in ar.getmembers())
        assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names)
        manifest = json.loads(ar.extractfile('SOURCE_MANIFEST.json').read())
        assert manifest['source_commit'] == PIN and manifest['CI_run'] == RUN
        assert manifest['tile_source_modules'] == {'XiRectangle': 308, 'XiBand58': 63, 'XiBand97': 469}
        assert set(names) == set(manifest['files_sha256']) | {'SOURCE_MANIFEST.json'}
        for name, expected in manifest['files_sha256'].items():
            assert sha(ar.extractfile(name).read()) == expected, name
        bindings = json.loads(ar.extractfile('verification/proof_CI/proof_source_sha256.json').read())
        assert len(bindings) == 1192
        for name, expected in bindings.items():
            assert sha(ar.extractfile('source/'+name).read()) == expected, name
        assert 'source/Reinmann/PNTPlus/LICENSE' in names
        assert 'source/Reinmann/PNTPlus/UPSTREAM.json' in names
        return manifest


def gate():
    verify(PACKET)
    ci = json.loads(subprocess.check_output(['gh', 'run', 'view', str(RUN), '--repo',
        'sciencenerd-des/reinmann', '--json', 'headSha,status,conclusion,jobs,url'], cwd=ROOT))
    check_gate(ci, PIN, [58, 97])
    return ci


def prepare():
    ci = gate()
    paper = ROOT/'paper/formal_split_pair/v3'
    tex, pdf = (paper/'main.tex').read_bytes(), (paper/'main.pdf').read_bytes()
    visual = json.loads((OUT/'paper_visual_review.json').read_text())
    assert visual['tex_sha256'] == sha(tex) and visual['pdf_sha256'] == sha(pdf)
    assert visual['pages_rendered_and_inspected'] == 10 and not visual['external_human_review_completed']
    assert b'version 3 draft' not in tex and b'local, unpublished' not in tex
    assert b'Unreviewed formalization preprint, version 3' in tex and PIN.encode() in tex
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', PIN], cwd=ROOT, text=True).splitlines()
    bindings = json.loads((PACKET/'proof_source_sha256.json').read_text())
    selected = set(bindings)
    selected |= {p for p in paths if p.startswith(('Reinmann/PNTPlus/', 'scripts/'))}
    selected |= {p for p in paths if p.startswith('experiments/prime_spectral/') and p.endswith('.py')}
    selected |= {p for p in paths if p.startswith('bridges/openai-seven-eighths/') and p.endswith(('.py','.toml','.json','.md'))}
    selected |= {'README.md','AGENTS.md',
        'research/prime_spectral/verification_2026_10_21_finite_bands/pf58_plan.json',
        'research/prime_spectral/verification_2026_10_21_finite_bands/pf97_plan.json',
        'research/prime_spectral/verification_2026_10_19_rectangle/cover_plan.json',
        'research/prime_spectral/PNT_HADAMARD_BACKPORT_2026_10_20.md'}
    assert selected <= set(paths), sorted(selected-set(paths))
    files = {'source/'+p:blob(p) for p in sorted(selected)}
    for name, expected in bindings.items():
        assert sha(files['source/'+name]) == expected, name
    counts = {lib:sum(n.startswith('source/'+lib+'/Tile') and n.endswith('.lean') for n in files)
              for lib in ['XiRectangle','XiBand58','XiBand97']}
    assert counts == {'XiRectangle':308,'XiBand58':63,'XiBand97':469}
    for p in PACKET.rglob('*'):
        if p.is_file():files['verification/proof_CI/'+str(p.relative_to(PACKET))] = p.read_bytes()
    for name in ['main.tex','main.pdf','CHANGES.md','RELEASE_GATE.md']:
        files['paper/'+name]=(paper/name).read_bytes()
    files['verification/ci_current.json']=(json.dumps(ci,indent=2)+'\n').encode()
    files['verification/paper_visual_review.json']=(OUT/'paper_visual_review.json').read_bytes()
    for name in ['prepare_formal_pf97_release.py','publish_formal_pf97_version.py']:
        files['release_tools/'+name]=(ROOT/'experiments/prime_spectral'/name).read_bytes()
    readme=f'''Unreviewed formalization preprint, version 3.0.0 (22 October 2026).
Proof source: {PIN}; Lean and Mathlib v4.30.0.
CI: {ci['url']}; all 34 jobs passed, including no-rebuild assembly and audits.

This package contains standalone paper/main.tex and main.pdf, every pinned Lean
source/configuration binding, all 840 numerical tile part modules, bounded
build scripts, rational plans, upstream attribution, and the complete raw CI
and axiom-audit receipts. Check every member against SOURCE_MANIFEST.json.
All 1192 proof-source/configuration bindings are also checked against the
included exact-proof-commit map. No compiled proof artifacts are included.

Fresh kernel reproduction from source/ (requires elan and the pinned toolchain):
  lake exe cache get
  lake build
  bash scripts/verify_axiom_clean.sh
  python3 experiments/prime_spectral/build_xi_rectangle.py --jobs 2 --output tmp/rectangle
  python3 experiments/prime_spectral/build_finite_band.py --rank 58 --jobs 2 --output tmp/band58
  python3 experiments/prime_spectral/build_finite_band.py --rank 97 --jobs 2 --output tmp/band97
  lake build Reinmann.XiFinitePFCertified
  lake env lean ../verification/proof_CI/PF58/Audit.lean
  lake env lean ../verification/proof_CI/PF97/Audit.lean
The numerical rebuild is substantial. Gamma tiles are serialized by the bounded
scripts; the pinned workflow records the parallel hosted replay. The live
source-provenance verifiers additionally require an actual Git checkout at the
proof pin; raw audit inputs above work with the extracted sources. Historical
standalone adapters for the separate Lean 4.34.1 external replay are not default
root imports and do not enter the Lean 4.30 finite-PF proofs.

The root audit covers 2643 declarations. Separate PF58/PF97 audits cover 47896
and 363579 distinct implementation theorem constants, including private generated
ones and canonical entry points; these are not counts of new mathematical results.
Only propext, Classical.choice and Quot.sound occur in the claimed proof chain.
All ordered minors through ranks 43, 58 and 97 are nonnegative for ordinary
folded-Xi coefficients. The full strip is certified only through 14.1; higher
right-hand boxes reach 19 and 32 and allow critical-line zeros. Platt--Trudgian's
published height-3e12 computation gives a much larger classical PF benchmark;
these small ranks measure formal coverage, not new mathematical knowledge.
The split-pair theorem retains its simple selected zeros and isolated boundary
tie. No RH proof, unbounded-rank PF, Green budget, or Lean DH atlas is claimed.

Paper CC-BY-4.0; code Apache-2.0 with upstream PNT+ authorship preserved in
source/Reinmann/PNTPlus/. AI assistance and lack of completed external human
peer review are disclosed. Historical README/status snapshots inside source/
are exact proof-commit bytes; the completed CI receipts supersede their then-
pending labels. Earlier published versions and the DH-controls record are
unchanged. This package's publication state is established by its Zenodo record.
'''.encode()
    files['README_RELEASE.txt']=readme
    inner={'source_commit':PIN,'CI_run':RUN,'toolchain':'leanprover/lean4:v4.30.0',
           'tile_source_modules':counts,'proof_source_bindings':len(bindings),
           'files_sha256':{n:sha(b) for n,b in sorted(files.items())}}
    files['SOURCE_MANIFEST.json']=(json.dumps(inner,indent=2)+'\n').encode()
    buffer=io.BytesIO()
    with tarfile.open(fileobj=buffer,mode='w',format=tarfile.PAX_FORMAT) as ar:
        for name,data in sorted(files.items()):
            info=tarfile.TarInfo(name);info.size=len(data);info.mtime=0
            info.mode=0o755 if name.endswith('.sh') else 0o644
            ar.addfile(info,io.BytesIO(data))
    archive=gzip.compress(buffer.getvalue(),mtime=0)
    check_archive(archive)
    release=OUT/'release';release.mkdir(exist_ok=False)
    public={PDF:pdf,ARCHIVE:archive,'README_RELEASE.txt':readme}
    outer={'kind':'formalization_release_file_manifest','version':'3.0.0','source_commit':PIN,
           'CI_run':RUN,'unreviewed_preprint':True,
           'files':{n:{'bytes':len(b),'sha256':sha(b)} for n,b in public.items()}}
    public['FORMAL_FINITE_PF_RELEASE.json']=(json.dumps(outer,indent=2)+'\n').encode()
    for name,data in public.items():(release/name).write_bytes(data)
    receipt={'status':'local_release_package_verified','source_commit':PIN,'CI_run':RUN,
             'archive_members':len(files),'proof_source_bindings':1192,'tile_source_modules':counts,
             'all_archive_members_read_back_and_verified':True,
             'files':{n:{'bytes':len(b),'sha256':sha(b)} for n,b in public.items()}}
    (OUT/'package_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--prepare',action='store_true')
    p.add_argument('--check-archive',type=Path);a=p.parse_args()
    if a.check_archive:print('Complete source archive verified:',check_archive(a.check_archive.read_bytes())['source_commit'])
    elif a.prepare:prepare()
    else:p.error('Specify --prepare or --check-archive')
