"""Bind fresh frozen-release executions and independently check their coverage."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import shutil
import zipfile

BASE=Path('tmp/liu_audit')
PACKAGE=BASE/'extracted/w200-pub-2026-09-14'
OUT=Path('research/prime_spectral/verification_2026_10_15_split_pair')


def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for part in iter(lambda:f.read(1024*1024),b''):h.update(part)
    return h.hexdigest()


def run():
    frozen=BASE/'certified-weil-positivity-b6cd2183c1e79c6c27a34267812a7b2d73ed1b59/frozen-manifest.json'
    manifest=json.loads(frozen.read_text())
    if sha(BASE/'w200-frozen-artifact.zip')!=manifest['archive']['sha256']:
        raise ValueError('frozen archive identity changed')
    for entry in manifest['members']:
        name=entry['archiveMember'];relative=Path(name).relative_to('w200-pub-2026-09-14')
        p=PACKAGE/relative
        if p.stat().st_size!=entry['bytes'] or sha(p)!=entry['sha256']:
            raise ValueError('frozen scientific input or driver changed: '+name)
    aroot=PACKAGE/'reproduction-a';broot=PACKAGE/'reproduction'
    a=json.loads((aroot/'external-a-result.json').read_text())
    finite=json.loads((aroot/'external-a-full/result.json').read_text())
    res=json.loads((aroot/'external-a-full/res.json').read_text())
    source=json.loads((aroot/'external-a-full/source.json').read_text())
    projection=json.loads((aroot/'external-a-full/projection.json').read_text())
    expected={'coefficient_contributions':126877696,'projection_G_cells':1983872,
              'quadrature_nodes':45056,'res_lower_cells':1983872,
              'res_multiply_accumulate_terms':1864839680,'res_rows':2816}
    if a['status']!='THEOREM_A_RETAINED_REPRODUCTION_PASS' or a['full_run_counts']!=expected or a['fresh_scalar_checks']!=72:
        raise ValueError('Theorem A complete coverage differs')
    # Coefficient replay alone deliberately has full_SRC=False: whole SRC
    # also requires the separately completed projection/PDE stage below.
    if not source['complete'] or source['node_count']!=45056 or source['required_nodes']!=45056 or source['pilot_complete'] or not source['independent_coefficients_enclosed']:
        raise ValueError('source reconstruction incomplete')
    if not projection['complete'] or not projection['full_SRC'] or not projection['independent_projection_replay_complete']:
        raise ValueError('full source-to-matrix projection incomplete')
    if not res['complete'] or not res['finite_RES_verified'] or res['total_rows']!=2816:
        raise ValueError('residual replay incomplete')
    for sector in res['both_parities']:
        if sector['rows']!=1408 or sector['cells']!=991936 or not Fraction(sector['minimum_slack'])>0 or not Fraction(sector['r'])<Fraction(1,2):
            raise ValueError('sector residual or inverse-majorant gate failed')
    schur=finite['conditional_schur']
    ell,complement,cross,epsilon=(Fraction(schur[k]) for k in ['ell','complement_a','cross_b','epsilon'])
    determinant=(ell-epsilon)*(complement-epsilon)-cross*cross
    if epsilon!=Fraction(1,2**151) or determinant<=0 or determinant!=Fraction(schur['determinant']):
        raise ValueError('independent exact Schur determinant check failed')
    b=[]
    expected_b={'moments':1024,'primeCenters':13,'orderedShiftPairs':169,'matrixIntervals':151200,
                'tailCoordinates':896,'tailParityZeros':448,'targetCoordinates':100352,'gramRows':448}
    for name in ['theorem-b-result.json','fast-theorem-b-result.json']:
        d=json.loads((broot/'external-b-full'/name).read_text())
        if d['verdict']!='INDEPENDENT_REPRODUCTION_PASS' or d['countsObserved']!=expected_b or d['exactScalarAssertions']!=56:
            raise ValueError('Theorem B rebuild/verification incomplete')
        b.append({'mode':d['mode'],'counts':d['countsObserved'],'exact_scalar_assertions':56})
    copied=OUT/'liu_fresh_receipts';copied.mkdir(exist_ok=True)
    paths=[aroot/'external-a-result.json',aroot/'external-a-scalars.json']
    paths += [aroot/'external-a-full'/n for n in
              ['result.json','environment.json','execution-manifest.json','source.json','projection.json','res.json']]
    paths += [broot/'external-b-full'/n for n in
              ['theorem-b-result.json','fast-theorem-b-result.json','environment.json','release-execution.json',
               'verification-summary.json','scalar-receipt.json']]
    for p in paths:
        name=('a_' if p.is_relative_to(aroot) else 'b_')+p.name
        shutil.copyfile(p,copied/name)
    # Verify the private zip contains exactly byte-identical original stdlib code.
    original=Path('/Users/biswajitmondal/.local/share/uv/python/cpython-3.12-macos-aarch64-none').resolve()
    archive=BASE/'python312-layout/python312.zip';members=0
    with zipfile.ZipFile(archive) as z:
        for name in z.namelist():
            if hashlib.sha256(z.read(name)).hexdigest()!=sha(original/'lib/python3.12'/name):
                raise ValueError('private standard-library byte change')
            members+=1
    result={'status':'frozen_Liu_A_retained_and_B_clean_full_fast_reproduced',
            'frozen_commit':'b6cd2183c1e79c6c27a34267812a7b2d73ed1b59',
            'archive_sha256':manifest['archive']['sha256'],'immutable_members_rechecked':len(manifest['members']),
            'theorem_A':{'epsilon':'2^-151','half_width':'1','clean_proposal_regeneration':False,
                         'source_and_matrix_reconstruction':True,'full_residual_replay':True,
                         'counts':expected,'exact_scalar_relations':72,'independent_Schur_check':True},
            'theorem_B':{'epsilon':'2^-49162','half_width':'17/16','runs':b},
            'runtime':{'implementation':'CPython 3.12.11 macOS arm64, -I -S -B',
                       'adaptation':'Private byte-identical zipped standard library at the original audit-allowlisted root; no scientific or driver code change, audit bypass or modified acceptance gate.',
                       'stdlib_members_checked':members,'stdlib_zip_sha256':sha(archive),
                       'original_macOS_preflight_failed':'Windows-only Lib/DLLs allowlist rejected dataclasses.py; failed run preserved.'},
            'analytic_review':'Both analytic-source.md files read, with explicit complex normalization, whole-complement/cross bounds, source-error payment, positive congruences and legal-domain return checked in writing; classical external theorems remain dependencies.',
            'input_sha256':{str(p):sha(p) for p in sorted(copied.glob('*.json'))},
            'source_sha256':{'audit_liu_frozen_release.py':sha(Path(__file__))},
            'scope':'Re-execution of frozen author-supplied arithmetic implementations and recorded analytic review. Not a new arithmetic implementation, external human review, formal proof or RH proof.'}
    (OUT/'liu_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'all',len(manifest['members']),'frozen members unchanged',flush=True)


if __name__=='__main__':
    run()
