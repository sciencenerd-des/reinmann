"""Verify the Target A replay and the first finite-PF sector transport lemma."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'research/prime_spectral/verification_2026_10_20_sector'
PARENT=ROOT/'research/prime_spectral/verification_2026_10_19_rectangle/manifest.json'
PIN='40d48033f14842c88486c257d6cfe39c496bbf66'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def check(record=False):
    parent=json.loads(PARENT.read_text())
    assert len(parent['artifacts_sha256'])==1759
    for n,h in parent['artifacts_sha256'].items():
        p=ROOT/n
        if sha(p)!=h:
            # The authorized post-CI README update has a separate historical copy.
            assert n=='README.md',('Changed parent artifact',n)
            p=ROOT/'research/prime_spectral/verification_2026_10_20_target_b_closeout/historical_40d4803'/n
            assert hashlib.sha256(subprocess.check_output(['git','show',PIN+':'+n],cwd=ROOT)).hexdigest()==h
        assert sha(p)==h,n
    verifier=ROOT/'experiments/prime_spectral/verify_xi_rectangle.py'
    assert sha(verifier)==parent['artifacts_sha256'][str(verifier.relative_to(ROOT))]
    spec=importlib.util.spec_from_file_location('rectangle_audit',verifier)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    for source,log in [('TargetAReview.lean','target_a_axioms.log'),('SectorLimitAudit.lean','limit_axioms.log')]:
        names=re.findall(r'^#print axioms (\S+)',(OUT/source).read_text(),re.M)
        module.audit(OUT/log,names)
    for name in ['replay.json','default_checks.json']:
        data=json.loads((OUT/name).read_text())
        assert data['rows'] and all(r['returncode']==0 for r in data['rows'])
        for row in data['rows']:
            assert 'error:' not in (ROOT/row['log']).read_text(),row
    source=ROOT/'Reinmann/FinitePFLimits.lean'
    assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom)\b',module.strip_comments(source.read_text()))
    sources=['Reinmann/SplitPairMixedRows.lean','Reinmann/AnalyticSplitPair.lean','Reinmann/AnalyticToeplitzJacobi.lean']
    for n in sources:
        assert sha(ROOT/n)==hashlib.sha256(subprocess.check_output(['git','show',PIN+':'+n],cwd=ROOT)).hexdigest(),n
    paths=[source,PARENT,Path(__file__).resolve(),ROOT/'research/prime_spectral/TARGET_B_CLOSEOUT_AND_SECTOR_2026_10_20.md']
    paths += [p for p in OUT.rglob('*') if p.is_file() and p.name!='manifest.json']
    result={'proof_parent_commit':PIN,'parent_bindings_verified':1759,
            'Target_A_mixed_row_and_entire_extension_proved':True,
            'new_theorem':'Reinmann.finitePF_of_tendsto',
            'new_theorem_standard_axioms_only':True,'KatkovaSectorBridge_43_proved':False,
            'CI_closeout_status':'conditional patch prepared; no successful hosted CI asserted',
            'height_increased':False,'new_Zenodo_version_published':False,'RH_proved':False,
            'artifacts_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(set(paths))}}
    target=OUT/'manifest.json'
    if record:
        if target.exists():raise FileExistsError(target)
        target.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(target.read_text())==result,'Manifest mismatch'
    print('Verified Target A replay, PF limit lemma and',len(result['artifacts_sha256']),'bindings; sector bridge remains open')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',action='store_true')
    check(parser.parse_args().record)
