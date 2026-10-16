"""Current-revision provenance; prior full-paper manifests stay historical."""
from fractions import Fraction
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'research/prime_spectral/verification_2026_10_15_second_band'
PREVIOUS=ROOT/'research/prime_spectral/verification_2026_10_15_split_pair/manifest.json'
MANIFEST=OUT/'manifest.json'
MUTABLE={'paper/dh_controls_paper.tex','paper/dh_controls_paper.pdf','paper/DH_CONTROLS_READINESS.md',
         'paper/DH_CONTROLS_REPRODUCTION.md','paper/zenodo_dh_controls.json','research/RESEARCH_STATUS_2026_10_11.md'}
EXCLUDED={'manifest.json','release_bundle_receipt.json','zenodo_draft_update_receipt.json'}


def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()


def run(record=False):
    previous=json.loads(PREVIOUS.read_text());bound={};seen=set();declarations=0
    for name,digest in previous['artifacts_sha256'].items():
        p=ROOT/name
        if name not in MUTABLE and sha(p)!=digest:raise ValueError('historical scientific artifact changed: '+name)
        bound[p]=sha(p)
    def resolve(name,source=False):
        p=Path(name)
        if not p.is_absolute():p=(ROOT/'experiments/prime_spectral' if source else ROOT)/p
        p=p.resolve()
        if not p.is_relative_to(ROOT):raise ValueError('external path in local declaration')
        return p
    def bind(p,digest):
        nonlocal declarations
        actual=bound.setdefault(p,sha(p))
        if actual!=digest:raise ValueError('hash mismatch: '+str(p.relative_to(ROOT)))
        declarations+=1;inspect(p)
    def visit(node):
        if isinstance(node,list):
            for x in node:visit(x)
        elif isinstance(node,dict):
            for key in ['input_sha256','source_sha256']:
                for name,digest in node.get(key,{}).items():bind(resolve(name,key=='source_sha256'),digest)
            if 'file' in node and 'sha256' in node:bind(resolve(node['file']),node['sha256'])
            for x in node.values():visit(x)
    def inspect(p):
        if p in seen:return
        seen.add(p)
        if p.suffix=='.json' and 'liu_fresh_receipts' not in p.parts and p.name!='manifest.json':visit(json.loads(p.read_text()))
    records=[p for p in OUT.rglob('*.json') if p.name not in EXCLUDED]
    for p in records:inspect(p);bound[p]=sha(p)
    get=lambda n:json.loads((OUT/n).read_text())
    f=get('forecast_assessment.json');assert f['observed_band']==[1536,1972] and f['forecast_passes']==[True,True]
    assert f['nearby_cells']==1620 and f['leading_cosine_signs_matching']==600
    for key in ['b015','b008','b004']:
        a=get(key+'/atlas_H160/atlas.json');r=get(key+'/atlas_replay.json');s=get(key+'/window_search.json')
        assert a['global_count']==123 and a['remaining_count']==0 and a['right_off_line_count']==5
        assert r['status']=='all_contours_and_root_gates_replayed' and r['global_count']==123
        assert s['status']=='common_N192_path_endpoint_certified'
        endpoint=next(x for x in s['records'] if x['C']==s['negative_certificate_C'])
        d=json.loads((ROOT/endpoint['file']).read_text());assert d['status']=='negative_full_form_trial'
        assert any(Fraction(x['normalized_full_form']['hi'])<0 for x in d['sectors'] if 'normalized_full_form' in x)
    log=(OUT/'tests.log').read_text();assert 'Ran 3 tests' in log and log.rstrip().endswith('OK')
    artifacts=set(bound)|{PREVIOUS}|set(p for p in OUT.rglob('*') if p.is_file() and p.name not in EXCLUDED)
    artifacts |= set((ROOT/'experiments/prime_spectral').glob('*.py'))
    artifacts |= {ROOT/n for n in MUTABLE}
    artifacts |= {ROOT/n for n in ['paper/HUMAN_REVIEW_REQUEST.md','paper/LIU_REPLAY_NOTE_DRAFT.md',
          'research/prime_spectral/SECOND_BAND_AND_COLLISION_PATH_2026_10_15.md',
          'research/prime_spectral/POST_PUBLICATION_FORMAL_TARGETS_2026_10_15.md']}
    artifacts |= set((ROOT/'paper/figures').glob('dh_second_band_column.*'))
    artifacts |= set((ROOT/'paper/figures').glob('dh_mixture_collision_path.*'))
    result={'status':'second_band_and_collision_path_revision_verified','previous_manifest_sha256':sha(PREVIOUS),
            'json_roots_checked':len(records),'hash_declarations_checked':declarations,'new_tests_passed':3,
            'second_band':[1536,1972],'nearby_cells':1620,'complete_new_atlases':3,
            'artifacts_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(artifacts)},
            'scope':'Current revision and immutable prior scientific inputs. Prior full-paper manifests bind historical paper revisions. Local preregistration; human read pending; no public post or publication authorized by these checks. Finite support upper bounds, not a limiting detection theorem or RH proof.'}
    if record:MANIFEST.write_text(json.dumps(result,indent=2)+'\n')
    elif json.loads(MANIFEST.read_text())!=result:raise ValueError('current revision differs from manifest')
    print(result['status'],len(result['artifacts_sha256']),'artifacts;',declarations,'declared hashes',flush=True)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');run(p.parse_args().record)
