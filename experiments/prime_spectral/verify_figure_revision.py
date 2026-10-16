"""Current-revision provenance; prior full-paper manifests stay historical."""
from fractions import Fraction
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'research/prime_spectral/verification_2026_10_16_figures'
PREVIOUS=ROOT/'research/prime_spectral/verification_2026_10_15_second_band/manifest.json'
MANIFEST=OUT/'manifest.json'
MUTABLE={'paper/dh_controls_paper.tex','paper/dh_controls_paper.pdf','paper/DH_CONTROLS_READINESS.md',
         'paper/DH_CONTROLS_REPRODUCTION.md','paper/HUMAN_REVIEW_REQUEST.md','paper/zenodo_dh_controls.json','research/RESEARCH_STATUS_2026_10_11.md'}
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
    figures=get('figure_validation.json')
    assert figures['status']=='added_figure_caption_numbers_verified'
    assert figures['line_zero_count']==235 and figures['off_line_pair_count']==7
    assert figures['inner_line_zero_count']==43 and figures['single_folded_zero_inside_radius64']
    validation=get('paper_validation.json')
    assert validation['status']=='figure_revision_pdf_built_and_visually_inspected'
    assert validation['pages']>=17
    artifacts=set(bound)|{PREVIOUS}|set(p for p in OUT.rglob('*') if p.is_file() and p.name not in EXCLUDED)
    artifacts |= set((ROOT/'experiments/prime_spectral').glob('*.py'))
    artifacts |= {ROOT/n for n in MUTABLE}
    artifacts |= {ROOT/n for n in ['paper/HUMAN_REVIEW_REQUEST.md','paper/LIU_REPLAY_NOTE_DRAFT.md',
          'research/prime_spectral/SECOND_BAND_AND_COLLISION_PATH_2026_10_15.md',
          'research/prime_spectral/POST_PUBLICATION_FORMAL_TARGETS_2026_10_15.md']}
    artifacts |= set((ROOT/'paper/figures').glob('dh_second_band_column.*'))
    artifacts |= set((ROOT/'paper/figures').glob('dh_mixture_collision_path.*'))
    artifacts |= set((ROOT/'paper/figures').glob('dh_*_verified.*'))
    artifacts |= {ROOT/'paper/figures/dh_folded_wedge.pdf',ROOT/'paper/figures/dh_attribution_bars.pdf',ROOT/'research/prime_spectral/ADDED_FIGURES_2026_10_16.md'}
    result={'status':'added_figure_revision_verified','previous_manifest_sha256':sha(PREVIOUS),
            'json_roots_checked':len(records),'hash_declarations_checked':declarations,'new_tests_passed':0,'caption_assertions_passed':True,'prior_scientific_suite_unchanged':True,
            'second_band':[1536,1972],'nearby_cells':1620,'complete_new_atlases':3,
            'artifacts_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(artifacts)},
            'scope':'Figures and current manuscript checked against immutable prior scientific inputs. Existing eleven-test scientific/package suite is unchanged. No new numerical search or mathematical theorem. Prior full-paper manifests bind historical paper revisions. Local preregistration; human read pending; no public post or publication authorized by these checks. Finite support upper bounds, not a limiting detection theorem or RH proof.'}
    if record:MANIFEST.write_text(json.dumps(result,indent=2)+'\n')
    elif json.loads(MANIFEST.read_text())!=result:raise ValueError('current revision differs from manifest')
    print(result['status'],len(result['artifacts_sha256']),'artifacts;',declarations,'declared hashes',flush=True)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');run(p.parse_args().record)
