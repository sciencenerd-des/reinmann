"""Bind the current paper and new certificates without rewriting old manifests.

This is a provenance/outcome verifier. Numerical replay is in the test and
atlas/column generators. Upstream Liu receipts are opaque, hash-bound inputs.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'research/prime_spectral/verification_2026_10_15_split_pair'
OLD=ROOT/'research/prime_spectral/verification_2026_10_12_sector'
CAL=ROOT/'research/prime_spectral/verification_2026_10_13_calibration'
MANIFEST=OUT/'manifest.json'


def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()


def run(record=False):
    bound={};seen=set();declarations=0
    def resolve(name,source=False):
        p=Path(name)
        if not p.is_absolute():p=(ROOT/'experiments/prime_spectral' if source else ROOT)/p
        p=p.resolve()
        if not p.is_relative_to(ROOT):raise ValueError(f'outside workspace input: {p}')
        return p
    def bind(p,digest):
        nonlocal declarations
        actual=bound.setdefault(p,sha(p))
        if actual!=digest:raise ValueError(f'hash mismatch: {p.relative_to(ROOT)}')
        declarations+=1
        inspect(p)
    def visit(node):
        if isinstance(node,list):
            for child in node:visit(child)
        elif isinstance(node,dict):
            for key in ['source_sha256','input_sha256']:
                for name,digest in node.get(key,{}).items():bind(resolve(name,key=='source_sha256'),digest)
            if 'file' in node and 'sha256' in node:bind(resolve(node['file']),node['sha256'])
            if 'coefficient_file' in node and 'coefficient_sha256' in node:
                bind(resolve(node['coefficient_file']),node['coefficient_sha256'])
            if 'compacted_mathematical_core_sha256' in node:
                core=json.dumps(node['sectors'],sort_keys=True,separators=(',',':')).encode()
                if hashlib.sha256(core).hexdigest()!=node['compacted_mathematical_core_sha256']:
                    raise ValueError('compacted core changed')
            for child in node.values():visit(child)
    def inspect(p):
        if p in seen:return
        seen.add(p)
        if p.suffix=='.json' and 'liu_fresh_receipts' not in p.parts:
            visit(json.loads(p.read_text()))
    excluded={'manifest.json','zenodo_matching_drafts.json','zenodo_draft_receipt.json','release_bundle_receipt.json'}
    roots=[p for p in OUT.rglob('*.json') if p.name not in excluded]
    roots += [CAL/'calibration_dataset.json',CAL/'atlas_replays.json',
              OLD/'atlas_H340.json',OLD/'atlas_replay.json',OLD/'high_rank_replay.json',
              OLD/'dh_rank430-520_shift0-200_32768bits.json',OLD/'lean_validation.json']
    for p in roots:inspect(p);bound.setdefault(p,sha(p))
    compaction=CAL/'storage_compaction.json'
    inspect(compaction);bound.setdefault(compaction,sha(compaction))
    c=json.loads(compaction.read_text())
    bind(CAL/'source_snapshots/control_window_calibration_initial.py',c['snapshot_sha256'])
    for event in c['events']:bind(resolve(event['file']),event['compacted_sha256'])
    old_atlas=json.loads((OLD/'atlas_replay.json').read_text())
    bind(OLD/'atlas_H340.json',old_atlas['atlas_sha256'])
    old_grid=json.loads((OLD/'high_rank_replay.json').read_text())
    bind(OLD/'dh_rank430-520_shift0-200_32768bits.json',old_grid['scan_sha256'])
    def data(name):return json.loads((OUT/name).read_text())
    initial=data('column44_rank521-677_32768bits.json')
    assert [r['rank'] for r in initial['per_rank'] if r['sign']=='negative']==list(range(664,678))
    assert all(r['sign']=='positive' for r in initial['per_rank'] if r['rank']<664)
    assert {r['rank'] for r in initial['direct_checks']} >= {520,521,663,664,677}
    asym=data('split_pair_asymptotic.json')
    assert asym['status']=='split_pair_order_and_nonvanishing_certified' and asym['inner_real_zero_count']==43
    atlas=data('mixture13_H160/atlas.json');replay=data('mixture_atlas_replay.json')
    assert atlas['global_count']==123 and atlas['remaining_count']==0
    assert replay['status']=='all_contours_and_root_gates_replayed' and replay['global_count']==123
    windows=data('mixture13_windows/search_N192_2048bits.json')
    assert windows['negative_certificate_C']=='593/16'
    for name in ['C593_16_N192_2048bits.json','C37_N256_2048bits.json','C593_16_N256_2048bits.json']:
        d=data('mixture13_windows/'+name)
        assert d['status']=='negative_full_form_trial'
        assert any(Fraction(s['normalized_full_form']['hi'])<0 for s in d['sectors'] if 'normalized_full_form' in s)
    liu=data('liu_audit.json')
    assert liu['status']=='frozen_Liu_A_retained_and_B_clean_full_fast_reproduced'
    assert liu['immutable_members_rechecked']==292
    for name in ['tests_split_pair.log','tests_near_line.log']:
        log=(OUT/name).read_text();assert 'Ran 3 tests' in log and log.rstrip().endswith('OK')
    log=(OUT/'tests_bundle.log').read_text()
    assert 'Ran 2 tests' in log and log.rstrip().endswith('OK')
    artifacts=set(bound)|set(p for p in OUT.rglob('*') if p.is_file() and p.name not in excluded)
    artifacts |= set((ROOT/'experiments/prime_spectral').glob('*.py'))
    artifacts |= {ROOT/p for p in ['paper/dh_controls_paper.tex','paper/dh_controls_paper.pdf',
        'paper/dh_controls_tables.tex','paper/dh_controls_attribution_table.tex','paper/DH_CONTROLS_READINESS.md',
        'research/prime_spectral/SPLIT_PAIR_AND_LIU_AUDIT_2026_10_15.md',
        'research/prime_spectral/LIU_FROZEN_RELEASE_AUDIT_2026_10_15.md','research/RESEARCH_STATUS_2026_10_11.md','lean-toolchain']}
    artifacts |= {p for p in [ROOT/'lakefile.toml',ROOT/'lakefile.lean',ROOT/'lake-manifest.json'] if p.is_file()}
    artifacts |= set((ROOT/'paper/figures').glob('dh_controls_calibration.*'))
    for name in ['paper/figures/dh_split_pair_column.pdf','paper/figures/dh_split_pair_column.png',
                 'paper/zenodo_dh_controls.json','paper/DH_CONTROLS_REPRODUCTION.md']:
        if (ROOT/name).is_file():artifacts.add(ROOT/name)
    result={'status':'split_pair_round_provenance_and_outcomes_verified',
        'json_roots_checked':len(roots),'hash_declarations_checked':declarations,
        'new_tests_passed':8,'scientific_tests_passed':6,'bundle_gate_tests_passed':2,'first_negative_in_shift44_column':664,
        'small_offset_conclusion':'one certified support upper bound; limiting behaviour inconclusive',
        'liu_status':liu['status'],
        'artifacts_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(artifacts)},
        'scope':'Hash and recorded outcome verification, supplementary to numerical replay. AI review, not human peer review. No globally first minor, minimum negative support, universal exchange law or RH proof.'}
    fresh=OUT/'dh_coefficients_1450_32768bits.json';extended=OUT/'column44_rank521-1400_32768bits.json'
    if fresh.is_file():
        d=json.loads(fresh.read_text());assert d['count']==1450 and d['prior_coefficients_overlapping']==721
        result['fresh_coefficients']=1451
    if extended.is_file():
        d=json.loads(extended.read_text());assert len(d['per_rank'])==880 and all(r['sign']!='unresolved' for r in d['per_rank'])
        assert {r['rank']:r['sign'] for r in initial['per_rank']}=={r['rank']:r['sign'] for r in d['per_rank'] if r['rank']<=677}
        assert d['negative_ranks']==list(range(664,1100))
        replay=data('column44_extended_replay.json')
        assert replay['status']=='extended_targeted_column_replayed' and replay['ranks_checked']==880
        assert {r['rank'] for r in replay['direct_checks']} >= {663,664,1099,1100}
        result['extended_column_negative_ranks']=d['negative_ranks']
    if record:MANIFEST.write_text(json.dumps(result,indent=2)+'\n')
    else:
        recorded=json.loads(MANIFEST.read_text())
        if recorded!=result:raise ValueError('current artifacts differ from recorded manifest')
    print(result['status'],len(result['artifacts_sha256']),'artifacts;',declarations,'hash declarations')
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--record',action='store_true')
    run(p.parse_args().record)
