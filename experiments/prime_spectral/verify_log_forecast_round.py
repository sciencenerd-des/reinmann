"""Bind the new forecast experiment and retain historical science unchanged."""
import argparse,datetime,hashlib,json
from pathlib import Path
from fractions import Fraction
from plain_l13_decay import OUT
ROOT=Path(__file__).resolve().parents[2]
MANIFEST=ROOT/OUT/'manifest.json'
PREVIOUS=ROOT/'research/prime_spectral/verification_2026_10_16_figures/manifest.json'
MUTABLE={'paper/HUMAN_REVIEW_REQUEST.md','paper/DH_CONTROLS_READINESS.md'}


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def run(record=False):
    previous=json.loads(PREVIOUS.read_text());bound={};seen=set();declarations=0
    for name,digest in previous['artifacts_sha256'].items():
        p=ROOT/name
        if name not in MUTABLE and sha(p)!=digest:raise ValueError('previous artifact changed: '+name)
        bound[p]=sha(p)
    def inspect(p):
        nonlocal declarations
        if p in seen:return
        seen.add(p)
        if p.suffix!='.json' or p.name=='manifest.json':return
        def visit(node):
            nonlocal declarations
            if isinstance(node,list):
                for item in node:visit(item)
            elif isinstance(node,dict):
                for key in ['input_sha256','source_sha256']:
                    for name,digest in node.get(key,{}).items():
                        target=Path(name)
                        if not target.is_absolute():target=(ROOT/'experiments/prime_spectral' if key=='source_sha256' else ROOT)/target
                        target=target.resolve()
                        if not target.is_relative_to(ROOT) or sha(target)!=digest:raise ValueError('declared hash mismatch: '+name)
                        bound[target]=digest;declarations+=1
                        # Follow only current experiment records; prior scientific closures are immutable.
                        if target.is_relative_to(ROOT/OUT):inspect(target)
                if 'file' in node and 'sha256' in node:
                    target=Path(node['file'])
                    if not target.is_absolute():target=ROOT/target
                    target=target.resolve()
                    if not target.is_relative_to(ROOT) or sha(target)!=node['sha256']:raise ValueError('recorded artifact hash mismatch')
                    bound[target]=node['sha256'];declarations+=1
                for item in node.values():visit(item)
        visit(json.loads(p.read_text()))
    for p in (ROOT/OUT).rglob('*'):
        if p.is_file() and p.name!='manifest.json':bound[p]=sha(p);inspect(p)
    forecast=json.loads((ROOT/OUT/'preregistered_forecast.json').read_text())
    if sha(ROOT/OUT/'preregistered_forecast.json')!='bc07008f9b5777ec6c6577f974e649ad00170e4d8956eaf888c22dfd5f70e62a':raise ValueError('frozen forecast changed')
    when=lambda s:datetime.datetime.fromisoformat(s)
    for key in ['b002','b001']:
        folder=ROOT/OUT/key;definition=json.loads((folder/'definition.json').read_text());atlas=json.loads((folder/'atlas_H160/atlas.json').read_text());replay=json.loads((folder/'atlas_replay.json').read_text());summary=json.loads((folder/'window_search.json').read_text())
        assert when(forecast['recorded_utc'])<when(definition['recorded_utc'])
        assert atlas['remaining_count']==0 and atlas['global_count']==123
        assert replay['status']=='all_contours_and_root_gates_replayed'
        assert summary['status']=='held_out_N192_support_endpoint_certified'
        assert Fraction(summary['negative_certificate_C'])-Fraction(summary['positive_finite_evidence_C'])<=Fraction(1,32)
    fresh=json.loads((ROOT/OUT/'fresh_witness_replay.json').read_text())
    assert fresh['status']=='both_held_out_exact_witnesses_reassembled_at_higher_precision'
    assert 'PASS even-gamma single-L entries' in (ROOT/OUT/'normalization_tests.log').read_text()
    for p in (ROOT/'experiments/prime_spectral').glob('*.py'):bound[p]=sha(p)
    for name in ['README.md','paper/HUMAN_REVIEW_REQUEST.md','paper/DH_CONTROLS_READINESS.md','paper/rh_same_height_fiber_framework.tex','paper/rh_same_height_fiber_framework.pdf','paper/rh_same_height_fiber_framework.html','research/COMPONENTWISE_CRITICAL_EXCLUSION_PROOF.md','research/STRATEGIC_SCOPE_CORRECTION_2026_10_17.md','research/prime_spectral/LOG_FORECAST_PROTOCOL_2026_10_17.md','research/prime_spectral/LOG_FORECAST_RESULTS_2026_10_17.md','paper/dh_log_forecast_note.md','paper/figures/dh_log_forecast.pdf','paper/figures/dh_log_forecast.png']:
        p=ROOT/name;bound[p]=sha(p)
    bound[PREVIOUS]=sha(PREVIOUS)
    result={'status':'held_out_log_forecast_round_verified','previous_science_unchanged_except_declared_review_status_docs':True,'forecast_fixed_before_target_selection':True,'complete_replayed_new_atlases':2,'exact_negative_witnesses_replayed':2,'normalization_tests_passed':2,'hash_declarations_checked':declarations,'artifacts_sha256':{str(p.relative_to(ROOT)):digest for p,digest in sorted(bound.items())},'scope':'Finite calibration, frozen local forecasts and editorial scope correction. No global minimum-support bounds, universal law, new Lean result or publication. Private correspondence receipts are kept outside this public scientific closure.'}
    if record:MANIFEST.write_text(json.dumps(result,indent=2)+'\n')
    elif json.loads(MANIFEST.read_text())!=result:raise ValueError('round differs from current manifest')
    print(result['status'],len(bound),'artifacts;',declarations,'declared hashes',flush=True)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');run(p.parse_args().record)
