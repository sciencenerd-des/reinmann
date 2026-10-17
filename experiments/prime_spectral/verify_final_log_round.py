"""Bind the reconciled baseline, final no-refit test, and proved uniform tail."""
import argparse,datetime,hashlib,json
from fractions import Fraction
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'research/prime_spectral/verification_2026_10_17_final_mechanism'
PREVIOUS=ROOT/'research/prime_spectral/verification_2026_10_17_log_forecast/manifest.json'
MANIFEST=OUT/'manifest.json'
RECONCILED={'README.md','paper/rh_same_height_fiber_framework.tex','paper/rh_same_height_fiber_framework.pdf','paper/rh_same_height_fiber_framework.html'}
FROZEN='d8dc2a26b3d9981b8df6dab574b9ef708ae993a03065ec697b16ba735f535616'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(record=False):
    previous=json.loads(PREVIOUS.read_text());bound={};seen=set();declarations=0
    for name,digest in previous['artifacts_sha256'].items():
        p=ROOT/name
        if name in RECONCILED:
            old=OUT/'historical_worktree_9b65a08'/name
            if sha(old)!=digest:raise ValueError('historical committed artifact mismatch: '+name)
        elif sha(p)!=digest:raise ValueError('historical scientific artifact changed: '+name)
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
                for key in ['input_sha256','source_sha256','files_sha256']:
                    for name,digest in node.get(key,{}).items():
                        target=Path(name)
                        if not target.is_absolute():
                            target=ROOT/target
                            if key=='source_sha256' and not target.exists():target=ROOT/'experiments/prime_spectral'/name
                        target=target.resolve()
                        if not target.is_relative_to(ROOT) or sha(target)!=digest:raise ValueError('declared hash mismatch: '+name)
                        bound[target]=digest;declarations+=1
                        if target.is_relative_to(OUT):inspect(target)
                if 'file' in node and 'sha256' in node:
                    target=Path(node['file']);target=(target if target.is_absolute() else ROOT/target).resolve()
                    if not target.is_relative_to(ROOT) or sha(target)!=node['sha256']:raise ValueError('recorded artifact mismatch')
                    bound[target]=node['sha256'];declarations+=1
                for item in node.values():visit(item)
        visit(json.loads(p.read_text()))
    for p in OUT.rglob('*'):
        if p.is_file() and p.name!='manifest.json':bound[p]=sha(p);inspect(p)
    fp=OUT/'preregistered_forecast.json';forecast=json.loads(fp.read_text());assert sha(fp)==FROZEN
    when=datetime.datetime.fromisoformat
    for key in ['b0005','b00025']:
        folder=OUT/key;definition=json.loads((folder/'definition.json').read_text());atlas=json.loads((folder/'atlas_H160/atlas.json').read_text());replay=json.loads((folder/'atlas_replay.json').read_text());s=json.loads((folder/'window_search.json').read_text());w=json.loads((folder/'fresh_witness_replay.json').read_text());n=json.loads((folder/'resolution_N256.json').read_text())
        assert when(forecast['recorded_utc'])<when(definition['recorded_utc'])
        assert atlas['remaining_count']==0 and atlas['global_count']==123 and replay['status']=='all_contours_and_root_gates_replayed'
        assert s['status']=='final_held_out_N192_support_endpoint_certified'
        assert Fraction(s['negative_certificate_C'])-Fraction(s['positive_finite_evidence_C'])<=Fraction(1,32)
        assert Fraction(n['negative_certificate_C'])-Fraction(n['positive_finite_evidence_C'])<=Fraction(1,64)
        assert w['status']=='final_exact_rational_witness_reassembled_at_higher_precision' and w['bits']==4352
        assert all(Fraction(c['quotient']['hi'])<0 for c in w['checked'])
    assessment=json.loads((OUT/'forecast_assessment.json').read_text());assert assessment['forecasting_closed']
    assert 'Build completed successfully (3563 jobs).' in (OUT/'lean_full_build.log').read_text()
    assert 'all 244 audited theorems' in (OUT/'lean_axiom_audit.log').read_text()
    assert 'AXIOM-CLEAN: 0 sorry, 0 custom axioms.' in (OUT/'lean_axiom_audit.log').read_text()
    for name in ['Reinmann/XiMellinRectangle.lean','Reinmann.lean','Reinmann/AxiomAudit.lean','README.md','research/RECONCILIATION_2026_10_17.md','research/prime_spectral/FINAL_LOG_MECHANISM_PROTOCOL_2026_10_17.md','research/prime_spectral/FINAL_LOG_MECHANISM_RESULTS_2026_10_17.md','research/prime_spectral/SINE_TYPE_LOG_COST_OBSTRUCTION_2026_10_17.md','research/prime_spectral/XI_LOW_RECTANGLE_STATUS_2026_10_17.md','paper/dh_final_log_mechanism_note.md','paper/figures/dh_final_log_mechanism.pdf','paper/figures/dh_final_log_mechanism.png']:
        p=ROOT/name;bound[p]=sha(p)
    for p in (ROOT/'experiments/prime_spectral').glob('*.py'):bound[p]=sha(p)
    for p in (ROOT/'Reinmann').rglob('*.lean'):bound[p]=sha(p)
    for name in ['lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify_axiom_clean.sh']:
        p=ROOT/name;bound[p]=sha(p)
    bound[PREVIOUS]=sha(PREVIOUS)
    result={'status':'reconciled_final_mechanism_round_verified','baseline_worktree_commit':'9b65a08','merge_commit':'701ea85','historical_scientific_artifacts_unchanged':True,'declared_reconciled_documents':sorted(RECONCILED),'forecast_fixed_before_target_selection':True,'complete_replayed_new_atlases':2,'exact_negative_witnesses_replayed':2,'forecasting_closed':True,'uniform_actual_Xi_tail_full_build_and_audit_passed':True,'hash_declarations_checked':declarations,'artifacts_sha256':{str(p.relative_to(ROOT)):h for p,h in sorted(bound.items())},'scope':'Finite calibration, explicit model obstruction and a Lean integral-tail bound. No full support lower bound, universal log law, zero-free rectangle, RH proof or publication. Historical manuscript revisions are preserved in 9b65a08; the four declared reconciliations are bound as current documents.'}
    if record:
        if MANIFEST.exists():raise FileExistsError('manifest exists; inspect changes instead of overwriting')
        MANIFEST.write_text(json.dumps(result,indent=2)+'\n')
    elif json.loads(MANIFEST.read_text())!=result:raise ValueError('round differs from current manifest')
    print(result['status'],len(bound),'artifacts;',declarations,'declared hashes')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');run(p.parse_args().record)
