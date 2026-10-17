"""Bind the finite-product Lean proof and retain the prior scientific closure."""
import argparse, hashlib, json, re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'research/prime_spectral/verification_2026_10_17_formal_A'
PREVIOUS=ROOT/'research/prime_spectral/verification_2026_10_17_final_mechanism/manifest.json'
MANIFEST=OUT/'manifest.json'
MUTABLE={'README.md','Reinmann.lean','Reinmann/AxiomAudit.lean'}
MODULES=['SplitPairCoefficients','SplitPairDeterminant','SplitPairModulusOrder','SplitPairOscillation','FiniteProductSplitPair','FiniteProductSplitPairControl']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(record=False):
    previous=json.loads(PREVIOUS.read_text());bound={}
    for name,h in previous['artifacts_sha256'].items():
        p=ROOT/name
        if name in MUTABLE:
            if sha(OUT/'historical_4989621'/name)!=h:raise ValueError('historical baseline mismatch: '+name)
        elif sha(p)!=h:raise ValueError('prior scientific artifact changed: '+name)
        bound[p]=sha(p)
    audit=(ROOT/'Reinmann/AxiomAudit.lean').read_text();names=[]
    for module in MODULES:
        p=ROOT/'Reinmann'/f'{module}.lean';source=p.read_text()
        ns=re.search(r'^namespace (\S+)',source,re.M).group(1)
        for name in re.findall(r'^theorem (\w+)',source,re.M):
            full=ns+'.'+name;names.append(full)
            if '#print axioms '+full not in audit:raise ValueError('theorem not audited: '+full)
        bound[p]=sha(p)
    assert len(names)==41
    assert 'Build completed successfully (2163 jobs).' in (OUT/'targeted_build.log').read_text()
    for name in ['targeted_build.log','direct_capstone.log','direct_controls.log','full_build.log','axiom_audit.log']:
        text=(OUT/name).read_text()
        if 'error:' in text or 'build failed' in text:raise ValueError('failed final validation: '+name)
    assert 'Build completed successfully' in (OUT/'full_build.log').read_text()
    assert 'all 285 audited theorems' in (OUT/'axiom_audit.log').read_text()
    assert 'OK: no sorry/admit in Reinmann/*.lean' in (OUT/'axiom_audit.log').read_text()
    assert 'AXIOM-CLEAN: 0 sorry, 0 custom axioms.' in (OUT/'axiom_audit.log').read_text()
    for p in OUT.rglob('*'):
        if p.is_file() and p.name!='manifest.json':bound[p]=sha(p)
    for name in ['research/prime_spectral/FORMAL_TARGET_A_2026_10_17.md','experiments/prime_spectral/verify_formal_A_round.py']:
        p=ROOT/name;bound[p]=sha(p)
    bound[PREVIOUS]=sha(PREVIOUS)
    result={'status':'finite_product_split_pair_formal_round_verified','baseline_commit':'4989621','new_proved_theorems':41,'total_audited_theorems':285,'sorry':0,'custom_axioms':0,'declared_updated_files':sorted(MUTABLE),'prior_scientific_artifacts_unchanged':True,'main_theorem':'Reinmann.FiniteProductSplitPair.finite_product_split_pair_of_root_order','exponential_bound':'Reinmann.FiniteProductSplitPair.exponential_remainder_bound','concrete_controls':['quadratic_control_both_signs','cubic_control_both_signs'],'artifacts_sha256':{str(p.relative_to(ROOT)):h for p,h in sorted(bound.items())},'scope':'Actual finite-product reciprocal complementary minors, nonzero Vandermonde coefficients, proved root ordering, geometric remainder and unbounded signs. No assumed two-term asymptotic. No entire-function Cauchy remainder, original-coefficient Jacobi bridge, numerical DH atlas formalization, RH proof or publication.'}
    if record:
        if MANIFEST.exists():raise FileExistsError('manifest exists; inspect changes rather than overwrite')
        MANIFEST.write_text(json.dumps(result,indent=2)+'\n')
    elif json.loads(MANIFEST.read_text())!=result:raise ValueError('proof round differs from manifest')
    print(result['status'],len(bound),'bound artifacts;',len(names),'new theorems')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');run(p.parse_args().record)
