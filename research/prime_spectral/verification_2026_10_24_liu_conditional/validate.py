from pathlib import Path
import hashlib,json,subprocess,sys
root=Path('research/prime_spectral/verification_2026_10_24_liu_conditional')
commands=[('unit_tests',[sys.executable,'-m','unittest','discover','-s','experiments/prime_spectral','-p','test_liu*.py','-v']),('DH_gate',[sys.executable,'experiments/prime_spectral/check_dh_research_gate.py']),('retained_DH_arithmetic_replay',[sys.executable,'-c',"import sys,json; from pathlib import Path; sys.path.insert(0,'experiments/prime_spectral'); from verify_row_density_extraction import calculate; assert calculate()==json.loads(Path('research/prime_spectral/verification_2026_10_22_row_density/exact_checks.json').read_text()); print('Retained exact DH arithmetic receipt agrees; no new row-density analysis')"]),('diff_check',['git','diff','--check'])]
records=[]
for name,argv in commands:
    result=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    p=root/(name+'.log')
    if p.exists(): raise FileExistsError(p)
    p.write_text(result.stdout)
    records.append(dict(name=name,argv=argv,exit_code=result.returncode,log=p.name,log_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
    print(name,result.returncode,flush=True)
    if result.returncode: print(result.stdout,flush=True)
phase1=Path('research/prime_spectral/verification_2026_10_24_liu_exponents/manifest.json')
old=json.loads(phase1.read_text())
changed=[]
for name,digest in old['artifacts_sha256'].items():
    p=Path(name)
    if hashlib.sha256(p.read_bytes()).hexdigest()!=digest:
        snapshot=root/('before_'+p.name)
        assert snapshot.exists() and hashlib.sha256(snapshot.read_bytes()).hexdigest()==digest,(name,'prior bytes not captured')
        changed.append(dict(path=name,phase1_sha256=digest,preserved_snapshot=str(snapshot)))
validation=dict(python=sys.version.split()[0],base_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),dirty_checkout=True,commands=records,prior_phase1_artifact_updates=changed,prior_manifests_preserved={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [phase1,Path('research/prime_spectral/verification_2026_10_24_dh_spectral/manifest.json')]},external_Lean_rebuilt=False,analytic_moment_proved=False,historical_full_round_verifier_rerun=False)
(root/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
assert all(r['exit_code']==0 for r in records)
print('Prior phase-1 bytes retained for',len(changed),'updated notes/registers')
