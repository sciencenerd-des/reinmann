"""Bounded, kernel-only timing of a weighted theta integral panel at height 14.

This is not a complete Xi jet or hard-tile certificate. It uses the isolated
LeanCert thin API produced by check_leancert_v430.py, without a project dependency.
"""
import argparse,hashlib,json,os,subprocess,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/'research/prime_spectral/hard_tile_2026_10_18/PanelBenchmark.lean'

def run(leancert_output,output):
    receipt=json.loads((leancert_output/'receipt.json').read_text())
    assert receipt['pin']=='5a59804aa7c499f81ffd5eedf2a2cc5f9e8766d1'
    output.mkdir(parents=True,exist_ok=True)
    env=os.environ.copy()
    env['LEAN_PATH']=str((leancert_output/'olean').resolve())+os.pathsep+subprocess.check_output(
        ['lake','env','printenv','LEAN_PATH'],cwd=ROOT).decode().strip()
    lean=subprocess.check_output(['lake','env','which','lean'],cwd=ROOT).decode().strip()
    baseline=output/'PanelImports.lean'
    baseline.write_text('\n'.join(line for line in SOURCE.read_text().splitlines() if line.startswith('import '))+'\n')
    times={};status='completed';code=None
    for label,source in [('imports',baseline),('panel',SOURCE)]:
        start=time.monotonic()
        try:
            with (output/(label+'.log')).open('w') as log:
                result=subprocess.run([lean,str(source.resolve())],cwd=ROOT,env=env,
                                      stdout=log,stderr=subprocess.STDOUT,timeout=300)
            times[label]=time.monotonic()-start;code=result.returncode
            if code:status=label+'_failed';break
        except subprocess.TimeoutExpired:
            times[label]=time.monotonic()-start;status=label+'_timeout_300_seconds';break
    log=(output/'panel.log').read_text() if (output/'panel.log').exists() else ''
    audited=[line for line in log.splitlines() if 'depends on axioms' in line]
    if status=='completed':
        assert len(audited)==3 and all(line.endswith('[propext, Classical.choice, Quot.sound]') for line in audited)
    result={'status':status,'exit_code':code,'timings_seconds':times,
            'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            'log_sha256':hashlib.sha256(log.encode()).hexdigest(),'axiom_audit':audited,
            'Lean_Xi_jet_certified':False,'Lean_hard_tile_certified':False,
            'Lean_hard_tile_seconds':None,'thirty_five_tile_seconds':None,
            'scope':'Actual interval-integral bounds for 17 weighted first-theta-term integrands on [1,1025/1024], both components. The Mellin/jet assembly, rest of the interval and local Xi variation are not supplied.'}
    (output/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
    if status!='completed':raise SystemExit(1)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--leancert-output',type=Path,default=ROOT/'tmp/leancert-v430-compatibility')
    p.add_argument('--output',type=Path,default=ROOT/'tmp/hard-panel-benchmark')
    a=p.parse_args();run(a.leancert_output.resolve(),a.output.resolve())
