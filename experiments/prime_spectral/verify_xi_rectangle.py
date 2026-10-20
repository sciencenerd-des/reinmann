"""Fail-closed evidence closure for the optional actual-Xi rectangle certificate."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'research/prime_spectral/verification_2026_10_19_rectangle'
BASE=ROOT/'research/prime_spectral/verification_2026_10_19_hard_tile/manifest.json'
PIN='736e1dc4a78cb570f75ba902f8fa2e832fcfe3b8'
REFRESHED=('Reinmann.lean','Reinmann/AxiomAudit.lean','lakefile.toml','README.md')
SHARED=('RegularizedEulerMaclaurin','UniformXiRemainders','RectangleTaylor',
        'RectangleTileRules','RationalBallCover','RectangleFiniteFormulas',
        'RectangleLogInputs','RectangleModel')
ALLOWED={'propext','Classical.choice','Quot.sound'}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def strip_comments(source):
    result=[];depth=0;i=0
    while i<len(source):
        if source[i:i+2]=='/-':depth+=1;i+=2
        elif depth and source[i:i+2]=='-/':depth-=1;i+=2
        elif depth:i+=1
        elif source[i:i+2]=='--':
            j=source.find('\n',i);i=len(source) if j<0 else j
        else:result.append(source[i]);i+=1
    assert depth==0,'Unterminated comment'
    return ''.join(result)


def audit(log,expected):
    raw=log.read_text();assert 'error:' not in raw,log
    flat=re.sub(r'\n\s+',' ',raw)
    found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",flat)
    empty=re.findall(r"'([^']+)' does not depend on any axioms",flat)
    assert [n for n,_ in found]+empty==expected,(log,len(found),len(expected))
    assert all(set(map(str.strip,a.split(',')))<=ALLOWED for _,a in found),log


def declarations():
    result=[]
    for m in SHARED:
        text=(ROOT/'Reinmann'/f'{m}.lean').read_text()
        result += ['Reinmann.'+m+'.'+n for n in re.findall(r'^\s*(?:@\[[^\]]*\]\s*)*(?:protected\s+)?(?:theorem|lemma)\s+(\w+)',text,re.M)]
    result += ['Reinmann.XiRectangle.Data.centre_mem_quarter','Reinmann.XiRectangle.Cover.quarter_covered']
    for p in sorted((ROOT/'XiRectangle').glob('Tile*.lean')):
        text=p.read_text()
        ns=re.search(r'^namespace (\S+)',text,re.M).group(1)
        result += [ns+'.'+n for n in re.findall(r'^\s*(?:@\[[^\]]*\]\s*)*(?:protected\s+)?(?:theorem|lemma)\s+(\w+)',text,re.M)]
    text=(ROOT/'XiRectangle/Final.lean').read_text()
    result += ['Reinmann.XiRectangle.'+n for n in re.findall(r'^\s*(?:@\[[^\]]*\]\s*)*(?:protected\s+)?(?:theorem|lemma)\s+(\w+)',text,re.M)]
    return result


def audit_source():
    names=declarations()
    return 'import XiRectangle\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n'


def check(record=False):
    bound={}
    previous=json.loads(BASE.read_text());assert len(previous['artifacts_sha256'])==1279
    for n,h in previous['artifacts_sha256'].items():
        path=OUT/'historical_736e1dc'/n if n in REFRESHED else ROOT/n
        assert sha(path)==h,('Historical binding mismatch',n)
        bound[path]=h
    for n in REFRESHED:
        p=OUT/'historical_736e1dc'/n
        assert hashlib.sha256(subprocess.check_output(['git','show',PIN+':'+n],cwd=ROOT)).hexdigest()==sha(p)
    modules=[ROOT/'Reinmann'/f'{m}.lean' for m in SHARED]+list((ROOT/'XiRectangle').glob('*.lean'))+[ROOT/'XiRectangle.lean']
    for p in modules:
        code=strip_comments(p.read_text())
        assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom)\b',code),p
        bound[p]=sha(p)
    assert not any(re.search(r'^import Reinmann$',p.read_text(),re.M) for p in (ROOT/'Reinmann').glob('*.lean'))
    assert (OUT/'AllNewAxioms.lean').read_text()==audit_source()
    audit(OUT/'all_new_axioms.log',declarations())
    plan=json.loads((OUT/'cover_plan.json').read_text())
    assert plan['M']==1000 and plan['tile_count']==44 and plan['degree']==12
    assert plan['quarter']==['1/2','1','0','141/10']
    assert plan['source_sha256']==sha(ROOT/'experiments/prime_spectral/xi_lean_constant_cover.py')
    for name in ('main_build.log','rectangle_build.log'):
        text=(OUT/name).read_text()
        assert 'error:' not in text and re.search(r'Build completed successfully|All targets up-to-date',text),name
    guard=(OUT/'axiom_guard.log').read_text()
    assert 'AXIOM-CLEAN:' in guard and 'FAIL:' not in guard
    timing=json.loads((OUT/'parallel/timings.json').read_text())
    assert timing['status']=='complete' and all(x['returncode']==0 for x in timing['rows'])
    expected_tiles={str(p.relative_to(ROOT)) for p in (ROOT/'XiRectangle').glob('Tile[0-9][0-9][0-9].lean')}
    assert len(expected_tiles)==44 and set(timing['tiles_source_sha256'])==expected_tiles
    assert timing['rows'][-1]['targets']==['XiRectangle'],'Full assembly was not the final successful batch'
    for n,h in timing['tiles_source_sha256'].items():assert sha(ROOT/n)==h,n
    subprocess.run(['python3','experiments/prime_spectral/generate_rectangle_certificates.py','--shared','--tiles','all','--check'],cwd=ROOT,check=True)
    for p in [BASE,ROOT/'README.md',ROOT/'lakefile.toml',ROOT/'.github/workflows/ci.yml',ROOT/'Reinmann.lean',ROOT/'Reinmann/AxiomAudit.lean',ROOT/'research/prime_spectral/XI_RECTANGLE_2026_10_20.md']:
        bound[p]=sha(p)
    for n in ('rectangle_model','xi_lean_constant_cover','generate_rectangle_certificates','build_xi_rectangle','verify_xi_rectangle'):
        p=ROOT/'experiments/prime_spectral'/f'{n}.py';bound[p]=sha(p)
    for p in OUT.rglob('*'):
        if p.is_file() and p.name!='manifest.json':bound[p]=sha(p)
    result={'status':'actual_Xi_closed_rectangle_verified','base_commit':PIN,
            'closed_rectangle':{'real':['0','1'],'imag':['-141/10','141/10']},
            'tiles':44,'degree':12,'certified_function':'Reinmann.xiCompleted',
            'zero_free_rectangle_certified':True,'ZetaNoLowStripZero_141_div_10_discharged':True,
            'RH_proved':False,'KatkovaSectorBridge_discharged':False,
            'new_public_declarations':declarations(),'standard_axioms_only':True,
            'artifacts_sha256':{str(p.relative_to(ROOT)):h for p,h in sorted(bound.items())}}
    target=OUT/'manifest.json'
    if record:
        if target.exists():raise FileExistsError('Immutable manifest already exists')
        target.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(target.read_text())==result,'Manifest mismatch'
    print(result['status'],len(bound),'checksum bindings;',len(declarations()),'audited declarations')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--write-audit-source',action='store_true')
    p.add_argument('--record',action='store_true')
    p.add_argument('--live-audit',action='store_true')
    a=p.parse_args()
    if a.write_audit_source:(OUT/'AllNewAxioms.lean').write_text(audit_source())
    elif a.live_audit:
        paths=[ROOT/'Reinmann'/f'{m}.lean' for m in SHARED]+list((ROOT/'XiRectangle').glob('*.lean'))+[ROOT/'XiRectangle.lean']
        for path in paths:
            assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom)\b',strip_comments(path.read_text())),path
        temp_root=ROOT/'tmp';temp_root.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=temp_root,prefix='rectangle_audit_') as tmp:
            source=Path(tmp)/'Audit.lean';source.write_text(audit_source())
            output=Path(tmp)/'audit.log'
            with output.open('w') as stream:
                subprocess.run(['lake','env','lean',str(source)],cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT,check=True)
            audit(output,declarations())
        print('AXIOM-CLEAN:',len(declarations()),'rectangle declarations; no placeholders or native evaluation')
    else:check(a.record)
