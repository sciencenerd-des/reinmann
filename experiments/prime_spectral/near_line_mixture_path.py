"""Three exact mixtures, complete atlases, and common-resolution window searches."""
import argparse
import datetime
from fractions import Fraction
import json
from pathlib import Path
import math
from flint import acb,arb,ctx
from near_line_mixture_control import MixtureControl
from character_zero_atlas import CharacterControl,run_control,center
from near_line_window_calibration import matrices
from dh_weil_certificate import negative_ldl_witness
from replay_control_atlases import replay
from certified_weil import endpoints
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT=Path('research/prime_spectral/verification_2026_10_15_second_band')
OLD=Path('research/prime_spectral/verification_2026_10_15_split_pair')
TARGETS={'b015':'3/200','b008':'1/125','b004':'1/250'}
SOURCES=['near_line_mixture_path.py','near_line_mixture_control.py','near_line_window_calibration.py',
         'character_zero_atlas.py','replay_control_atlases.py','control_window_calibration.py','dh_weil_certificate.py']


def sources():return {n:sha256(Path(__file__).with_name(n)) for n in SOURCES}

def select(key):
    folder=OUT/key;folder.mkdir(exist_ok=True)
    with ctx.workprec(384):
        a,b=CharacterControl(13,2),CharacterControl(13,6);gamma=arb('31.4336');offset=arb(TARGETS[key])
        for _ in range(16):
            s=acb(arb('1/2')+offset,gamma);u,v=a.jet(s,1),b.jet(s,1)
            t=-u[0]/(v[0]-u[0]);derivative=acb(0,1)*(-u[1]*(v[0]-u[0])+u[0]*(v[1]-u[1]))/(v[0]-u[0])**2
            if derivative.imag.contains(0):raise ArithmeticError('selector singular')
            gamma=(gamma-t.imag/derivative.imag).mid()
        rational=Fraction(t.real.mid().str(50,radius=False));control=MixtureControl(rational)
        disk=control.disk(acb(arb('1/2')+offset,gamma),radius='1e-80')
        actual=box(disk['real'])-arb('1/2')
        if not abs(actual-offset)<arb('1e-35'):raise ArithmeticError('target not achieved')
        definition={'status':'exact_mixture_selected_before_own_window_trials','recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    'key':key,'t':str(rational),'target_offset':TARGETS[key],'selected_zero':disk,**control.metadata(),
                    'source_sha256':sources(),'input_sha256':{str(OUT/'preregistered_forecast.json'):sha256(OUT/'preregistered_forecast.json')},
                    'scope':'One selected disk; lowest-offline claim requires complete atlas.'}
    (folder/'definition.json').write_text(json.dumps(definition,indent=2)+'\n');print(key,'parameter fixed',rational,'gamma',gamma.str(16),flush=True)
    return definition


def atlas(key):
    folder=OUT/key;definition=json.loads((folder/'definition.json').read_text());control=MixtureControl(definition['t']);target=folder/'atlas_H160';target.mkdir(exist_ok=True)
    old=json.loads((OLD/'mixture13_H160/atlas.json').read_text());roots=[definition['selected_zero']]
    for disk in old['right_off_line_zeros'][1:]:roots.append(control.disk(center(disk),radius='1e-80'))
    roots.sort(key=lambda r:float(box(r['imag']).mid()))
    (target/'offline_disks.json').write_text(json.dumps({'status':'individual_disks_only','roots':roots,**control.metadata()},indent=2)+'\n')
    for action in ['line','winding','assemble']:run_control(control,160,target,action)
    p=target/'atlas.json';d=json.loads(p.read_text())
    for n in ['kappa','root_number_real','root_number_imag']:d.pop(n,None)
    d['input_sha256'][str(folder/'definition.json')]=sha256(folder/'definition.json');d['source_sha256'].update(sources())
    lowest=d['lowest_right_off_line_zero']
    with ctx.workprec(640):
        if not abs(center(lowest)-center(definition['selected_zero']))<arb('1e-40'):raise ArithmeticError('selected pair is not lowest')
        offset=box(lowest['real'])-arb('1/2');radius=arb(lowest['radius'])
        if not radius<offset/1000000:raise ArithmeticError('root resolution too coarse for collision')
        d['off_line_pair_separation_lower']=endpoints(2*(offset-radius))
        d['disk_radius_to_offset_upper']=str((radius/offset).upper())
    p.write_text(json.dumps(d,indent=2)+'\n');r=replay(target,control);r['source_sha256']=sources()
    (folder/'atlas_replay.json').write_text(json.dumps(r,indent=2)+'\n')


def trial(key,C,modes=192,bits=4096):
    folder=OUT/key;definition=folder/'definition.json';d=json.loads(definition.read_text());control=MixtureControl(d['t']);C=str(Fraction(C))
    target=folder/'windows';target.mkdir(exist_ok=True);p=target/f'C{C.replace("/","_")}_N{modes}_{bits}bits.json'
    if p.exists():return json.loads(p.read_text()),p
    with ctx.workprec(bits):
        S=arb(C).log();terms=max(32,math.ceil((bits*math.log(2)+20)/(2*float(S.lower()))))
        E,O,_=matrices(control,C,modes,terms);sectors=[]
        for parity,A in [('even',E),('odd',O)]:
            try:r=negative_ldl_witness(A)
            except ArithmeticError as e:r={'unresolved':str(e)}
            r.update(parity=parity,dimension=len(A));sectors.append(r)
        status='negative_full_form_trial' if any('normalized_full_form' in s for s in sectors) else 'positive_finite_sections_only' if all(s.get('positive_finite_section') for s in sectors) else 'unresolved'
        result={'status':status,'C':C,'modes':modes,'bits':bits,'archimedean_tail_terms':terms,'sectors':sectors,'key':key,'t':d['t'],
                'input_sha256':{str(definition):sha256(definition)},'source_sha256':sources(),
                'scope':'Exact rational negative witness or finite positive evidence; no full support lower bound.'}
    p.write_text(json.dumps(result,indent=2)+'\n');print(key,C,'N',modes,status,flush=True);return result,p


def search(key):
    folder=OUT/key;atlas_path=folder/'atlas_H160/atlas.json';a=json.loads(atlas_path.read_text());r=json.loads((folder/'atlas_replay.json').read_text())
    if a['remaining_count']!=0 or r['status']!='all_contours_and_root_gates_replayed':raise ValueError('complete replayed atlas required')
    low,high=Fraction(32),Fraction(48);records=[]
    def evaluate(C):
        result,p=trial(key,C);records.append({'file':str(p),'sha256':sha256(p),'C':str(C),'status':result['status']});return result['status']
    if evaluate(low)!='positive_finite_sections_only':raise ArithmeticError('initial finite endpoint is not positive')
    while evaluate(high)=='positive_finite_sections_only':
        low,high=high,high*Fraction(3,2)
        if high>512:raise ArithmeticError('bounded support search exhausted')
    if records[-1]['status']!='negative_full_form_trial':raise ArithmeticError('negative endpoint unresolved')
    for _ in range(9):
        mid=(low+high)/2;status=evaluate(mid)
        if status=='negative_full_form_trial':high=mid
        elif status=='positive_finite_sections_only':low=mid
        else:raise ArithmeticError('unresolved trial')
    with ctx.workprec(512):
        z=a['lowest_right_off_line_zero'];gamma=box(z['imag']);b=box(z['real'])-arb('1/2')
        resolution=2*arb.pi()*arb(str(high))/(13*gamma)
        summary={'status':'common_N192_path_endpoint_certified','key':key,'positive_finite_evidence_C':str(low),'negative_certificate_C':str(high),
                 'modes':192,'bits':4096,'lowest_offset':endpoints(b),'gamma':endpoints(gamma),'r':endpoints(resolution),'records':records,
                 'input_sha256':{str(atlas_path):sha256(atlas_path),str(folder/'atlas_replay.json'):sha256(folder/'atlas_replay.json')},
                 'scope':'Common finite-family support upper bounds along one collision path; neither minimum-support law nor universal b-to-zero theorem.'}
    (folder/'window_search.json').write_text(json.dumps(summary,indent=2)+'\n')
    # Test the common endpoints at a larger retained degree, recording both signs honestly.
    trial(key,low,modes=256);trial(key,high,modes=256)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--key',choices=TARGETS,required=True)
    p.add_argument('--action',choices=['select','atlas','windows','all'],default='all');a=p.parse_args()
    if a.action in ['select','all']:select(a.key)
    if a.action in ['atlas','all']:atlas(a.key)
    if a.action in ['windows','all']:search(a.key)
