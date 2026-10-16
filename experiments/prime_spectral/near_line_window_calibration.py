"""Common-degree window trials for the explicitly defined conductor-13 mixture."""
from fractions import Fraction
import json
import math
from pathlib import Path
import time
from flint import arb,ctx
import control_window_calibration as calibration
from dh_weil_certificate import negative_ldl_witness
from near_line_mixture_control import OUT,MixtureControl
from replay_control_atlases import replay
from full_ground_fourier import sha256

DEFINITION=OUT/'near_line_mixture_definition.json'
FOLDER=OUT/'mixture13_windows'


def matrices(control,C,modes,terms):
    # The closed generator consumes only the real periodic coefficient vector
    # returned by parameters()[2]. Scope the provider override to this process.
    old=calibration.CharacterControl
    try:
        calibration.CharacterControl=lambda q,label:control
        return calibration.matrices('character',13,0,C,modes,terms)
    finally:
        calibration.CharacterControl=old


def trial(control,C,modes=192,bits=2048):
    start=time.monotonic();C=str(Fraction(C))
    with ctx.workprec(bits):
        terms=max(32,math.ceil((bits*math.log(2)+20)/(2*float(arb(C).log().lower()))))
        E,O,_=matrices(control,C,modes,terms)
        sectors=[]
        for parity,A in [('even',E),('odd',O)]:
            try:
                s=negative_ldl_witness(A)
            except ArithmeticError as e:
                s={'unresolved':str(e)}
            s.update(parity=parity,dimension=len(A));sectors.append(s)
        status=('negative_full_form_trial' if any('normalized_full_form' in s for s in sectors)
                else 'positive_finite_sections_only' if all(s.get('positive_finite_section') for s in sectors)
                else 'unresolved')
        result={'status':status,'C':C,'modes':modes,'bits':bits,'t':str(control.t),
                'control':control.metadata(),'archimedean_tail_terms':terms,'sectors':sectors,
                'seconds':time.monotonic()-start,
                'input_sha256':{str(DEFINITION):sha256(DEFINITION)},
                'source_sha256':{n:sha256(Path(__file__).with_name(n)) for n in
                                 ['near_line_window_calibration.py','near_line_mixture_control.py',
                                  'control_window_calibration.py','dh_weil_certificate.py']},
                'scope':'Exact rational negative witness or positive finite evidence only; no minimum-support bracket.'}
    FOLDER.mkdir(parents=True,exist_ok=True)
    path=FOLDER/f'C{C.replace("/","_")}_N{modes}_{bits}bits.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(C,status,'seconds',result['seconds'],flush=True)
    return result,path


def run():
    definition=json.loads(DEFINITION.read_text());control=MixtureControl(definition['t'])
    atlas=OUT/'mixture13_H160/atlas.json';d=json.loads(atlas.read_text())
    if d['status']!='complete_certified_control_zero_atlas' or d['right_off_line_count']!=5:
        raise ArithmeticError('complete mixture atlas required')
    r=replay(OUT/'mixture13_H160',control)
    r['source_sha256']={n:sha256(Path(__file__).with_name(n)) for n in
                        ['near_line_window_calibration.py','near_line_mixture_control.py',
                         'replay_control_atlases.py','character_zero_atlas.py']}
    (OUT/'mixture_atlas_replay.json').write_text(json.dumps(r,indent=2)+'\n')
    records=[]
    def evaluate(C):
        result,path=trial(control,C)
        records.append({'file':str(path),'C':str(C),'status':result['status'],'sha256':sha256(path)})
        return result['status']
    low,high=Fraction(16),Fraction(32)
    if evaluate(low)!='positive_finite_sections_only':
        raise ArithmeticError('initial positive finite endpoint failed')
    while evaluate(high)=='positive_finite_sections_only':
        low,high=high,2*high
        if high>512:
            raise ArithmeticError('bounded window search exhausted')
    if records[-1]['status']!='negative_full_form_trial':
        raise ArithmeticError('negative endpoint unresolved')
    for _ in range(9):
        mid=(low+high)/2;status=evaluate(mid)
        if status=='negative_full_form_trial':high=mid
        elif status=='positive_finite_sections_only':low=mid
        else:raise ArithmeticError('finite search unresolved')
    summary={'status':'finite_family_search_with_certified_negative_endpoint',
             'positive_finite_evidence_C':str(low),'negative_certificate_C':str(high),
             'records':records,'modes':192,'bits':2048,
             'input_sha256':{str(atlas):sha256(atlas),str(DEFINITION):sha256(DEFINITION),
                             str(OUT/'near_line_forecast.json'):sha256(OUT/'near_line_forecast.json')},
             'scope':'Positive finite sections do not bound the first full negative support from below.'}
    (FOLDER/'search_N192_2048bits.json').write_text(json.dumps(summary,indent=2)+'\n')


if __name__=='__main__':
    run()
