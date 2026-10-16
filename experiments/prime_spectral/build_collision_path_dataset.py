"""Describe the measured mixture path without extrapolating to b=0."""
from fractions import Fraction
import json
from pathlib import Path
import numpy as np
from flint import arb,ctx
from near_line_mixture_path import OUT,OLD
from threshold_ground_gap import box
from certified_weil import endpoints
from full_ground_fourier import sha256


def run():
    rows=[];inputs={}
    def read(path):inputs[str(path)]=sha256(path);return json.loads(path.read_text())
    with ctx.workprec(512):
        a=read(OLD/'mixture13_H160/atlas.json');s=read(OLD/'mixture13_windows/search_N192_2048bits.json');z=a['lowest_right_off_line_zero'];C=Fraction(s['negative_certificate_C']);gamma=box(z['imag']);b=box(z['real'])-arb('1/2')
        p=Path(next(r['file'] for r in s['records'] if r['C']==str(C)));d=read(p);q=next(x['normalized_full_form'] for x in d['sectors'] if 'normalized_full_form' in x)
        p256=OLD/'mixture13_windows/C37_N256_2048bits.json';read(p256)
        rows.append({'key':'b030','b':endpoints(b),'gamma':endpoints(gamma),'C_N192':str(C),'C_N256':'37',
                     'r_N192':endpoints(2*arb.pi()*arb(str(C))/(13*gamma)),'quotient_N192':q,'N256_scope':'one negative trial, not newly bisected'})
        for key in ['b015','b008','b004']:
            folder=OUT/key;a=read(folder/'atlas_H160/atlas.json');read(folder/'atlas_replay.json');s=read(folder/'window_search.json');r=read(folder/'resolution_N256.json');attr=read(folder/'attribution.json')
            p=Path(next(x['file'] for x in s['records'] if x['C']==s['negative_certificate_C']));d=read(p);q=next(x['normalized_full_form'] for x in d['sectors'] if 'normalized_full_form' in x)
            rows.append({'key':key,'b':s['lowest_offset'],'gamma':s['gamma'],'C_N192':s['negative_certificate_C'],'C_N256':r['negative_certificate_C'],
                         'r_N192':s['r'],'quotient_N192':q,'N256_scope':'finite-family endpoint with positive finite evidence only',
                         'off_line_pair_separation_lower':a['off_line_pair_separation_lower'],'root_disk_radius':a['lowest_right_off_line_zero']['radius']})
        offsets=np.array([float(box(x['b']).mid()) for x in rows]);Cs=np.array([float(Fraction(x['C_N192'])) for x in rows]);rs=np.array([float(box(x['r_N192']).mid()) for x in rows])
        x=np.log(offsets[0]/offsets);X=np.column_stack([np.ones(len(x)),x]);coef=np.linalg.lstsq(X,Cs,rcond=None)[0]
        prediction=X@coef
        result={'status':'four_point_collision_path_described','rows':rows,
                'descriptive_C_log_fit':{'model':'C_N192 = a + k log(b0/b), b0=0.03','a':float(coef[0]),'k':float(coef[1]),'RMSE':float(np.sqrt(np.mean((Cs-prediction)**2))),
                                         'warning':'Four support upper bounds on one path; not an asymptotic rate or universal law.'},
                'observed_r_growth_percent':float(100*(rs[-1]/rs[0]-1)),
                'interpretation':'Measured endpoints increase as offset shrinks. Approximately logarithmic-looking growth over this finite range; neither boundedness nor divergence of the true minimum-support limit is established.',
                'input_sha256':inputs,'source_sha256':{Path(__file__).name:sha256(Path(__file__))},
                'scope':'Common retained degree192; larger-degree sensitivity separately measured. No refit of the original seven-control model, no full positive-support lower bound and no universal limit theorem.'}
    (OUT/'collision_path_dataset.json').write_text(json.dumps(result,indent=2)+'\n')
    print('collision path C values',Cs.tolist(),'r values',rs.tolist(),'descriptive log slope',coef[1],flush=True)


if __name__=='__main__':run()
