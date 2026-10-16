"""A tunable conductor-13 root-number-one control for the small-offset limit.

The mixture is explicitly distinguished from a single Conrey-label control.
Its exact rational parameter is selected before any new window trial.
"""
from fractions import Fraction
import json
from pathlib import Path
from flint import acb,arb,ctx
from character_zero_atlas import CharacterControl,run_control
from certified_weil import endpoints
from full_ground_fourier import sha256

OUT=Path('research/prime_spectral/verification_2026_10_15_split_pair')


class MixtureControl:
    q,label=13,0
    near_one_bound=CharacterControl.near_one_bound
    strip=CharacterControl.strip
    completed=CharacterControl.completed
    disk=CharacterControl.disk

    def __init__(self,t):
        self.t=Fraction(t)
        self.first,self.second=CharacterControl(13,2),CharacterControl(13,6)

    def weight(self):
        return arb(str(self.t))

    def parameters(self):
        t=self.weight()
        a,b=self.first.parameters()[2],self.second.parameters()[2]
        period=[(1-t)*x+t*y for x,y in zip(a,b)]
        period[0],period[1]=arb(0),arb(1)
        return acb(1),arb(0),period

    def value(self,s):
        t=self.weight()
        return (1-t)*self.first.value(s)+t*self.second.value(s)

    def jet(self,s,degree=2):
        t=self.weight()
        return (1-t)*self.first.jet(s,degree)+t*self.second.jet(s,degree)

    def metadata(self):
        return {'kind':'root_number_one_character_mixture','conductor':13,
                'components':[{'Conrey_label':2,'weight':str(1-self.t)},
                              {'Conrey_label':6,'weight':str(self.t)}],
                'gamma_degree':1,'normalization':'Same odd gamma and conductor 13; exact real linear combination of two root-number-one completions.'}


def select():
    with ctx.workprec(256):
        a,b=CharacterControl(13,2),CharacterControl(13,6)
        gamma=arb('31.43420501')
        for _ in range(12):
            s=acb('53/100',gamma)
            u,v=a.jet(s,1),b.jet(s,1)
            t=-u[0]/(v[0]-u[0])
            derivative=acb(0,1)*(-u[1]*(v[0]-u[0])+u[0]*(v[1]-u[1]))/(v[0]-u[0])**2
            if derivative.imag.contains(0):
                raise ArithmeticError('mixture parameter selector singular')
            gamma=(gamma-t.imag/derivative.imag).mid()
        rational=Fraction(str(t.real.mid().str(35,radius=False)))
        control=MixtureControl(rational)
        disk=control.disk(acb('53/100',gamma),radius='1e-80')
        if not arb('299/10000')<arb(str(Fraction(disk['real']['lo'])))-arb('1/2')<arb('301/10000'):
            raise ArithmeticError('selected offset not close to 0.03')
        result={'status':'exact_mixture_selected_before_window_trials',
                **control.metadata(),'t':str(rational),'target_offset':'3/100',
                'selected_zero':disk,'source_sha256':{'near_line_mixture_control.py':sha256(Path(__file__))},
                'scope':'One disk, not a lowest-zero claim; a complete atlas is required before calibration.'}
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'near_line_mixture_definition.json').write_text(json.dumps(result,indent=2)+'\n')
    print('mixture parameter',rational,'height',gamma.str(15),flush=True)
    return result


if __name__=='__main__':
    definition=select()
    control=MixtureControl(definition['t'])
    run_control(control,160,OUT/'mixture13_H160','all')
    path=OUT/'mixture13_H160/atlas.json'
    d=json.loads(path.read_text())
    for key in ['kappa','root_number_real','root_number_imag']:
        d.pop(key,None)
    d['source_sha256']['near_line_mixture_control.py']=sha256(Path(__file__))
    path.write_text(json.dumps(d,indent=2)+'\n')
