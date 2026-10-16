"""Rigorous ordinary-coefficient tail via DH's positive Taylor coefficients.

If F(z)=sum mu_n z^n and mu_n>=0 (the positive-theta lemma in the
manuscript), mu_n<=F(R)/R^n for every positive real R. No fitted tail.
"""
import json
from pathlib import Path
from flint import acb,arb,ctx
from character_zero_atlas import CharacterControl
from certified_weil import endpoints
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT=Path('research/prime_spectral/verification_2026_10_15_second_band')


def run():
    path=Path('research/prime_spectral/verification_2026_10_15_split_pair/dh_coefficients_1450_32768bits.json')
    data=json.loads(path.read_text())
    with ctx.workprec(32768):
        mu=[box(x) for x in data['coefficients']];mu[0]=arb(1)
        c=CharacterControl(5,2);R=arb(2)**20
        numerator=c.completed(acb(arb('1/2')+R.sqrt()));denominator=c.completed(acb('1/2'))
        if not numerator.imag.contains(0) or not denominator.imag.contains(0) or not numerator.real>0 or not denominator.real>0:
            raise ArithmeticError('positive real completed value unresolved')
        bound=numerator.real/denominator.real
        for n in range(len(mu),2051):
            upper=(bound/R**n).upper();mu.append(arb(upper/2,upper/2))
        result={'status':'ordinary_coefficients_extended_by_positive_Cauchy_bound','bits':32768,'count':2050,
                'coefficients':[endpoints(x) for x in mu],'exact_jet_coefficients':1451,
                'tail_bound':'0 <= mu_n <= F(R)/R^n, n>=1451, from written positive-theta Taylor-coefficient lemma',
                'radius':str(2**20),'F_radius':endpoints(bound),
                'input_sha256':{str(path):sha256(path)},
                'source_sha256':{n:sha256(Path(__file__).with_name(n)) for n in ['dh_cauchy_coefficient_extension.py','character_zero_atlas.py']},
                'scope':'Enclosures through index2050; final600 are rigorous broad bounds, not new coefficient evaluations. Same FLINT backend and written positivity dependency.'}
    target=OUT/'dh_coefficients_2050_cauchy_32768bits.json';target.write_text(json.dumps(result,indent=2)+'\n')
    print('Enclosed',len(mu),'coefficients using positive-coefficient tail bounds',flush=True)


if __name__=='__main__':run()
