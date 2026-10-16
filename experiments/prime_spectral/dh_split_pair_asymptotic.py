"""Certify DH's split modulus ordering and nonzero leading residue constant."""
import json
from pathlib import Path
from flint import acb,arb,ctx
from character_zero_atlas import CharacterControl
from certified_weil import endpoints
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT=Path('research/prime_spectral/verification_2026_10_15_split_pair')
ATLAS=Path('research/prime_spectral/verification_2026_10_13_calibration/dh5_refined_atlas.json')


def rectangle(record):
    radius=arb(record['radius'])
    return acb(box(record['real'])+arb(0,radius),box(record['imag'])+arb(0,radius))


def run():
    data=json.loads(ATLAS.read_text())
    with ctx.workprec(640):
        control=CharacterControl(5,2)
        lam0=control.completed(acb('1/2')).real
        pair=rectangle(data['right_off_line_zeros'][0])-arb('1/2')
        pair_modulus=abs(pair)**2
        inside=[];outside=[]
        for record in data['critical_line_disks']:
            z=rectangle(record)-arb('1/2')
            if abs(z)**2 <pair_modulus:
                inside.append(z)
            elif abs(z)**2 >pair_modulus:
                outside.append(z)
            else:
                raise ArithmeticError('critical zero straddles pair modulus')
        if len(inside)!=43:
            raise ArithmeticError('shift-44 ordering failed')
        if any(not abs(rectangle(r)-arb('1/2'))**2>pair_modulus
               for r in data['right_off_line_zeros'][1:]):
            raise ArithmeticError('another off pair precedes selected pair')
        inside.sort(key=lambda z:float(z.imag.mid()))
        outside.sort(key=lambda z:float(z.imag.mid()))
        lambdas=[];residues=[]
        for z in inside+[pair]:
            s=z+arb('1/2');jet=control.jet(s,1)
            g=(s*(arb(5)/arb.pi()).log()/2).exp()*((s+1)/2).gamma()
            derivative=g*(jet[1]+jet[0]*((arb(5)/arb.pi()).log()/2+((s+1)/2).digamma()/2))
            c=-2*lam0/(z*derivative)
            if not c.is_finite() or c.contains(0):
                raise ArithmeticError('residue nonvanishing unresolved')
            lambdas.append(-1/(z*z));residues.append(c)
        shift=len(lambdas)
        constant=acb((-1)**(shift*(shift-1)//2))
        for x,c in zip(lambdas,residues):
            constant*=c/x**(shift-1)
        for j,x in enumerate(lambdas):
            for y in lambdas[:j]:
                constant*=(x-y)**2
        if not constant.is_finite() or constant.contains(0):
            raise ArithmeticError('leading constant nonvanishing unresolved')
        phi=2*((pair.real/pair.imag).atan())
        P=arb(1)
        for x in lambdas[:-1]:
            if not x.real>0 or not x.imag.contains(0):
                raise ArithmeticError('inner inverse roots not positive real')
            P*=x.real
        predictions=[]
        for r in range(430,1401):
            value=(constant.arg()+r*phi).cos()
            predictions.append({'rank':r,'leading_cosine':value.str(20),
                                'sign':'positive' if value>0 else 'negative' if value<0 else 'unresolved'})
        result={'status':'split_pair_order_and_nonvanishing_certified','shift':44,
                'inner_real_zero_count':43,'folded_pair_modulus':endpoints(pair_modulus),
                'effective_height':endpoints(pair_modulus.sqrt()),'angle':endpoints(phi),
                'rank_period_scale':endpoints(2*arb.pi()/phi),
                'inner_modulus_gap_ratio':endpoints(pair_modulus/abs(inside[-1])**2),
                'outer_modulus_gap_ratio':endpoints(abs(outside[0])**2/pair_modulus),
                'leading_constant_real':constant.real.str(50),
                'leading_constant_imag':constant.imag.str(50),
                'leading_constant_absolute':abs(constant).str(50),
                'leading_constant_argument':endpoints(constant.arg()),
                'positive_growth_base':(P*abs(lambdas[-1])).str(50),
                'leading_sign_predictions':predictions,
                'input_sha256':{str(ATLAS):sha256(ATLAS)},
                'source_sha256':{n:sha256(Path(__file__).with_name(n)) for n in
                                 ['dh_split_pair_asymptotic.py','character_zero_atlas.py']},
                'scope':'Ordering and nonzero leading coefficient are certified. Predicted finite-rank signs omit an unquantified asymptotic remainder; direct determinants supply finite certificates.'}
    (OUT/'split_pair_asymptotic.json').write_text(json.dumps(result,indent=2)+'\n')
    print('split shift',shift,'period',(2*arb.pi()/phi).str(15),'phase',constant.arg().str(15),flush=True)
    print('predicted negative ranks',[r['rank'] for r in predictions if r['sign']=='negative'][:3],flush=True)


if __name__=='__main__':
    run()
