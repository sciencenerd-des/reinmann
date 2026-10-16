"""Fresh ordinary DH coefficients using the conjugate Dirichlet-L series path."""
import argparse
import json
from pathlib import Path
import time
from flint import acb, acb_series, arb, ctx
from character_zero_atlas import CharacterControl
from davenport_heilbronn_control import kappa
from certified_weil import endpoints
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT=Path('research/prime_spectral/verification_2026_10_15_second_band')


def run(count,bits):
    start=time.monotonic()
    with ctx.workprec(bits):
        old=ctx.cap
        try:
            ctx.cap=2*count+1
            control=CharacterControl(5,2)
            if not control.parameters()[1].overlaps(kappa()):
                raise ArithmeticError('classical DH normalization mismatch')
            s=acb_series([arb('1/2'),1])
            print('fresh L-series coefficients',count,bits,flush=True)
            H=control.jet(acb('1/2'),2*count)
            F=(s*(arb(5)/arb.pi()).log()/2).exp()*((s+1)/2).gamma()*H
            if not F[0].real>0 or any(not F[j].contains(0) for j in range(1,2*count,2)):
                raise ArithmeticError('center or evenness gate failed')
            if any(not F[2*j].imag.contains(0) for j in range(count+1)):
                raise ArithmeticError('coefficient reality gate failed')
            mu=[F[2*j].real/F[0].real for j in range(count+1)]
            mu[0]=arb(1)
            if any(not x.is_finite() for x in mu):
                raise ArithmeticError('coefficient enclosure not finite')
            old_path=Path('research/prime_spectral/verification_2026_10_12_sector/dh_rank430-520_shift0-200_32768bits_coefficients.json')
            old_coefficients=json.loads(old_path.read_text())['coefficients']
            first_path=Path('research/prime_spectral/verification_2026_10_15_split_pair/dh_coefficients_1450_32768bits.json')
            first_coefficients=json.loads(first_path.read_text())['coefficients']
            if any(not mu[j].overlaps(box(x)) for j,x in enumerate(first_coefficients)):
                raise ArithmeticError('second-band and first-band coefficient paths disagree')
            if any(not mu[j].overlaps(box(x)) for j,x in enumerate(old_coefficients)):
                raise ArithmeticError('fresh and prior coefficient paths disagree')
            result={'status':'fresh_DH_ordinary_coefficients_via_Dirichlet_L',
                    'bits':bits,'count':count,'coefficients':[endpoints(x) for x in mu],
                    'positive_coefficient_balls':sum(x>0 for x in mu),
                    'prior_coefficients_overlapping':len(old_coefficients),
                    'first_band_coefficients_overlapping':len(first_coefficients),
                    'input_sha256':{str(old_path):sha256(old_path),str(first_path):sha256(first_path)},
                    'seconds':time.monotonic()-start,
                    'source_sha256':{n:sha256(Path(__file__).with_name(n)) for n in
                                     ['dh_second_band_coefficients.py','character_zero_atlas.py',
                                      'davenport_heilbronn_control.py']}}
        finally:
            ctx.cap=old
    OUT.mkdir(parents=True,exist_ok=True)
    path=OUT/f'dh_coefficients_{count}_{bits}bits.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print('fresh coefficients complete',result['seconds'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--count',type=int,default=2050)
    p.add_argument('--bits',type=int,default=32768)
    a=p.parse_args();run(a.count,a.bits)
