"""Finite-section decay for a plain odd Euler-product L-function.

On each real parity sector this is the conjugation-symmetrized single-character
form, (W_chi + W_chibar)/2, not the logarithmic derivative of their L-mixture.
Eigenvalue enclosures below are finite-matrix facts, never full-operator bounds.
"""
import argparse,datetime,json,math,time
from fractions import Fraction
from pathlib import Path
from flint import arb,arb_mat,ctx,dirichlet_char,fmpz
import control_window_calibration as calibration
from certified_weil import endpoints
from full_ground_fourier import sha256

OUT=Path('research/prime_spectral/verification_2026_10_17_log_forecast')


def prime_coefficients(count,label=2):
    chi=dirichlet_char(13,label)
    assert chi.is_primitive() and chi.parity()==1
    coefficients=[arb(0) for _ in range(count+1)]
    for p in range(2,count+1):
        if fmpz(p).is_prime():
            n=p
            while n<=count:
                coefficients[n]=chi(n).real*arb(p).log()
                n*=p
    # correlation_ball already includes both translations; its input is
    # Re(chi(p^k))*log(p), not twice this logarithmic derivative coefficient.
    return coefficients


def matrices(C,modes,bits=768,label=2):
    C=str(Fraction(C));top=math.ceil(Fraction(C));length=arb(C).log()
    terms=max(32,math.ceil((bits*math.log(2)+20)/(2*float(length.lower()))))
    old=calibration.log_derivative_coefficients
    try:
        calibration.log_derivative_coefficients=lambda a:prime_coefficients(len(a)-1,label)
        E,O,_=calibration.matrices('character',13,label,C,modes,terms)
    finally:calibration.log_derivative_coefficients=old
    return E,O,terms


def measure(C,modes,bits=768):
    path=OUT/f'plain_L13_label2_C{C}_N{modes}_{bits}bits.json'
    if path.exists():return json.loads(path.read_text())
    start=time.monotonic()
    with ctx.workprec(bits):
        E,O,terms=matrices(C,modes,bits);sectors=[]
        for name,A in [('even',E),('odd',O)]:
            values=arb_mat(A).eig()
            if any(not v.imag.contains(0) for v in values):raise ArithmeticError('real spectrum unresolved')
            values=sorted([v.real for v in values],key=lambda x:float(x.mid()))
            if any(not v>0 for v in values):raise ArithmeticError('positive finite eigenvalues unresolved')
            sectors.append({'parity':name,'dimension':len(A),'lowest_eigenvalues':[endpoints(x) for x in values[:4]],'lowest_display':[x.str(22) for x in values[:4]],'all_finite_eigenvalues_positive':True})
        result={'status':'plain_character_finite_spectrum_enclosed','C':str(C),'modes':modes,'bits':bits,'archimedean_tail_terms':terms,'conductor':13,'Conrey_label':2,'sectors':sectors,'seconds':time.monotonic()-start,
                'source_sha256':{n:sha256(Path(__file__).with_name(n)) for n in ['plain_l13_decay.py','control_window_calibration.py','character_zero_atlas.py']},
                'scope':'Euler-product single-character real parity form, equivalently half the conjugate-pair form; same odd gamma and conductor as mixtures. Finite eigenvalues only. Global GRH is not assumed or certified.'}
    path.write_text(json.dumps(result,indent=2)+'\n');print(C,modes,[(s['parity'],s['lowest_display'][0]) for s in sectors],round(result['seconds'],2),flush=True);return result


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--C',type=int);p.add_argument('--modes',type=int,default=96);a=p.parse_args()
    OUT.mkdir(parents=True,exist_ok=True)
    if a.C:measure(a.C,a.modes)
    else:
        for N in [96,128]:
            for C in [16,20,24,28,32]:measure(C,N)
