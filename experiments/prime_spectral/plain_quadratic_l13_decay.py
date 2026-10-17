"""Canonical real primitive L(s,chi_13) decay control (even quadratic).

Conrey label12 has real coefficients, so both parity blocks belong to the
actual single L-function. Its even gamma differs from the odd DH mixture:
conductor-only transfer of kappa is precisely a hypothesis, not a theorem.
"""
import json,math,time
from pathlib import Path
from flint import arb,arb_mat,ctx,dirichlet_char
import control_window_calibration as calibration
from plain_l13_decay import OUT,prime_coefficients
from certified_weil import endpoints
from full_ground_fourier import sha256


def matrices(C,N,bits):
    chi=dirichlet_char(13,12)
    assert chi.is_primitive() and chi.parity()==0
    period=[chi(n).real for n in range(13)]
    class Plain:
        def parameters(self):return None,None,period
    provider,coef,arch=calibration.CharacterControl,calibration.log_derivative_coefficients,calibration.arch_cell
    terms=max(32,math.ceil((bits*math.log(2)+20)/(2*float(arb(C).log().lower()))))
    try:
        calibration.CharacterControl=lambda q,label:Plain()
        # For a real character these are the exact single-L log coefficients.
        def coefficients(a):
            from flint import fmpz
            c=[arb(0) for _ in a]
            for p in range(2,len(a)):
                if fmpz(p).is_prime():
                    n=p
                    while n<len(a):c[n]=chi(n).real*arb(p).log();n*=p
            return c
        calibration.log_derivative_coefficients=coefficients
        calibration.arch_cell=lambda m,n,length,alpha,terms:arch(m,n,length,arb(1)/4,terms)
        E,O,_=calibration.matrices('character',13,12,str(C),N,terms)
    finally:
        calibration.CharacterControl,calibration.log_derivative_coefficients,calibration.arch_cell=provider,coef,arch
    return E,O,terms


def measure(C,N,bits=768):
    p=OUT/f'plain_quadratic_L13_C{C}_N{N}_{bits}bits.json'
    if p.exists():return
    start=time.monotonic()
    with ctx.workprec(bits):
        E,O,terms=matrices(C,N,bits);sectors=[]
        for parity,A in [('even',E),('odd',O)]:
            v=arb_mat(A).eig();assert all(x.imag.contains(0) for x in v)
            v=sorted([x.real for x in v],key=lambda x:float(x.mid()))
            assert all(x>0 for x in v)
            sectors.append({'parity':parity,'dimension':len(A),'lowest_eigenvalues':[endpoints(x) for x in v[:4]],'lowest_display':[x.str(22) for x in v[:4]],'all_finite_eigenvalues_positive':True})
        result={'status':'plain_quadratic_character_finite_spectrum_enclosed','C':str(C),'modes':N,'bits':bits,'conductor':13,'Conrey_label':12,'gamma_alpha':'1/4','archimedean_tail_terms':terms,'sectors':sectors,'seconds':time.monotonic()-start,
                'source_sha256':{n:sha256(Path(__file__).with_name(n)) for n in ['plain_quadratic_l13_decay.py','control_window_calibration.py']},'scope':'Actual single even quadratic L-function. Finite spectra, not full-operator eigenvalues or global GRH. Its gamma parity differs from the odd mixture.'}
    p.write_text(json.dumps(result,indent=2)+'\n');print(C,N,[(s['parity'],s['lowest_display'][0]) for s in sectors],round(result['seconds'],2),flush=True)


if __name__=='__main__':
    for N in [96,128]:
        for C in [16,20,24,28,32]:measure(C,N)
