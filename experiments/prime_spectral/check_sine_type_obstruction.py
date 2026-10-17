"""Numerical checks of the explicit identities in the written obstruction proof.

These checks accompany the elementary proof; they do not replace it.
"""
import hashlib,json
from pathlib import Path
import mpmath as mp
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'research/prime_spectral/verification_2026_10_17_final_mechanism'
mp.mp.dps=100
def F(z):return z*mp.cos(mp.pi*z)/(z*z-mp.mpf(1)/4)
rows=[]
for z in [mp.mpf('0.2'),mp.mpf('1.25'),mp.mpc('.3','.07'),mp.mpc('2.1','-.4')]:
    fourier=mp.quad(lambda t:mp.j/2*mp.sin(t/2)*mp.exp(mp.j*z*t),[-mp.pi,0,mp.pi])
    error=abs(F(z)-fourier);assert error<mp.mpf('1e-90');rows.append({'z':str(z),'fourier_identity_error':mp.nstr(error,10)})
for b in [mp.mpf('0.25'),mp.mpf('0.001'),mp.mpf('0.00025'),mp.mpf('1e-20')]:
    q=2*mp.re(F(mp.j*b)*mp.conj(F(-mp.j*b)))
    explicit=-2*b*b*mp.cosh(mp.pi*b)**2/(b*b+mp.mpf('.25'))**2
    assert q<0 and abs(q-explicit)<mp.mpf('1e-90')
    rows.append({'b':str(b),'zero_form':mp.nstr(q,20),'closed_formula_error':mp.nstr(abs(q-explicit),10)})
def W(z):return (z*z-1)*mp.cos(mp.pi*z)/((z*z-mp.mpf('.25'))*(z*z-mp.mpf('2.25')))
for z in [mp.mpf('.2'),mp.mpc('1.1','.07')]:
    integral=mp.quad(lambda t:(-mp.mpf(3)/8*mp.cos(t/2)+mp.mpf(5)/24*mp.cos(3*t/2))*mp.exp(mp.j*z*t),[-mp.pi,0,mp.pi])
    assert abs(W(z)-integral)<mp.mpf('1e-90')
    rows.append({'quartet_z':str(z),'fourier_identity_error':mp.nstr(abs(W(z)-integral),10)})
for b in [mp.mpf('.25'),mp.mpf('.001'),mp.mpf('1e-20')]:
    z=1+mp.j*b;a=mp.mpf(15)/4-b*b
    formula=mp.cosh(mp.pi*b)/(b*b+mp.mpf('.25'))*(b*b*(mp.mpf(17)/4+b*b)+2*mp.j*b*(mp.mpf(15)/4+b*b))/(a*a+16*b*b)
    assert abs(W(z)-formula)<mp.mpf('1e-90') and 4*mp.re(W(z)**2)<0
    rows.append({'quartet_b':str(b),'zero_form':mp.nstr(4*mp.re(W(z)**2),20),'closed_formula_error':mp.nstr(abs(W(z)-formula),10)})
def gram(L,b):
    A=L-mp.sin(L);D=mp.sinh(2*b*L)/(2*b)-L
    B=2*(b*mp.sin(L/2)*mp.cosh(b*L)-mp.mpf('.5')*mp.cos(L/2)*mp.sinh(b*L))/(b*b+mp.mpf('.25'))
    return A,B,D
for b in [mp.mpf('.03'),mp.mpf('.01'),mp.mpf('.001')]:
    def determinant(L):
        A,B,D=gram(L,b);return (mp.pi-A)*(mp.pi-D)-B*B
    L=mp.findroot(determinant,mp.pi-32/mp.pi*b*b)
    A,B,D=gram(L,b)
    assert 0<L<mp.pi and abs(determinant(L))<mp.mpf('1e-90')
    Bi=mp.quad(lambda t:mp.sin(t/2)*mp.sinh(b*t),[-L,0,L])
    assert abs(B-Bi)<mp.mpf('1e-90')
    rows.append({'model_b':str(b),'L_cutoff':mp.nstr(L,30),'delta_over_b_squared':mp.nstr((mp.pi-L)/(b*b),20),'limit_32_over_pi':mp.nstr(32/mp.pi,20),'Gram_integral_error':mp.nstr(abs(B-Bi),10),'crossing_residual':mp.nstr(abs(determinant(L)),10)})
paths=[Path(__file__),ROOT/'research/prime_spectral/SINE_TYPE_LOG_COST_OBSTRUCTION_2026_10_17.md']
result={'status':'explicit_Fourier_and_negative_pair_identities_checked','decimal_precision':100,'records':rows,'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},'scope':'Numerical sanity checks only; the accompanying written cardinal-sine and direct pair calculation are the mathematical proof.'}
(OUT/'sine_type_identity_checks.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',len(rows),'identity and sign checks')
