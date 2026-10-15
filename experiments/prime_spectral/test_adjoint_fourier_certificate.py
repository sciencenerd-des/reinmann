"""Actual matrix identities, independent integrals and entire residual checks."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from flint import acb, arb, ctx

from adjoint_fourier_certificate import (OUT,certify_correction,endpoint_zero_coefficients,
    fourier_coordinate,full_tail,l2_norm_bounds,matrix_inputs,payload_hash,
    sequence_bound,target_coordinates)
from certified_weil import entry
from full_ground_fourier import OUTPUT
from threshold_ground_gap import box
from weil_matrix import prime_powers


class AdjointTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=json.loads((OUT/'adjoint_N8_M64_cover16x8.json').read_text())
        cls.base=json.loads((OUTPUT/'full_ground_fourier.json').read_text())

    def test_divided_difference_matrix_against_direct_integrals(self):
        with ctx.workprec(384):
            for C in [2,3]:
                A,b,_=matrix_inputs(C,8,64,OUT); L=arb(C).log(); pp=prime_powers(C)
                for m,n in [(0,0),(0,3),(1,1),(2,5),(7,2),(8,8),(9,0),(17,3),(64,8)]:
                    if m==n==0: direct=entry(0,0,L,pp,C)
                    elif m==0: direct=arb(2).sqrt()*entry(0,n,L,pp,C)
                    elif n==0: direct=arb(2).sqrt()*entry(m,0,L,pp,C)
                    else: direct=entry(m,n,L,pp,C)+entry(m,-n,L,pp,C)
                    self.assertTrue(A[m][n].overlaps(direct),(C,m,n))

    def test_sequence_against_independent_sine_integrals(self):
        with ctx.workprec(256):
            for C in [2,3]:
                _,b,_=matrix_inputs(C,8,64,OUT); L=arb(C).log()
                for n in [1,7,23]:
                    w=2*arb.pi()*n/L
                    def integrand(r,analytic):
                        sinhc=(acb(0,1)*r).sinc()
                        return ((r/2).exp()*w*(w*r).sinc()/(2*sinhc)
                                -2*(r/2).cosh()*(w*r).sin())/arb.pi()
                    value=acb.integral(integrand,0,L)
                    value+=sum((arb(p).log()/arb(q).sqrt()*(w*arb(q).log()).sin()/arb.pi()
                                for q,p in prime_powers(C) if q<C),arb(0))
                    self.assertTrue(b[n].overlaps(value.real))
                    self.assertTrue(abs(b[n])<sequence_bound(C))

    def test_fourier_coordinates_against_physical_integrals(self):
        with ctx.workprec(256):
            for C in [2,3]:
                L=arb(C).log(); z=acb(1,'0.4')
                for n in [0,1,8]:
                    def integrand(t,analytic):
                        basis=1/L.sqrt() if n==0 else (2/L).sqrt()*(2*arb.pi()*n*t/L).cos()
                        return basis*(-acb(0,1)*z*(t-L/2)).exp()/L.sqrt()
                    direct=acb.integral(integrand,0,L)
                    self.assertTrue(fourier_coordinate(z,L,n).overlaps(direct))

    def test_removable_resonances_use_entire_fourier_formula(self):
        with ctx.workprec(256):
            L=arb(2).log()
            for n in [1,3,8]:
                z=2*arb.pi()*n/L
                value=fourier_coordinate(z,L,n)
                self.assertTrue(value.real.overlaps((-1)**n/arb(2).sqrt()))
                self.assertTrue(value.imag.contains(0))

    def test_endpoint_zero_and_norm_by_independent_integral(self):
        with ctx.workprec(256):
            for row in self.data['results']:
                C=row['cutoff']; L=arb(C).log()
                h=endpoint_zero_coefficients(row['probes'][2]['exact_positive_coefficients'])
                self.assertTrue((h[0]+arb(2).sqrt()*sum(h[1:],acb(0))).contains(0))
                def value(t):
                    return h[0]/L.sqrt()+sum(((2/L).sqrt()*h[n]*(2*arb.pi()*n*t/L).cos()
                                              for n in range(1,len(h))),acb(0))
                def conjugate_value(t):
                    return h[0].conjugate()/L.sqrt()+sum(((2/L).sqrt()*h[n].conjugate()*(2*arb.pi()*n*t/L).cos()
                                              for n in range(1,len(h))),acb(0))
                direct=acb.integral(lambda t,analytic:value(t)*conjugate_value(t),0,L)
                self.assertTrue(l2_norm_bounds(h).overlaps(direct.real.sqrt()))

    def test_all_admissible_sequence_values_obey_tail_majorant(self):
        with ctx.workprec(256):
            for row in self.data['results']:
                C=row['cutoff']; _,b,_=matrix_inputs(C,8,64,OUT)
                positive=row['probes'][2]['exact_positive_coefficients']; h=endpoint_zero_coefficients(positive)
                z=acb(1,'0.4'); _,d=full_tail(C,positive,b,z,64)
                C2,C3,K2=[box(d[k]) for k in ['C2','C3','target_K2']]
                for m in [65,128,1024]:
                    for bm in [sequence_bound(C),-sequence_bound(C)]:
                        image=arb(2).sqrt()*bm*h[0]/m
                        image+=sum((2*(m*bm-n*b[n])*h[n]/(m*m-n*n) for n in range(1,9)),acb(0))
                        residual=image-fourier_coordinate(z,arb(C).log(),m)
                        self.assertTrue(abs(residual)<C3/m**3+(C2+K2)/m**2)

    def test_zero_frequency_is_exact_and_trial_annihilation(self):
        with ctx.workprec(256):
            for row in self.base['results']:
                C=row['threshold_prime']; L=arb(C).log(); trial=row['exact_cosine_coefficients']
                p,k=target_coordinates(0,L,trial,64)
                self.assertEqual(p,1); self.assertTrue(all(x.is_zero() for x in k))
                A,b,_=matrix_inputs(C,8,64,OUT)
                checked=certify_correction(C,[['0','0']]*8,A,b,0,trial,0,1,1)
                self.assertEqual(checked['normalized_profile_error_upper'],{'lo':'0','hi':'0'})
                _,k=target_coordinates(acb(1,'0.4'),L,trial,64)
                self.assertTrue(sum((arb(c)*k[n] for n,c in enumerate(trial)),acb(0)).contains(0))

    def test_norm_enclosures_crossing_zero_remain_finite(self):
        with ctx.workprec(128):
            norm=l2_norm_bounds([acb(arb('0 +/- 1'),arb('0 +/- 1'))])
            self.assertTrue(norm.is_finite()); self.assertTrue(norm.contains(0))
            self.assertTrue(norm.upper()>=arb(2).sqrt().lower())

    def test_corrupted_matrix_payload_rejected(self):
        raw=json.loads((OUT/'matrix_C2_N8_M64.json').read_text())
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'matrix_C2_N8_M64.json'
            bad=copy.deepcopy(raw); bad['b_sequence'][1]={'lo':'0','hi':'0'}
            p.write_text(json.dumps(bad))
            with self.assertRaises(ValueError):matrix_inputs(2,8,64,directory)
            bad=copy.deepcopy(raw);bad['source_sha256']={}; p.write_text(json.dumps(bad))
            with self.assertRaises(ValueError):matrix_inputs(2,8,64,directory)

    def test_invalid_domain_tail_and_scalar_inputs_fail_closed(self):
        with ctx.workprec(128):
            A,b,_=matrix_inputs(2,8,64,OUT); trial=self.base['results'][0]['exact_cosine_coefficients']
            with self.assertRaises(ValueError):endpoint_zero_coefficients([['nan','0']])
            with self.assertRaises(ValueError):full_tail(2,[['1','0']]*8,b,1,8)
            with self.assertRaises(ArithmeticError):full_tail(2,[['1','0']]*8,b,10000,64)
            for delta,mean in [(-1,1),(0,0)]:
                with self.assertRaises(ValueError):certify_correction(2,[['0','0']]*8,A,b,1,trial,0,delta,mean)

    def test_replay_all_fixed_corrections_and_rectangle_cells(self):
        with ctx.workprec(384):
            for row in self.data['results']:
                C=row['cutoff']; A,b,_=matrix_inputs(C,8,64,OUT)
                trial=next(r for r in self.base['results'] if r['threshold_prime']==C)['exact_cosine_coefficients']
                nu,delta,mean=[box(row[k]) for k in ['spectral_shift','eigenvalue_uncertainty','ground_mean_lower']]
                cover=row['rectangle_cover']; worst=arb(0)
                self.assertEqual(len(cover['cells']),16*8)
                for cell in cover['cells']:
                    i,j=cell['cell']; z=acb((arb(i)/16).union(arb(i+1)/16),(arb(j)/20).union(arb(j+1)/20))
                    check=certify_correction(C,cell['exact_positive_coefficients'],A,b,z,trial,nu,delta,mean)
                    upper=box(check['normalized_profile_error_upper'])
                    self.assertTrue(upper.overlaps(box(cell['normalized_profile_error_upper'])))
                    worst=arb(max(worst.upper(),upper.upper()))
                self.assertTrue(abs(worst-box(cover['normalized_profile_error_upper']))<arb(2)**-300)


if __name__=='__main__':unittest.main()
