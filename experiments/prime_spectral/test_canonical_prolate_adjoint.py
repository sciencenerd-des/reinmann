"""Independent unprojected Fourier integrals and complete certificate replay."""
import json
from pathlib import Path
import tempfile
import unittest

from flint import acb, arb, ctx

from adjoint_fourier_certificate import OUT as MATRIX_DIR, fourier_coordinate, matrix_inputs
from canonical_prolate_adjoint import (OUT, CanonicalProfile, certify_external,
    external_target, widen)
from certified_prolate_projection import _normalized_trial
from certified_weil import entry
from weil_matrix import prime_powers
from full_ground_fourier import sha256
from threshold_ground_gap import box


class CanonicalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=json.loads((OUT/'canonical_adjoint_cover16x8.json').read_text())
        cls.refined=json.loads((OUT/'canonical_adjoint_N16_M128_cover16x8.json').read_text())
        cls.profiles={}
        with ctx.workprec(1024):
            for C in (2,3):
                cls.profiles[C]=CanonicalProfile(OUT/f'jacobi_C{C}_T40.json',OUT/f'vectors_C{C}_T40.json')

    def independent_integral(self,C,z=None,moment=None):
        """Integrate Legendre recurrence, without monomials or Mellin formulas.

        Integrate each arithmetic summand on its own complete support interval;
        this retains the threshold jumps in the full sum.
        """
        data=json.loads((OUT/f'vectors_C{C}_T40.json').read_text())
        zero,four=[_normalized_trial(data['modes'][key]['trial_vector']) for key in ('0','2')]
        r=four[0]/zero[0]
        amplitudes=[(four[k]-r*zero[k])*(arb(4*k+1)/2).sqrt() for k in range(len(zero))]
        L=arb(C).log(); lam=arb(C).sqrt(); result=acb(0)
        def H(x):
            previous,current=acb(1),x
            value=amplitudes[0]*previous
            for degree in range(1,2*len(zero)-2):
                previous,current=current,((2*degree+1)*x*current-degree*previous)/(degree+1)
                if (degree+1)%2==0:
                    value+=amplitudes[(degree+1)//2]*current
            return value
        for n in range(1,C):
            def integrand(t,analytic):
                K=(t/2).exp()*H(n*t.exp()/lam)
                return K*(t**moment if moment is not None else (-acb(0,1)*z*t).exp())
            result+=acb.integral(integrand,-L/2,L/2-arb(n).log())
        return result

    def test_full_complex_transform_against_independent_legendre_integrals(self):
        with ctx.workprec(384):
            for C,p in self.profiles.items():
                for z in (acb(0),acb(1,'2/5'),acb(1,'-2/5')):
                    direct=self.independent_integral(C,z=z)
                    self.assertTrue(p.raw_direct(z).overlaps(direct),(C,z))
                    self.assertTrue(p.raw_taylor(z).overlaps(direct),(C,z))

    def test_first_three_moments_against_independent_physical_integrals(self):
        with ctx.workprec(384):
            for C,p in self.profiles.items():
                for j in (1,2,3):
                    direct=self.independent_integral(C,moment=j)
                    self.assertTrue(p.moments[j].overlaps(direct.real),(C,j))
                    self.assertTrue(direct.imag.contains(0))

    def test_taylor_remainder_and_stable_target_at_large_frequency(self):
        with ctx.workprec(1024):
            for C,p in self.profiles.items():
                for z in (acb(1,'-2/5'),acb(10,'2/5'),acb(-7,'1/4')):
                    direct=p.raw_direct(z)/p.moments[0]
                    self.assertTrue(p.raw_taylor(z).overlaps(p.raw_direct(z)))
                    self.assertTrue(p.target_constant(z).overlaps(fourier_coordinate(z,p.length,0)-direct))

    def test_exact_origin_and_protected_normalization(self):
        with ctx.workprec(1024):
            for p in self.profiles.values():
                self.assertTrue(p.origin>arb('0.49'))
                self.assertTrue(p.profile(0).real==1)
                self.assertTrue(p.target_constant(0).is_zero())
                self.assertTrue(p.output_error<arb('1e-40'))
                self.assertTrue(p.moments[0].overlaps(p.raw_direct(0).real))

    def test_odd_candidate_part_is_retained_and_nonzero(self):
        with ctx.workprec(1024):
            p2=self.profiles[2].profile(1);p3=self.profiles[3].profile(1)
            self.assertTrue(-p2.imag>arb('0.00054020'))
            self.assertTrue(p3.imag>arb('0.000000475782'))
            for p in self.profiles.values():
                z=acb('1/2','-2/5')
                self.assertTrue(p.profile(-z.conjugate()).overlaps(p.profile(z).conjugate()))

    def test_interval_target_encloses_corners_and_center(self):
        with ctx.workprec(1024):
            for p in self.profiles.values():
                cell=acb(arb('1/4').union(arb('3/8')),arb('-2/5').union(arb('-3/10')))
                target=p.target_constant(cell);profile=p.profile(cell)
                for x,y in [('1/4','-2/5'),('3/8','-3/10'),('5/16','-7/20')]:
                    z=acb(x,y)
                    self.assertTrue(target.contains(p.target_constant(z)))
                    self.assertTrue(profile.contains(p.profile(z)))

    def test_every_saved_point_and_full_rectangle_cell_replays(self):
        with ctx.workprec(1024):
            for data in (self.data,self.refined):
                self.replay_certificate(data)

    def replay_certificate(self,data):
        with ctx.workprec(1024):
            N=data['correction_modes'];M=data['residual_prefix']
            directory=MATRIX_DIR if (N,M)==(8,64) else OUT
            for row in data['results']:
                C=row['cutoff']; p=self.profiles[C]
                with ctx.workprec(384):
                    A,b,_=matrix_inputs(C,N,M,directory)
                nu=box(row['spectral_shift']);delta=box(row['eigenvalue_uncertainty']);mean=box(row['ground_mean_lower'])
                cover=row['rectangle_cover'];nx=cover['real_half_subdivisions'];ny=cover['imag_half_subdivisions']
                self.assertEqual(len(cover['cells']),2*nx*ny)
                self.assertEqual({tuple(a['cell']) for a in cover['cells']},
                                 {(i,j) for i in range(nx) for j in range(2*ny)})
                for saved in row['probes']+cover['cells']:
                    if 'z' in saved:
                        z=acb(saved['z']['real'],saved['z']['imag'])
                    else:
                        i,j=saved['cell']
                        z=acb((arb(i)/nx).union(arb(i+1)/nx),
                              (arb(2)*(j-ny)/(5*ny)).union(arb(2)*(j+1-ny)/(5*ny)))
                    replay=certify_external(C,saved['exact_positive_coefficients'],A,b,z,p,nu,delta,mean)
                    for key,value in replay.items():
                        self.assertEqual(value,saved[key],(C,saved.get('cell'),key))
                self.assertTrue(box(cover['normalized_profile_error_upper'])<arb(('0.00563' if C==2 else '0.08697') if N==8 else ('0.00381' if C==2 else '0.07196')))

    def test_provenance_and_dependency_hashes(self):
        for data in (self.data,self.refined):
            for key in ('dependency_sha256','source_sha256'):
                for path,digest in data[key].items():
                    self.assertEqual(sha256(Path(path)),digest,path)

    def test_larger_matrix_against_direct_geometric_integrals(self):
        with ctx.workprec(384):
            for C in (2,3):
                A,_,_=matrix_inputs(C,16,128,OUT);L=arb(C).log();powers=prime_powers(C)
                for m,n in ((16,16),(30,13),(128,16)):
                    direct=entry(m,n,L,powers,C)+entry(m,-n,L,powers,C)
                    self.assertTrue(A[m][n].overlaps(direct),(C,m,n))

    def test_corrupted_vector_bound_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            j=Path(temp)/'j.json';v=Path(temp)/'v.json'
            j.write_bytes((OUT/'jacobi_C2_T40.json').read_bytes())
            d=json.loads((OUT/'vectors_C2_T40.json').read_text())
            d['modes']['2']['oriented_unit_eigenvector_l2_error_upper']='0'
            v.write_text(json.dumps(d))
            with self.assertRaisesRegex(ValueError,'differs from replay'):
                CanonicalProfile(j,v)
            d['jacobi_certificate_sha256']='corrupt';v.write_text(json.dumps(d))
            with self.assertRaisesRegex(ValueError,'provenance'):
                CanonicalProfile(j,v)

    def test_invalid_frequencies_radius_and_order_rejected(self):
        with ctx.workprec(1024):
            p=self.profiles[2]
            for z in (acb(0,'1/2'),acb('nan')):
                with self.assertRaises(ValueError):p.raw_direct(z)
            with self.assertRaises(ValueError):widen(0,-1)
            with self.assertRaises(ValueError):widen(acb('nan'),0)
            with self.assertRaises(ValueError):CanonicalProfile('unused','unused',order=2)


if __name__=='__main__':
    unittest.main()
