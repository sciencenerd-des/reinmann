"""Independent sequence integrals, adversarial tails and full adjoint replay."""
import json
from pathlib import Path
import unittest

from flint import acb,arb,ctx

from adjoint_fourier_certificate import fourier_coordinate,l2_norm_bounds,matrix_inputs
from boundary_moment_adjoint import (OUT,PROLATE_DIR,asymptotic_sequence_bound,
    coefficients,coherent_tail,certify,ground_pairing_upper,trial_target_pairing)
from canonical_prolate_adjoint import CanonicalProfile,external_target
from certified_weil import entry
from full_ground_fourier import sha256
from threshold_ground_gap import box
from weil_matrix import prime_powers


class BoundaryMomentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=[json.loads((OUT/f'boundary_moment_N{N}_M{P}_cover16x8.json').read_text())
                  for N,P in ((16,128),(32,256))]
        with ctx.workprec(1024):
            cls.profiles={C:CanonicalProfile(PROLATE_DIR/f'jacobi_C{C}_T40.json',
                                           PROLATE_DIR/f'vectors_C{C}_T40.json') for C in (2,3)}

    def test_regular_kernel_integral_representation(self):
        with ctx.workprec(256):
            for r in (arb('1/100'),arb('1/3'),arb(3).log(),arb(13).log()):
                E=acb.integral(lambda t,analytic:(t*r/2).exp()/2,0,1)
                S=acb.integral(lambda t,analytic:(1-t)**2*(t*r).cosh()/2,0,1)
                sinhc=(acb(0,1)*r).sinc()
                regular=2*(r/2).cosh()-(E-r*S)/(2*sinhc)
                direct=2*(r/2).cosh()-(r/2).exp()/(2*r.sinh())+1/(2*r)
                self.assertTrue(regular.real.overlaps(direct))
                self.assertTrue(regular.imag.contains(0))

    def test_asymptotic_sequence_against_independent_sine_integrals(self):
        with ctx.workprec(256):
            for C in (2,3,5):
                L=arb(C).log()
                for m in (7,23,65):
                    w=2*arb.pi()*m/L
                    def integrand(r,analytic):
                        return ((r/2).exp()*w*(w*r).sinc()/(2*(acb(0,1)*r).sinc())
                                -2*(r/2).cosh()*(w*r).sin())/arb.pi()
                    arch=acb.integral(integrand,0,L)
                    prime=sum((arb(p).log()/arb(q).sqrt()*(w*arb(q).log()).sin()/arb.pi()
                               for q,p in prime_powers(C) if q<C),arb(0))
                    B,details=asymptotic_sequence_bound(C,m-1)
                    D=box(details['archimedean_asymptotic_error_coefficient'])
                    self.assertTrue(abs(arch.real-arb('1/4'))<D/m)
                    self.assertTrue(abs(arch.real+prime)<B)

    def test_geometric_tail_dominates_all_admissible_sequence_extremes(self):
        with ctx.workprec(192):
            exact=[['0.3','0.2'],['-0.17','0.05'],['0.03','-0.09'],['0.004','0.002']]
            h=coefficients(exact);b=list(map(arb,['0','0.2','0.4','-0.1']))
            z=acb('1','-2/5');P=20
            for C in (2,3):
                B,_=asymptotic_sequence_bound(C,P)
                L=arb(C).log()
                for J in (1,2,3):
                    bound,_=coherent_tail(C,exact,b,z,P,J)
                    squared=arb(0)
                    for m in range(P+1,P+401):
                        worst=arb(0)
                        for bm in (-arb(B.upper()),arb(B.upper())):
                            value=arb(2).sqrt()*bm*h[0]/m
                            value+=sum((2*(m*bm-n*b[n])*h[n]/(m*m-n*n) for n in range(1,len(h))),acb(0))
                            value-=fourier_coordinate(z,L,m)
                            worst=arb(max(worst.upper(),(abs(value)**2).upper()))
                        squared+=worst
                    self.assertTrue(squared.sqrt()<bound,(C,J))

    def test_nonzero_constant_correction_has_explicit_boundary_tail(self):
        with ctx.workprec(256):
            bound,d=coherent_tail(2,[['1','0'],['0','0']],[arb(0),arb('1/4')],acb(0),128)
            self.assertTrue(bound>0)
            self.assertTrue(box(d['boundary_tail_upper']).overlaps(bound))
            self.assertTrue(box(d['entire_geometric_remainder_upper']).is_zero())
            self.assertTrue(box(d['endpoint_coefficient']['real']).contains(1))

    def test_ground_pairing_bound_against_complex_finite_geometry(self):
        with ctx.workprec(256):
            for values in ([acb('0.1','0.2'),acb('0.7','-0.4'),acb('0.3')],
                           [acb(1),acb(0),acb(0)], [acb(0),acb(0,1),acb(0)]):
                norm=arb(l2_norm_bounds(values).upper())
                for mass in (arb('1/5'),arb('9/10')):
                    bound,_=ground_pairing_upper(values,norm,['1','0','0'],mass)
                    for t in (arb(0),mass/2,mass):
                        for phase in (acb(1),acb(0,1),acb(-1)):
                            pairing=(1-t).sqrt()*values[0]+t.sqrt()*phase*values[1]
                            self.assertTrue(abs(pairing)<=bound)

    def test_stable_trial_pairing_matches_independent_target_coordinates(self):
        with ctx.workprec(1024):
            for row in self.data[1]['results']:
                C=row['cutoff'];p=self.profiles[C];trial=row['ground_trial_coefficients']
                c=list(map(arb,trial));norm=sum((v*v for v in c),arb(0)).sqrt();g=[v/norm for v in c]
                for z in (acb(0),acb(1,'2/5'),acb('1/2','-1/4'),acb(7,'2/5')):
                    _,k=external_target(z,p.length,p,8)
                    direct=sum((g[n]*k[n] for n in range(9)),acb(0))
                    self.assertTrue(trial_target_pairing(p,z,trial).overlaps(direct))

    def test_full_tail_expansion_reconstructs_actual_omitted_rows(self):
        with ctx.workprec(384):
            for row in self.data[1]['results']:
                C=row['cutoff'];L=arb(C).log();powers=prime_powers(C)
                _,b,_=matrix_inputs(C,32,256,OUT)
                saved=row['probes'][2];h=coefficients(saved['exact_coefficients']);z=acb(1,'2/5')
                E=h[0]+arb(2).sqrt()*sum(h[1:],acb(0))
                for m in (257,300):
                    bm=m*entry(m,0,L,powers,C)
                    original=arb(2).sqrt()*bm*h[0]/m+sum((2*(m*bm-n*b[n])*h[n]/(m*m-n*n)
                                                                        for n in range(1,33)),acb(0))
                    split=arb(2).sqrt()*E*bm/m
                    split+=bm*sum((2*n*n*h[n]/(m*(m*m-n*n)) for n in range(1,33)),acb(0))
                    split-=sum((2*n*b[n]*h[n]/(m*m-n*n) for n in range(1,33)),acb(0))
                    self.assertTrue(original.overlaps(split))
                    self.assertTrue(abs(bm)<asymptotic_sequence_bound(C,256)[0])

    def test_entire_saved_rectangle_and_points_replay(self):
        with ctx.workprec(1024):
            for data in self.data:
                N,P=data['modes'],data['prefix']
                for row in data['results']:
                    C=row['cutoff'];p=self.profiles[C]
                    with ctx.workprec(384):A,b,_=matrix_inputs(C,N,P,PROLATE_DIR if N==16 else OUT)
                    nu,delta,mean=[box(row[k]) for k in ('spectral_shift','eigenvalue_uncertainty','ground_mean_lower')]
                    mass=box(row['ground_orthogonal_mass_upper']);trial=row['ground_trial_coefficients']
                    cover=row['rectangle_cover'];nx=cover['real_half_subdivisions'];ny=cover['imag_half_subdivisions']
                    self.assertEqual({tuple(a['cell']) for a in cover['cells']},{(i,j) for i in range(nx) for j in range(2*ny)})
                    for saved in row['probes']+cover['cells']:
                        if 'z' in saved:z=acb(saved['z']['real'],saved['z']['imag'])
                        else:
                            i,j=saved['cell'];z=acb((arb(i)/nx).union(arb(i+1)/nx),
                                (arb(2)*(j-ny)/(5*ny)).union(arb(2)*(j+1-ny)/(5*ny)))
                        replay=certify(C,saved['exact_coefficients'],A,b,z,p,nu,delta,mean,trial=trial,mass=mass)
                        self.assertEqual(replay,{k:saved[k] for k in replay},(C,N,saved.get('cell')))
                    if N==32:
                        self.assertTrue(box(cover['normalized_profile_error_upper'])<arb('0.000952' if C==2 else '0.006274'))

    def test_larger_matrix_against_direct_geometric_entries(self):
        with ctx.workprec(384):
            for C in (2,3):
                A,_,_=matrix_inputs(C,32,256,OUT);L=arb(C).log();powers=prime_powers(C)
                for m,n in ((32,32),(100,31),(256,32)):
                    direct=entry(m,n,L,powers,C)+entry(m,-n,L,powers,C)
                    self.assertTrue(A[m][n].overlaps(direct),(C,m,n))

    def test_source_dependency_and_artifact_hashes(self):
        for data in self.data:
            for category in ('source_sha256','dependency_sha256'):
                for path,digest in data[category].items():self.assertEqual(sha256(Path(path)),digest,path)

    def test_invalid_inputs_rejected(self):
        for exact in ([],[['0','0']], [['nan','0'],['0','0']]):
            with self.assertRaises(ValueError):coefficients(exact)
        for C,P in ((1,20),(2,0),(2.5,20)):
            with self.assertRaises(ValueError):asymptotic_sequence_bound(C,P)
        with self.assertRaises(ValueError):coherent_tail(2,[['0','0'],['1','0']],[arb(0),arb(1)],0,1)
        with self.assertRaises(ValueError):ground_pairing_upper([acb(1)],arb(1),['1','0'],arb('1/2'))
        with self.assertRaises(ValueError):ground_pairing_upper([acb(1)],arb(1),['1'],arb(1))


if __name__=='__main__':unittest.main()
