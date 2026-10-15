"""Geometric saturation, independent integrals, and whole-strip transfer checks."""
import json
from pathlib import Path
import tempfile
import unittest

from flint import acb, arb, ctx

from full_ground_fourier import OUTPUT, energy_distance
from orthogonal_fourier_transfer import (kernel_variance, profile_error,
    protected_mean, validated_base, variance_cover)
from strip_transfer import normalized_profile_upper
from threshold_ground_gap import box

NEW = Path('research/prime_spectral/verification_2026_10_11_orthogonal_fourier')


class OrthogonalFourierTests(unittest.TestCase):
    def test_exact_two_mode_mean_saturates_geometric_bound(self):
        with ctx.workprec(256):
            m, n = arb(12)/13, arb(5)/13
            r=n*n
            # g=m*e0+n*e1, h=n*e0-m*e1, u=m*g-n*h.
            u0, u1=m*m-n*n, 2*m*n
            self.assertTrue((u0*u0+u1*u1).contains(1))
            lower=protected_mean(r,m)
            # Inputs are rounded monotonically before transfer: the result
            # is a lower bound, not necessarily a ball around the exact mean.
            self.assertTrue(lower.lower()<=(arb(119)/169).upper())
            self.assertTrue(abs(lower-u0)<arb(2)**-180)
            _, d=energy_distance(r,0,1)
            self.assertTrue(protected_mean(r,m)>m-d)

    def test_kernel_variance_against_independent_complex_integrals(self):
        with ctx.workprec(192):
            for z in [acb(0),acb(2),acb(0,'0.4'),acb(3,'0.7')]:
                average=acb.integral(lambda t, analytic:(z*t).cos(),arb(-1)/2,arb(1)/2)
                norm=acb.integral(lambda t, analytic:(z*t).cos()*(z.conjugate()*t).cos(),arb(-1)/2,arb(1)/2)
                direct=norm.real-average.real**2-average.imag**2
                self.assertTrue(kernel_variance(z.real,z.imag).overlaps(direct))
            self.assertTrue(kernel_variance(0,0).is_zero())

    def test_complete_cover_and_analytic_tail(self):
        with ctx.workprec(128):
            cover=variance_cover(2,'0.4',extent=16,real_cells=128,imag_cells=8)
            self.assertEqual(cover['rectangles_checked'],1024)
            for a in ['0','0.1','1','3','7','15.9','16','17','100','10000']:
                for b in ['0','0.2','0.4','0.8']:
                    v=kernel_variance(a,b)
                    self.assertTrue(v<cover['upper'])
                    if arb(a)>=16:
                        self.assertTrue(v<cover['tail_upper'])
            self.assertTrue(cover['upper']<arb('0.7'))

    def test_real_two_mode_normalized_profiles_on_complex_strip(self):
        with ctx.workprec(192):
            m,n=arb(12)/13,arb(5)/13
            c,s=m,n
            u0,u1=c*m-s*n,c*n+s*m
            r=s*s
            cover=variance_cover(2,'0.4',real_cells=128,imag_cells=8)
            bound=profile_error(r,m,cover['upper'])
            for z in [acb(0),acb(1),acb(arb.pi()),acb(2,'0.4'),acb(50,'-0.4')]:
                a=z  # support length is two
                e0=a.sinc()
                e1=((a-arb.pi()).sinc()+(a+arb.pi()).sinc())/arb(2).sqrt()
                fg=m*e0+n*e1
                fu=u0*e0+u1*e1
                self.assertTrue(abs(fu/u0-fg/m)<bound)
                if not z.is_zero():
                    point=profile_error(r,m,arb(kernel_variance(2*z.real,2*z.imag).upper()))
                    # At z=pi this example saturates Cauchy-Schwarz, so
                    # independent outward balls can overlap at equality.
                    self.assertTrue(abs(fu/u0-fg/m).upper()<point.upper()+arb(2)**-150)

    def test_invalid_and_unprotected_inputs_fail_closed(self):
        for r,m in [(-1,'0.9'),(1,'0.9'),('nan','0.9'),(0,0),(0,2)]:
            with self.assertRaises(ValueError): protected_mean(r,m)
        for r,m in [('0.25','0.5'),('0.3','0.5')]:
            with self.assertRaises(ArithmeticError): protected_mean(r,m)
        with self.assertRaises(ValueError): profile_error(0,1,-1)
        for args in [(0,1), (1,-1)]:
            with self.assertRaises(ValueError): variance_cover(*args)
        with self.assertRaises(ValueError): variance_cover(1,1,real_cells=0)

    def test_orthogonal_mean_gate_can_pass_when_distance_gate_fails(self):
        with ctx.workprec(192):
            r,m=arb('0.24'),arb('0.5')
            _,distance=energy_distance(r,0,1)
            self.assertTrue(distance>m)
            with self.assertRaises(ArithmeticError): normalized_profile_upper(2,'0.4',m,distance)
            self.assertTrue(protected_mean(r,m)>0)
            self.assertTrue(profile_error(r,m,1).is_finite())

    def test_exact_trial_and_nearly_constant_mean(self):
        with ctx.workprec(192):
            self.assertTrue(protected_mean(0,1).is_exact())
            self.assertTrue(profile_error(0,1,1).is_zero())
            self.assertTrue(protected_mean('0.01',1).overlaps(arb('0.99').sqrt()))

    def test_mean_zero_even_kernel_retains_exponential_growth(self):
        with ctx.workprec(256):
            for B in [arb(8),arb(16),arb(32),arb(64)]:
                V=kernel_variance(0,B)
                explicit=arb(1)/2+B.sinh()/(2*B)-2*(B.cosh()-1)/B**2
                self.assertTrue(V.overlaps(explicit))
                self.assertTrue(V>B.exp()/(8*B))
                self.assertTrue(V<(1+acb(0,B).sinc().real)/2)

    def test_base_hash_tampering_rejected(self):
        base=OUTPUT/'full_ground_fourier.json'
        self.assertEqual(validated_base(base)['frequency_band'],128)
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)
            (p/'manifest.json').write_text((OUTPUT/'manifest.json').read_text())
            raw=json.loads(base.read_text()); raw['results'][0]['trial_rayleigh_enclosure']={'lo':'0','hi':'0'}
            (p/base.name).write_text(json.dumps(raw))
            with self.assertRaises(ValueError): validated_base(p/base.name)

    def test_saved_bounds_improve_both_ground_means_and_all_strips(self):
        data=json.loads((NEW/'orthogonal_transfer.json').read_text())
        with ctx.workprec(256):
            for row in data['results']:
                self.assertTrue(box(row['ground_mean_lower'])>box(row['previous_ground_mean_lower']))
                for strip in row['strips']:
                    self.assertTrue(box(strip['origin_normalized_profile_error_upper'])
                                    <box(strip['elementary_orthogonal_error_upper']))
                    self.assertTrue(box(strip['elementary_orthogonal_error_upper'])
                                    <box(strip['previous_profile_error_upper']))


if __name__=='__main__':
    unittest.main()
