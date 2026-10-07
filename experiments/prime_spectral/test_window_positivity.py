"""Normalization and fail-closed regressions for full-window certification."""
import json
from pathlib import Path
import tempfile
import unittest

from flint import arb, ctx

from verify_window_positivity import verify
from compact_window_certificate import bounds, certify, fourier_legendre, pole_legendre


CERTIFICATE = Path(__file__).resolve().parents[2] / 'research/prime_spectral/window_positivity_exp_1p2.json'


class WindowPositivityTests(unittest.TestCase):
    def test_fourier_constant_and_linear_normalizations(self):
        with ctx.workprec(256):
            a,t=arb(3)/5,arb(7)/3
            values=fourier_legendre(t,a,5)
            z=a*t
            self.assertTrue(values[0].overlaps((2*a).sqrt()*z.sinc()))
            self.assertTrue(values[1].overlaps((6*a).sqrt()*(z.sin()-z*z.cos())/z**2))
            at_zero=fourier_legendre(arb(0),a,5)
            self.assertTrue(at_zero[0].overlaps((2*a).sqrt()))
            self.assertTrue(all(v.is_zero() for v in at_zero[1:]))

    def test_pole_constant_and_linear_normalizations(self):
        with ctx.workprec(256):
            a=arb(3)/5
            values=pole_legendre(a,2)
            self.assertTrue(values[0].overlaps(4*(a/2).sinh()/(2*a).sqrt()))
            exact=(3/(2*a)).sqrt()/a*(4*a*(a/2).cosh()-8*(a/2).sinh())
            self.assertTrue(values[1].overlaps(exact))

    def test_insufficient_high_frequency_envelope_rejected(self):
        with ctx.workprec(128):
            with self.assertRaises(ValueError):
                bounds(arb(3)/5,4,160,80,[(2,2),(3,3)])

    def test_invalid_compression_rejected(self):
        for count in (0,3):
            with self.assertRaises(ValueError):
                certify(count=count)

    def test_saved_full_certificate_rechecks(self):
        self.assertEqual(verify(CERTIFICATE,independent=False)['public_lower'],'9e-13')

    def test_prime_or_parity_removal_cannot_verify(self):
        original=json.loads(CERTIFICATE.read_text())
        for field in ('active_prime_powers','sectors'):
            data=dict(original)
            data[field]=data[field][:-1]
            with tempfile.TemporaryDirectory() as directory:
                path=Path(directory)/'tampered.json'
                path.write_text(json.dumps(data))
                with self.assertRaises(ValueError):
                    verify(path,independent=False)

    def test_omitted_space_allowance_cannot_be_zeroed(self):
        data=json.loads(CERTIFICATE.read_text())
        data['infinite_coupling_bound']={'lo':'0','hi':'0'}
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'tampered.json'
            path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):
                verify(path,independent=False)

    def test_exaggerated_finite_margin_cannot_verify(self):
        data=json.loads(CERTIFICATE.read_text())
        data['finite_lower']='1'
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'tampered.json'
            path.write_text(json.dumps(data))
            with self.assertRaises(ArithmeticError):
                verify(path,independent=False)

    def test_schur_certificate_closes_when_linear_allowance_fails(self):
        path=CERTIFICATE.with_name('window_positivity_exp_1p2_schur.json')
        data=json.loads(path.read_text())
        with ctx.workprec(256):
            self.assertTrue(arb(data['finite_lower']) < arb(data['infinite_coupling_bound']['lo']))
        self.assertEqual(verify(path,independent=False)['block_method'],'schur')
        data['block_method']='linear'
        with tempfile.TemporaryDirectory() as directory:
            changed=Path(directory)/'tampered.json'
            changed.write_text(json.dumps(data))
            with self.assertRaises(ArithmeticError):
                verify(changed,independent=False)

    def test_schur_determinant_cannot_be_fabricated(self):
        data=json.loads(CERTIFICATE.with_name('window_positivity_exp_1p2_schur.json').read_text())
        data['schur_determinant']={'lo':'0','hi':'0'}
        with tempfile.TemporaryDirectory() as directory:
            changed=Path(directory)/'tampered.json'
            changed.write_text(json.dumps(data))
            with self.assertRaises(ArithmeticError):
                verify(changed,independent=False)


if __name__=='__main__':
    unittest.main()
