import json
from pathlib import Path
import unittest
from flint import arb,ctx
from isolated_kernel import isolated_spectrum,run
from positive_kernel import run as ldl_kernel
from certified_mode_comparison import box


class IsolatedKernelTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_spectrum_and_simple_eigenvector(self):
        values,vector=isolated_spectrum([[2,1],[1,2]])
        self.assertTrue(values[0].contains(1))
        self.assertTrue(values[1].contains(3))
        self.assertTrue((vector[0]+vector[1]).contains(0))

    def test_agrees_with_previous_method(self):
        root=Path(__file__).resolve().parents[2]
        certificate=json.loads((root/'research/prime_spectral/certified_weil_13_4.json').read_text())
        old,new=ldl_kernel(certificate),run(13,4)
        self.assertTrue(box(old['variance']).overlaps(box(new['variance'])))
        self.assertTrue(box(certificate['smallest_even_eigenvalue']).overlaps(box(new['even_spectrum'][0])))

    def test_higher_modes_have_full_positive_kernel(self):
        for N in (12,16):
            result=run(13,N)
            self.assertEqual(result['status'],'certified_finite_isolated_prime_kernel_not_uniform')
            self.assertTrue(all(box(x)>0 for x in result['bernstein_coefficients']))
            self.assertGreater(box(result['spectral_gap']),0)
            self.assertLess(box(result['variance']),arb('0.054'))
            self.assertFalse(box(result['raw_boundary_evaluation']).contains(0))

    def test_invalid_matrix_parameters(self):
        with self.assertRaises(ValueError):
            run(13,17)


if __name__=='__main__':
    unittest.main()
