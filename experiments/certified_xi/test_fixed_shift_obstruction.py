from fractions import Fraction
import unittest
from flint import arb, acb, ctx
from laboratory import endpoints
from fixed_shift_obstruction import deformation_tail


class FixedShiftObstructionTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512
        self.poles = {
            'circle': {'radius': '12', 'polynomial_modulus_lower': '1/10'},
            'function_tail': endpoints(arb(0)),
            'poles': [{'lo': str(r), 'hi': str(r), 'amplitude': endpoints(arb(a))}
                      for r,a in ((2,1),(4,-2),(8,3))]}

    def test_exact_prefix_and_positive_coefficients(self):
        N, L = 122, 3200
        a = [Fraction(1,n+1) for n in range(150)]
        modified = [a[n]+(a[n-N]/L**N if n>=N else 0) for n in range(150)]
        self.assertEqual(modified[:N], a[:N])
        self.assertGreater(modified[N], a[N])
        self.assertTrue(all(x>0 for x in modified))

    def test_exact_added_nonreal_zero(self):
        z = acb(0,3200)
        self.assertEqual(1+(z/3200)**122, acb(0))
        self.assertNotEqual(z.imag, 0)

    def test_deformation_tail_preserves_synthetic_pole_bounds(self):
        result = deformation_tail(self.poles, scale=48, start=200)
        self.assertEqual(result['status'], 'deformed_fixed_shift_tail_bounds_pass')
        self.assertLess(arb(result['shift_one_ratio_upper']), 1)
        self.assertLess(arb(result['shift_two_ratio_upper']), 1)
        self.assertEqual(result['preserved_coefficient_indices'], [0,121])

    def test_rejects_unsupported_deformations(self):
        for degree in (2,121,124,122.0):
            with self.assertRaises(ValueError):
                deformation_tail(self.poles, degree=degree)
        with self.assertRaises(ValueError):
            deformation_tail(self.poles, scale=12)
        with self.assertRaises(ValueError):
            deformation_tail(self.poles, start=1)


if __name__ == '__main__':
    unittest.main()
