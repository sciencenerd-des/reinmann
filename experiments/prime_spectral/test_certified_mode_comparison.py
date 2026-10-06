import unittest
from flint import arb, ctx
from certified_weil import run
from certified_mode_comparison import box, normalized_vector, compare


class ModeComparisonTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with ctx.workprec(512):
            cls.small=run(13,2)
            cls.large=run(13,4)

    def setUp(self):
        ctx.prec=512

    def test_boundary_and_unit_normalizations(self):
        vector,unit,origin=normalized_vector(self.small)
        boundary=vector[0]+arb(2).sqrt()*sum(vector[1:],arb(0))
        self.assertTrue(boundary.contains(1))
        self.assertTrue(sum((x*x for x in unit),arb(0)).contains(1))
        self.assertEqual(origin[0],arb(1))

    def test_nested_distance_identity_and_compact_bound(self):
        result=compare(self.small,self.large)
        inner=box(result['unit_vector_inner_product'])
        distance=box(result['unit_vector_distance'])
        self.assertTrue((distance**2).overlaps(2-2*inner))
        coefficient=box(result['origin_normalized_coefficient_distance'])
        upper=arb(result['entire_profile_difference_upper'])
        self.assertGreater(upper,coefficient)
        self.assertEqual(result['status'],'certified_finite_nested_mode_comparison_not_convergence')

    def test_rejects_mismatched_support_and_non_nested_spaces(self):
        changed=dict(self.large,cutoff=5)
        with self.assertRaises(ValueError):
            compare(self.small,changed)
        with self.assertRaises(ValueError):
            compare(self.large,self.small)
        with self.assertRaises(ValueError):
            compare(self.small,self.large,radius=-1)
        with self.assertRaises(ValueError):
            normalized_vector(dict(self.small,status='uncertified_float_diagnostic'))


if __name__=='__main__':
    unittest.main()
