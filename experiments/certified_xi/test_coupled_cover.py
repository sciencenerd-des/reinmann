from fractions import Fraction as F
import unittest
import copy
from flint import arb, ctx
from continuous_theta import log_moments, tail_bounds, curvature
from continuous_cover import moment_box, curvature_box as direct_box
from coupled_cover import numerator, numerator_derivative, curvature_box, run
from laboratory import interval
from verify_cover import summarize


class Jet:
    """Exact first-order dual numbers for an independent product-rule check."""
    def __init__(self, value, derivative=0):
        self.value, self.derivative = F(value), F(derivative)

    @staticmethod
    def lift(other):
        return other if isinstance(other, Jet) else Jet(other)

    def __add__(self, other):
        other = self.lift(other)
        return Jet(self.value+other.value, self.derivative+other.derivative)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.value, -self.derivative)

    def __sub__(self, other):
        return self+-self.lift(other)

    def __rsub__(self, other):
        return self.lift(other)+-self

    def __mul__(self, other):
        other = self.lift(other)
        return Jet(self.value*other.value, self.derivative*other.value+self.value*other.derivative)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.lift(other)
        return Jet(self.value/other.value,
                   (self.derivative*other.value-self.value*other.derivative)/other.value**2)

    def __pow__(self, n):
        return Jet(self.value**n, n*self.value**(n-1)*self.derivative)


class CoupledCoverTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 256

    def test_exact_derivative_product_rule(self):
        for t, q, lp, lpp, lppp in ((F(3,2), F(2,3), F(-2,5), F(7,11), F(-5,3)),
                                     (F(1), F(1,4), F(3), F(-2), F(7))):
            result = numerator(Jet(t, 1), Jet(q, q*lp), Jet(lp, lpp), Jet(lpp, lppp))
            self.assertEqual(result.derivative, numerator_derivative(t, q, lp, lpp, lppp))

    def test_third_moment_and_tail(self):
        for lo, hi in ((F(0), F(1,8)), (F(1), F(9,8))):
            box = moment_box(lo, hi, {}, max_order=3)
            point, _ = log_moments(str((lo+hi)/2), max_order=3)
            self.assertTrue(box[3].contains(point[3]))
        self.assertTrue(tail_bounds(arb(0), 3, left=80)[0] < tail_bounds(arb(0), 3)[0])
        with self.assertRaises(ValueError):
            tail_bounds(arb(0), 4)
        with self.assertRaises(ValueError):
            moment_box(F(0), F(1), {}, max_order=4)
        # A cache populated at lower order must upgrade safely.
        cache = {}
        moment_box(F(0), F(0), cache)
        self.assertEqual(len(moment_box(F(0), F(0), cache, max_order=3)), 4)

    def test_coupling_improves_wide_cell_and_encloses_points(self):
        lo, hi = F(3,2)-F(1,1024), F(3,2)+F(1,1024)
        self.assertEqual(direct_box(lo, hi, {})['status'], 'unresolved')
        cell = curvature_box(lo, hi, {})
        self.assertEqual(cell['status'], 'positive')
        for x in (lo, (3*lo+hi)/4, (lo+hi)/2, hi):
            point = curvature(str(x))
            self.assertTrue(interval(cell['G']).contains(interval(point['curvature_numerator_G'])))

    def test_complete_partition_and_budget_failure(self):
        result = run('1', '65/64', max_cells=64)
        self.assertEqual(result['status'], 'certified_finite_interval')
        self.assertEqual(summarize(result)['certified_subintervals'], [['1', '65/64']])
        forged = copy.deepcopy(result)
        forged['cells'][0]['variation_radius'] = '0'
        with self.assertRaises(ValueError):
            summarize(forged)
        forged = copy.deepcopy(result)
        forged['cells'][0]['G'] = forged['cells'][0]['midpoint_G']
        with self.assertRaises(ValueError):
            summarize(forged)
        incomplete = run('1', '2', max_depth=0, max_cells=1)
        self.assertEqual(incomplete['status'], 'incomplete_cover')
        self.assertEqual(summarize(incomplete)['certified_subintervals'], [])
        with self.assertRaises(ValueError):
            run('0', '2')


if __name__ == '__main__':
    unittest.main()
