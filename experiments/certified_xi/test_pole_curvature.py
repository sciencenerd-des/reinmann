import itertools
from fractions import Fraction as F
from pathlib import Path
import unittest
from flint import arb,acb,ctx
from laboratory import interval
from pole_boundary import evaluate,translate,certify_circle,isolate_real_zero,tail_criteria,run
from curvature_error import curvature_transfer,curvature_value,log_moment_errors,propagate_moment_errors


class PoleAndCurvatureTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_contour_count_and_translation_controls(self):
        co=list(map(acb,(2,-3,1)))
        shifted=translate(co,acb('1/3'))
        self.assertTrue(evaluate(shifted,acb('2/5')).overlaps(evaluate(co,acb('1/3')+acb('2/5'))))
        _,record=certify_circle(co,3,arb(0),segments=64)
        self.assertEqual(record['zero_count'],2)
        with self.assertRaises(ArithmeticError):
            certify_circle(co,1,arb(0),segments=64)
        with self.assertRaises(ArithmeticError):
            certify_circle(co,3,arb(0),expected=1,segments=64)
        with self.assertRaises(ArithmeticError):
            certify_circle(co,3,arb(100),segments=64)
        root,_=isolate_real_zero(co,arb(0),'7/10','7/5',width=F(1,10**12))
        self.assertTrue(root.contains(1))

    def test_two_pole_gap_identity_and_tail_rejection(self):
        A,B,alpha,beta=F(2),F(1),F(1),F(1,2)
        g=lambda n:A*alpha**n-B*beta**n
        for n in (1,2,10):
            self.assertEqual(g(n)**2-g(n-1)*g(n+1),A*B*(alpha*beta)**(n-1)*(alpha-beta)**2)
        passed,_=tail_criteria(10,arb(1),arb('.1'),arb(1),arb('.5'),arb('1e-10'),arb(3))
        self.assertTrue(passed)
        passed,_=tail_criteria(2,arb(1),arb('.1'),arb(1),arb('.5'),arb('1e10'),arb(3))
        self.assertFalse(passed)
        with self.assertRaises(ArithmeticError):
            tail_criteria(10,arb(1),arb('.1'),arb(1),arb('.5'),arb(1),arb(2))

    def test_xi_boundary_certificate_bridge_and_tail(self):
        path=Path(__file__).resolve().parents[2]/'research/certified_xi/coefficients_120.json'
        result=run(path)
        self.assertEqual(result['circle']['zero_count'],2)
        self.assertEqual(result['tail']['tail_start'],26)
        self.assertEqual(len(result['finite_bridge']),25)
        self.assertEqual(result['correction_tail']['correction_tail_start'],61)
        self.assertEqual(len(result['finite_correction_bridge']),60)
        self.assertTrue(interval(result['correction_tail']['scaled_curvature_error'])<1)
        self.assertTrue(interval(result['correction_tail']['weighted_successive_ratio'])<1)

    def test_curvature_error_covers_corners_and_fails_closed(self):
        x,q,L,M=map(arb,('2','.5','.1','.01'))
        errors=[arb('1e-6')]*3
        result=curvature_transfer(x,q,L,M,errors)
        self.assertEqual(result['status'],'negative_under_supplied_error_hypotheses')
        for signs in itertools.product((-1,1),repeat=3):
            point=curvature_value(x,q+signs[0]*errors[0],L+signs[1]*errors[1],M+signs[2]*errors[2])
            self.assertTrue(interval(result['curvature_enclosure']).contains(point))
        with self.assertRaises(ArithmeticError):
            curvature_transfer(x,q,L,M,[arb('.6'),arb(0),arb(0)])
        with self.assertRaises(ValueError):
            log_moment_errors([arb(1)]*3,[arb(1)]*3)
        models=[[arb(1),arb(0),arb(0)] for _ in range(3)]
        result=propagate_moment_errors(2,models,[[arb(0)]*3 for _ in range(3)])
        self.assertEqual(result['status'],'negative_under_supplied_error_hypotheses')
        self.assertEqual(F(result['curvature_error_upper']),0)
        self.assertTrue(interval(result['curvature_enclosure']).contains(-arb(16)/81+arb(4)/25))


if __name__=='__main__':
    unittest.main()
