from fractions import Fraction as F
import json
import math
import unittest
from flint import arb,ctx
from coefficients import theta_coefficient
from continuous_theta import log_moments,tail_bounds,curvature,run as run_points
from continuous_cover import moment_box,curvature_box,verify_partition,run as run_cover
from laboratory import interval
from verify_cover import summarize,summarize_union


class ContinuousThetaTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=256

    def test_integer_moments_match_independent_u_integral(self):
        for n in (0,2,4):
            moments,_=log_moments(str(n))
            mu,_=theta_coefficient(n,12,4,256,64)
            self.assertTrue((2*moments[0]/math.factorial(2*n)).overlaps(mu))
            self.assertFalse((moments[0]/math.factorial(2*n)).overlaps(mu))
            self.assertTrue(moments[2]/moments[0]-(moments[1]/moments[0])**2>0)

    def test_moment_boxes_enclose_fractional_interior(self):
        for a,b in ((F(0),F(1,8)),(F(1),F(9,8))):
            box=moment_box(a,b,{})
            mid,_=log_moments(str((a+b)/2))
            for outer,inner in zip(box,mid):
                self.assertTrue(outer.contains(inner))

    def test_tail_and_accuracy_fail_closed(self):
        small,_,_=tail_bounds(arb(0),2,left=64)
        smaller,_,_=tail_bounds(arb(0),2,left=80)
        self.assertTrue(smaller<small)
        with self.assertRaises(ValueError):
            log_moments('-1')
        with self.assertRaises(ArithmeticError):
            log_moments('0',accuracy=128)
        with self.assertRaises(ValueError):
            run_points(['1','1'])

    def test_fractional_curvature_and_enclosure(self):
        point=curvature('3/2')
        self.assertEqual(point['G_status'],'positive')
        cell=curvature_box(F(3,2)-F(1,65536),F(3,2)+F(1,65536),{})
        self.assertEqual(cell['status'],'positive')
        self.assertTrue(interval(cell['G']).contains(interval(point['curvature_numerator_G'])))
        self.assertTrue(interval(cell['log_epsilon_second'])<0)

    def test_small_complete_cover(self):
        result=run_cover('1','4097/4096',max_depth=8,max_cells=32)
        self.assertEqual(result['status'],'certified_finite_interval')
        summary=summarize(result)
        self.assertEqual(summary['certified_subintervals'],[['1','4097/4096']])

    def test_serialized_cover_rejects_false_labels(self):
        positive={'lo':'1','hi':'3/2','status':'positive',
                  'G':{'lo':'1/100','hi':'1/10'},
                  'log_epsilon_second':{'lo':'-1','hi':'-1/100'}}
        unresolved={'lo':'3/2','hi':'2','status':'unresolved'}
        data={'domain':['1','2'],'status':'incomplete_cover','cells':[positive,unresolved]}
        self.assertEqual(summarize(data)['certified_subintervals'],[['1','3/2']])
        data['status']='certified_finite_interval'
        with self.assertRaises(ValueError):
            summarize(data)
        data['status']='incomplete_cover'
        positive['G']['lo']='-1'
        with self.assertRaises(ValueError):
            summarize(data)

    def test_cover_budget_is_not_success(self):
        result=run_cover('1','2',max_depth=0,max_cells=1)
        self.assertEqual(result['status'],'incomplete_cover')
        self.assertEqual(len(result['cells']),1)
        with self.assertRaises(ArithmeticError):
            verify_partition([{'lo':'1','hi':'3/2'},{'lo':'7/4','hi':'2'}],F(1),F(2))
        with self.assertRaises(ArithmeticError):
            verify_partition([{'lo':'1','hi':'7/4'},{'lo':'3/2','hi':'2'}],F(1),F(2))

    def test_union_requires_complete_adjacent_compatible_covers(self):
        def cover(lo,hi,source='same'):
            return {'domain':[lo,hi], 'status':'certified_finite_interval',
                    'method':'coupled_G_derivative_mean_value',
                    'source_hashes':{'coupled_cover.py':source},'bits':256,
                    'theta_terms':12,'left_log_cutoff':64,'upper_u_cutoff':4,
                    'cells':[{'lo':lo,'hi':hi,'status':'positive',
                              'G':{'lo':'1/2','hi':'3/2'},
                              'log_epsilon_second':{'lo':'-2','hi':'-1/4'},
                              'midpoint_G':{'lo':'1','hi':'1'},
                              'derivative_G':{'lo':'0','hi':'0'},
                              'variation_radius':'0'}]}
        left,right=cover('1','2'),cover('2','3')
        inputs=[('left',json.dumps(left).encode()),('right',json.dumps(right).encode())]
        union=summarize_union(inputs)
        self.assertEqual(union['domain'],['1','3'])
        self.assertEqual(union['cell_counts']['positive'],2)
        self.assertEqual(union['uniform_negative_log_curvature_margin'],'1/4')
        with self.assertRaises(ValueError):
            summarize_union([inputs[0],('right',json.dumps(cover('5/2','3')).encode())])
        with self.assertRaises(ValueError):
            summarize_union([inputs[0],('right',json.dumps(cover('2','3','other')).encode())])
        with self.assertRaises(ValueError):
            summarize_union([inputs[0],inputs[0]])
        left.pop('method')
        with self.assertRaises(ValueError):
            summarize_union([('left',json.dumps(left).encode()),inputs[1]])

if __name__=='__main__':
    unittest.main()
