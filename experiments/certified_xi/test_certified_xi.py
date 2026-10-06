import math
import json
import tempfile
from pathlib import Path
import unittest
from fractions import Fraction
from flint import arb, arb_mat, ctx
from coefficients import generate, taylor_coefficients, theta_coefficient, theta_tail_bounds
from laboratory import interval, minor, deficits, complete_symmetric, sign, load_coefficients


class CertifiedXiTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 512

    def test_independent_normalization_and_theta_tails(self):
        mu = taylor_coefficients(8, 1024)
        for n in (0, 2, 8):
            theta, evidence = theta_coefficient(n, 12, 4, 256, 96)
            self.assertTrue(theta.overlaps(mu[n]))
            self.assertFalse((theta/2).overlaps(mu[n]))
            self.assertGreater(Fraction(evidence['spatial_tail_absolute_upper']), 0)
        self.assertTrue(mu[0] > arb('0.497'))
        self.assertTrue(mu[0] < arb('0.498'))
        old, _ = theta_tail_bounds(2, 8, 4)
        new, _ = theta_tail_bounds(2, 12, 4)
        self.assertTrue(new < old)

    def test_precision_and_domain_fail_closed(self):
        with self.assertRaises(ValueError):
            generate(max_n=-1)
        with self.assertRaises(ArithmeticError):
            generate(max_n=8, bits=128, max_bits=128, accuracy=1024, theta_max_n=-1)
        with self.assertRaises(ArithmeticError):
            theta_tail_bounds(100, 12, 1)
        with self.assertRaises(ValueError):
            interval({'lo':'2','hi':'1'})
        self.assertEqual(sign(arb(0,1)), 'unresolved')

    def test_loader_rejects_forged_indices_and_formula_disagreement(self):
        data=generate(max_n=4,bits=512,accuracy=64,theta_max_n=0)
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/'coefficients.json'
            path.write_text(json.dumps(data))
            self.assertEqual(len(load_coefficients(path)[0]),5)
            data['coefficients'][1]['n']=3
            path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):
                load_coefficients(path)
            data['coefficients'][1]['n']=1
            data['theta_check']['records'][0]['enclosure']={'lo':'1','hi':'2'}
            path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):
                load_coefficients(path)

    def test_exponential_reference_saturates_candidate(self):
        mu=[arb(1)/math.factorial(n) for n in range(20)]
        for r in range(1,7):
            for m in range(1,7):
                formula=arb(1)
                for j in range(r):
                    formula*=arb(math.factorial(j))/math.factorial(m+j)
                center=minor(mu,r,m)
                self.assertTrue(center.overlaps(formula))
                eta=1-minor(mu,r,m-1)*minor(mu,r,m+1)/center**2
                self.assertTrue(eta.overlaps(arb(r)/(m+r)))

    def test_exact_non_rh_control(self):
        # Determinant is rational, not inferred from numerical roots.
        mu = [arb(3+4**n)/math.factorial(2*n) for n in range(12)]
        raw = minor(mu,6,2)*mu[0]**6
        expected = arb('-26968264743653/74568823160832000')
        self.assertTrue(raw.overlaps(expected))
        self.assertTrue(raw < 0)
        for r in range(1,6):
            for m in range(6):
                self.assertTrue(minor(mu,r,m) > 0)

    def test_deficit_identity_and_dual_recurrence(self):
        mu = taylor_coefficients(12,1024)
        for row in deficits(mu):
            n = row['n']
            direct = minor(mu,3,n+2)*(mu[0]/mu[n+2])**3
            self.assertTrue(direct.overlaps(interval(row['normalized_D3'])))
            self.assertEqual(row['status'],'positive')
        e=[x/mu[0] for x in mu]
        h=complete_symmetric(e)
        for r,m in ((2,3),(4,2),(3,4)):
            dual=arb_mat([[h[r+i-j] if r+i-j>=0 else arb(0) for j in range(m)] for i in range(m)]).det()
            self.assertTrue(dual.overlaps(minor(mu,r,m)))
            residual=minor(mu,r+1,m)*minor(mu,r-1,m)-minor(mu,r,m)**2+minor(mu,r,m-1)*minor(mu,r,m+1)
            self.assertTrue(residual.contains(0))

if __name__ == '__main__':
    unittest.main()
