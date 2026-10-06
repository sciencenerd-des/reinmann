import math
import unittest
from weil_matrix import correlation, components, prime_powers, matrix, jacobi, run, simpson

class WeilTests(unittest.TestCase):
    def test_prime_support(self):
        self.assertEqual(prime_powers(13),[(2,2),(3,3),(4,2),(5,5),(7,7),(8,2),(9,3),(11,11),(13,13)])

    def test_correlation_against_sine_formula(self):
        L=math.log(13)
        for m in range(-3,4):
            for n in range(-3,4):
                for y in (0,L/7,L/2,L):
                    expected=(math.sin(2*math.pi*m*y/L)-math.sin(2*math.pi*n*y/L))/(math.pi*(n-m)) if m!=n else 2*(1-y/L)*math.cos(2*math.pi*n*y/L)
                    self.assertAlmostEqual(correlation(m,n,y,L),expected,places=13)
                    self.assertEqual(correlation(m,n,-y,L),correlation(n,m,y,L))

    def test_analytic_pole_and_tail(self):
        L=math.log(13)
        c=components(0,0,L,2048,prime_powers(13))
        # Independent elementary integral of 4(1-y/L)cosh(y/2).
        self.assertAlmostEqual(c['pole'],16*(math.cosh(L/2)-1)/L,places=10)
        self.assertLess(c['archimedean_tail'],0)
        # Check tail by integrating on [L,40]; omitted remainder < 1e-16.
        numeric=simpson(lambda t: -1/math.sinh(L+t),40-L,10000)
        self.assertAlmostEqual(c['archimedean_tail'],numeric,places=10)

    def test_matrix_symmetry_refinement_and_jacobi(self):
        a=matrix(5,2,256)
        self.assertEqual(a,[list(r) for r in zip(*a)])
        eig,residual,_=jacobi([[2.,1.],[1.,2.]])
        self.assertAlmostEqual(eig[0],1)
        self.assertAlmostEqual(eig[1],3)
        self.assertLess(residual,1e-12)
        result=run(5,2,256)
        self.assertLess(result['refinement_max_entry_difference'],1e-6)
        self.assertEqual(result['status'],'uncertified_float_diagnostic')
        with self.assertRaises(ValueError):
            matrix(1,2,256)
        with self.assertRaises(ValueError):
            matrix(5,17,256)

if __name__=='__main__':
    unittest.main()
