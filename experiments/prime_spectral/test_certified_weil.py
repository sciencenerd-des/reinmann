import unittest
from flint import arb, acb, ctx
from certified_weil import (arch_regularized, correlation_ball, inertia,
                            eigen_interval, certified_matrix, run)
from weil_matrix import matrix as floating_matrix


class CertifiedWeilTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_removable_endpoint_and_complex_identity(self):
        L=arb(13).log()
        for m,n in ((0,0),(3,3),(-2,1)):
            q0=2 if m==n else 0
            expected=arb(q0)/4-1/L
            self.assertTrue(arch_regularized(m,n,acb(0),L).real.overlaps(expected))
            z=acb('0.3','0.1')
            direct=((z/2).exp()*correlation_ball(m,n,z,L)-q0)/(2*z.sinh())
            difference=arch_regularized(m,n,z,L)-direct
            self.assertTrue(difference.contains(0))

    def test_interval_inertia_and_irrational_eigenvalues(self):
        values=[[arb(2),arb(1)],[arb(1),arb(3)]]
        self.assertEqual(inertia(values)[0],0)
        self.assertEqual(inertia(values,arb(5)/2)[0],1)
        smallest=eigen_interval(values,0,100)
        self.assertTrue(smallest.overlaps((5-arb(5).sqrt())/2))
        with self.assertRaises(ArithmeticError):
            inertia([[arb(0),arb(1)],[arb(1),arb(0)]])
        with self.assertRaises(ValueError):
            eigen_interval(values,2)

    def test_agreement_with_existing_float_formula(self):
        values,_,_=certified_matrix(5,2)
        old=floating_matrix(5,2,2048)
        for i,row in enumerate(values):
            for j,x in enumerate(row):
                self.assertLess(abs(x-arb(old[i][j])),arb('1e-8'))

    def test_finite_gates_and_boundary_kernel(self):
        result=run(13,4)
        self.assertEqual(result['status'],'certified_finite_weil_gates')
        self.assertEqual(result['dimension'],9)
        self.assertGreater(arb(result['spectral_gap']['lo']),0)
        self.assertTrue(all(arb(p['lo'])>0 for p in result['boundary_kernel_LDL_pivots']))
        self.assertIn('convergence',result['remaining'])

    def test_invalid_domains(self):
        for cutoff,modes in ((1,2),(5,0),(5,17),(True,2)):
            with self.assertRaises(ValueError):
                certified_matrix(cutoff,modes)


if __name__=='__main__':
    unittest.main()
