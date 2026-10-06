import unittest
from flint import arb, acb, arb_mat, fmpq, fmpq_mat, fmpq_poly, ctx
from certified_weil import run
from quotient_operator import build, fourier_profile


class QuotientOperatorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with ctx.workprec(512):
            cls.certificate=run(13,2)

    def setUp(self):
        ctx.prec=512

    def test_exact_rational_displacement_quotient_and_determinant(self):
        A=fmpq_mat([[3,-1,-1],[-1,1,-1],[-1,-1,3]])
        c=[fmpq(1,4),fmpq(1,2),fmpq(1,4)]
        d=[-1,0,1]
        self.assertEqual(A*fmpq_mat([[x] for x in c]),fmpq_mat([[0],[0],[0]]))
        T=fmpq_mat([[d[i]*((1 if i==j else 0)-c[i]) for j in range(3)] for i in range(3)])
        B=fmpq_mat([[d[j]*((1 if i==j else 0)-c[i]) for j in (0,2)] for i in (0,2)])
        K=fmpq_mat([[6,2],[2,6]])
        self.assertEqual(K*B,B.transpose()*K)
        z=fmpq_poly([0,1])
        Q=fmpq_poly([0])
        for i in range(3):
            term=fmpq_poly([c[i]])
            for j in range(3):
                if j!=i:
                    term*=z-d[j]
            Q+=term
        self.assertEqual(T.charpoly(),z*Q)
        self.assertEqual(B.charpoly(),Q)

    def test_certified_operator_and_profile_identity(self):
        c,L,B,K=build(self.certificate)
        residual=arb_mat(K)*arb_mat(B)-arb_mat(B).transpose()*arb_mat(K)
        self.assertTrue(all(residual[i,j].contains(0) for i in range(4) for j in range(4)))
        self.assertTrue(fourier_profile(c,L,0).contains(1))
        z=acb('1.2','0.3')
        resolvent=sum((value/(z-2*arb.pi()*n/L) for n,value in zip(range(-2,3),c)),acb(0))
        expected=2*(z*L/2).sin()*resolvent/(L*c[2])
        self.assertTrue((fourier_profile(c,L,z)-expected).contains(0))

    def test_forced_grid_zeros(self):
        c,L,_,_=build(self.certificate)
        for k in (-10,-3,3,10):
            self.assertTrue(fourier_profile(c,L,2*arb.pi()*k/L).contains(0))
        with self.assertRaises(ValueError):
            fourier_profile([arb(1),arb(0),arb(1)],L,0)


if __name__=='__main__':
    unittest.main()
