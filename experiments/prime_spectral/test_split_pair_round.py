"""Independent finite identities and direct replay for the targeted column."""
from itertools import combinations
import json
from pathlib import Path
import unittest
from flint import acb,arb,arb_mat,arb_series,ctx
from dh_split_pair_column import reciprocal,small_det,column,OLD
from dh_toeplitz_scan import solid_minor
from threshold_ground_gap import box


class SplitPairChecks(unittest.TestCase):
    def test_complement_identity_and_condensation(self):
        with ctx.workprec(2048):
            old=ctx.cap;ctx.cap=60
            try:
                f=arb_series([1,4])*arb_series([1,arb('3/2'),1])*arb_series([1,arb('1/5')])
                mu=[f[j] for j in range(60)]
                h=reciprocal(mu)
                for s in [1,2,3]:
                    result=column(h,s)
                    for r in [3,5,10]:
                        direct=solid_minor([x*arb(100)**j for j,x in enumerate(mu)],r,s)
                        self.assertTrue(direct.overlaps(small_det(h,r,s)))
                        self.assertTrue(result[r].overlaps(direct))
            finally:
                ctx.cap=old

    def test_nonzero_residue_vandermonde_formula(self):
        with ctx.workprec(2048):
            lambdas=[acb(2),acb('4/5')*acb(0,'1/20').exp(),
                     acb('4/5')*acb(0,'-1/20').exp(),acb('2/5')]
            c=[]
            for j,x in enumerate(lambdas):
                value=acb(1)
                for k,y in enumerate(lambdas):
                    if k!=j:value/=1-y/x
                c.append(value)
            for r in [3,20,80]:
                s=2
                h=lambda n:sum((v*x**n for v,x in zip(c,lambdas)),acb(0))
                entries=[[h(r+i-j) for j in range(s)] for i in range(s)]
                self.assertTrue(all(x.imag.contains(0) for row in entries for x in row))
                actual=arb_mat([[x.real for x in row] for row in entries]).det()
                total=acb(0)
                for I in combinations(range(4),s):
                    constant=acb((-1)**(s*(s-1)//2));product=acb(1)
                    for i in I:
                        constant*=c[i]/lambdas[i]**(s-1);product*=lambdas[i]
                    for u,i in enumerate(I):
                        for j in I[:u]:constant*=(lambdas[i]-lambdas[j])**2
                    self.assertFalse(constant.contains(0))
                    total+=constant*product**r
                self.assertTrue(total.imag.contains(0) and total.real.overlaps(actual))

    def test_rank664_boundary_by_direct_determinants(self):
        path=OLD/'dh_rank430-520_shift0-200_32768bits_coefficients.json'
        with ctx.workprec(33024):
            mu=[box(x) for x in json.loads(path.read_text())['coefficients']]
            mu[0]=arb(1);h=reciprocal(mu)
            self.assertTrue(small_det(h,663)>0)
            self.assertTrue(small_det(h,664)<0)
            self.assertTrue(small_det(h,677)<0)


if __name__=='__main__':
    unittest.main()
