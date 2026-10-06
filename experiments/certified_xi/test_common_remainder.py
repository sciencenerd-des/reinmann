import math
import unittest
from flint import arb,acb,ctx
from laboratory import interval
from common_remainder import derivative_bound,anchored_moments,certify_anchor,scaled_derivative_bound
from decaying_theta import saddle_theta_bound
from high_order_saddle import model_moments,stirling_row


class CommonRemainderTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=512

    def test_uniform_derivative_bounds_and_domains(self):
        with self.assertRaises(ValueError):
            derivative_bound(999999)
        with self.assertRaises(ValueError):
            anchored_moments(10**6,2)
        previous=None
        for X in (10**6,10**8,10**12):
            row=derivative_bound(X)
            self.assertTrue(0<arb(row['relative_complex_error_upper'])<1)
            self.assertTrue(arb(row['disk_radius_lower'])>1)
            if previous:
                for a,b in zip(previous['derivatives'],row['derivatives']):
                    self.assertTrue(arb(b['absolute_upper'])<arb(a['absolute_upper']))
            previous=row

    def test_decaying_theta_bounds(self):
        bound=saddle_theta_bound(10**6)
        stronger=saddle_theta_bound(10**8)
        self.assertTrue(arb(stronger['saddle_region_relative_upper'])<arb(bound['saddle_region_relative_upper']))
        with self.assertRaises(ValueError):
            saddle_theta_bound(10**6,order=True)
        x=arb(10**6)
        u=(2*x/arb.pi()).lambertw()/2
        A=2*x*(1+2*u)-arb(9)*u/2
        left=u*(-(32*u).sqrt()/A.sqrt()).exp()
        for v,high_region in ((arb(0),False),(arb(1),False),(left,True)):
            E=(2*v).exp()
            partial=sum((arb(j)**2*(2*arb.pi()*j*j*E-3)/(2*arb.pi()*E-3)*
                         (-arb.pi()*(j*j-1)*E).exp() for j in range(2,9)),arb(0))
            self.assertTrue(partial<arb(bound['global_relative_upper']))
            if high_region:
                self.assertTrue(partial<arb(bound['saddle_region_relative_upper']))

    def test_power_law_envelope_dominates_recomputed_bounds(self):
        with self.assertRaises(ValueError):
            scaled_derivative_bound(10**6,999999)
        for a in (2*10**6,10**8,10**12):
            envelope=scaled_derivative_bound(10**6,a)
            direct=derivative_bound(a)
            for outer,inner in zip(envelope['derivatives'],direct['derivatives']):
                self.assertTrue(arb(inner['absolute_upper'])<arb(outer['absolute_upper']))

    def test_centering_matches_original_model(self):
        a=arb(10**6)
        raw,errors=model_moments(a)
        centered=anchored_moments(a,0)
        c=((2*a/arb.pi()).lambertw()/2).log()
        mu=raw[1]/raw[0]
        second=raw[2]/raw[0]
        # Account for the original model's separately returned quadrature error.
        first_error=abs(mu)*(errors[1]+errors[0])/(1-errors[0])
        second_error=abs(second)*(errors[2]+errors[0])/(1-errors[0])
        first=mu-2*c+arb(0,first_error.upper())
        square=second-4*c*mu+4*c*c+arb(0,(second_error+4*abs(c)*first_error).upper())
        self.assertTrue(first.overlaps(centered[1]/centered[0]))
        self.assertTrue(square.overlaps(centered[2]/centered[0]))

    def test_complex_tilt_against_independent_exact_phase(self):
        a=arb(10**6)
        bound=derivative_bound(10**6)
        u=(2*a/arb.pi()).lambertw()/2
        A=2*a*(1+2*u)-arb(9)*u/2
        L=(32*u).sqrt()
        rho=A.sqrt()/(8*L)
        delta=acb(rho/2,rho/2)
        coefficients=[arb(0),(1+arb(9)*u/2)/A.sqrt()]
        for j in range(2,17):
            T=sum((arb(v)*(2*u)**k for k,v in enumerate(stirling_row(j))),arb(0))
            coefficients.append((arb(9)*u/2-a/u*T)/(math.factorial(j)*A**(arb(j)/2)))
        def integrand(s,_analytic,exact):
            d=s/A.sqrt()
            amplitude=1-3/(2*arb.pi())*(-2*u*d.exp()).exp()
            if exact:
                shifted=d.expm1()
                p=(2*a+1)*d+arb(9)*u/2*shifted-a/u*(2*u*shifted).expm1()
            else:
                p=acb(0)
                for v in reversed(coefficients):
                    p=p*s+v
            return (p+2*delta*d).exp()*amplitude
        direct=acb.integral(lambda s,k:integrand(s,k,True),-L,L,
                            rel_tol=arb(2)**-180,abs_tol=arb(2)**-200)
        model=acb.integral(lambda s,k:integrand(s,k,False),-L,L,
                           rel_tol=arb(2)**-180,abs_tol=arb(2)**-200)
        self.assertTrue(direct.is_finite() and model.is_finite())
        self.assertTrue(model.real>0)
        self.assertTrue(abs(direct/model-1)<arb(bound['relative_complex_error_upper']))

    def test_joint_transfer_resolves_formerly_inconclusive_anchor(self):
        result=certify_anchor(10**6+1)
        self.assertEqual(result['status'],'certified_negative_curvature_at_anchor')
        self.assertTrue(interval(result['transfer']['curvature_enclosure'])<0)
        self.assertTrue(arb(result['transfer']['curvature_error_upper'])<arb('1e-19'))


if __name__=='__main__':
    unittest.main()
