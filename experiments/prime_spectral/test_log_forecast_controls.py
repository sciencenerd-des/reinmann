"""Independent normalization checks for the new plain-L control."""
from flint import acb,arb,ctx,dirichlet_char
from plain_l13_decay import prime_coefficients
from plain_quadratic_l13_decay import matrices
from certified_weil import arch_regularized,correlation_ball


def test_complex_euler_coefficients_against_dirichlet_recurrence():
    with ctx.workprec(768):
        chi=dirichlet_char(13,2);a=[acb(0)]+[chi(n) for n in range(1,66)];c=[acb(0) for _ in a]
        for n in range(2,len(a)):
            c[n]=a[n]*arb(n).log()-sum((c[d]*a[n//d] for d in range(2,n) if n%d==0),acb(0))
        expected=prime_coefficients(65)
        assert all(c[n].real.overlaps(expected[n]) for n in range(len(a)))
        assert expected[6].is_zero() and not expected[2].contains(0)


def test_even_gamma_single_character_against_integral():
    with ctx.workprec(768):
        E,O,_=matrices(16,4,768);chi=dirichlet_char(13,12)
        a=[arb(0)]+[chi(n).real for n in range(1,17)];c=[arb(0) for _ in a]
        for n in range(2,len(a)):
            c[n]=a[n]*arb(n).log()-sum((c[d]*a[n//d] for d in range(2,n) if n%d==0),arb(0))
        length=arb(16).log()
        def direct(m,n):
            v=acb.integral(lambda z,_:-arch_regularized(m,n,z,length),0,length,rel_tol=arb(2)**-360,abs_tol=arb(2)**-360,eval_limit=400000)
            if m==n:v+=(arb(13).log()-(4*arb.pi()).log()-arb.const_euler()-(length/2).tanh().log())
            for j in range(2,16):v-=c[j]/arb(j).sqrt()*correlation_ball(m,n,acb(arb(j).log()),length)
            assert v.imag.contains(0);return v.real
        assert E[0][0].overlaps(direct(0,0))
        assert E[0][3].overlaps(arb(2).sqrt()*direct(3,0))
        assert E[3][3].overlaps(direct(3,3)+direct(3,-3))
        assert O[2][2].overlaps(direct(3,3)-direct(3,-3))


if __name__=='__main__':
    test_complex_euler_coefficients_against_dirichlet_recurrence();print('PASS Euler coefficients vs complex Dirichlet recurrence',flush=True)
    test_even_gamma_single_character_against_integral();print('PASS even-gamma single-L entries vs independent integral',flush=True)
