"""Necessary direct-side pricing and a distinct DH reciprocal-Mellin control.

No arithmetic probe estimate, GRH equivalence for J_eta, or DH metaplectic
probe is implemented/proved. The principal reciprocal model is explicitly
different from the arithmetic probe. See the accompanying analytic note.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

import sympy as sp

from liu_exponent_system import direct_components

ROOT = Path(__file__).resolve().parents[2]
Q = sp.Rational
ZERO_SOURCE = Path('research/prime_spectral/verification_2026_10_12_remaining/dh_zero_and_finite_gates.json')


def balanced_price(ell, b):
    """Formal pricing; does not extend validity of the probe beyond its domain."""
    ell, b = F(ell), F(b)
    lx, ly = (1-b-ell)/2, (1+b-ell)/2
    direct = direct_components(lx, ly, ell)
    endpoint = -(1+b)/6
    return dict(ell=str(ell), b=str(b), lx=str(lx), ly=str(ly),
                required_probe_exponent=str(endpoint),
                current_direct_exponent=str(direct['L_low']),
                necessary_saving=str(direct['L_low']-endpoint),
                positive_lengths=lx > 0 and ly > 0,
                support_lengths=lx > ell and ly > ell,
                arithmetic_estimate_proved=False)


def pricing_certificate():
    b, ell, lx, ly, M = sp.symbols('b ell lx ly M', real=True)
    C_half = Q(1, 2)-(4+b)/6
    low = (1-b-ell)/4+b/12
    assert sp.expand(C_half+(1+b)/6) == 0
    assert sp.expand(low-C_half-(Q(5, 12)-ell/4)) == 0
    assert sp.solve(sp.Eq(Q(11, 12)-ell/4, Q(1, 2)), ell) == [Q(5, 3)]
    # Even with no reflection penalty: support requires ell<(1-b)/3.
    # B(ell)=5/6+b/12+((1-b)/3-ell)/4, so it cannot reach 1/2.
    assert sp.expand(Q(11, 12)-ell/4-Q(5, 6)-b/12
                     -((1-b)/3-ell)/4) == 0
    # With only lx>0, ell<1-b, the remaining floor is 2/3+b/4.
    assert sp.expand(Q(11, 12)-ell/4-Q(2, 3)-b/4-(1-b-ell)/4) == 0
    # Free-length signal convention from Liu (22.1).
    free_C_half = -Q(1, 3)+lx/3+ell/6
    assert sp.expand((lx/2+(ly-lx)/12+Q(5, 6)-lx/3-ell/6)-Q(1, 2)
                     -(lx/2+(ly-lx)/12-free_C_half)) == 0
    # A blanket saving s subtracted from the retained direct bound shifts
    # the direct-only optimum from 13/15 to 13/15-s. Necessary only.
    assert Q(13, 15)-Q(1, 2) == Q(11, 30)
    witness = balanced_price(F(1, 5), F(1, 10))
    assert witness['current_direct_exponent'] == '11/60'
    assert witness['required_probe_exponent'] == '-11/60'
    assert witness['necessary_saving'] == '11/30'
    # Removing the b/12 Gram cost alone still leaves lx/2>0, whereas the
    # required target is negative whenever b>0.
    return dict(target_B='1/2', required_balanced_exponent='-(1+b)/6',
                necessary_saving_without_extra_penalties='5/12-ell/4',
                minimum_blanket_saving_with_retained_majorant='11/30',
                formal_length_for_half='5/3',
                length_at_formal_half=dict(lx='-1/3-b/2', ly='-1/3+b/2'),
                reflection_free_support_identity='B(ell)=5/6+b/12+((1-b)/3-ell)/4',
                reflection_free_positive_lx_identity='B(ell)=2/3+b/4+(1-b-ell)/4',
                removing_reflection_or_Gram_penalty_alone_sufficient=False,
                free_signal_target='-1/3+lx/3+ell/6',
                primal_price=witness,
                formal_half_price=balanced_price(F(5, 3), F(1, 10)),
                scope='necessary direct-only conditions; not sufficient for the full comparison')


def dh_reciprocal_coefficients(count=91):
    """Exact polynomial Dirichlet inverse of the actual period-5 DH series."""
    if type(count) is not int or count < 1:
        raise ValueError('positive coefficient count required')
    k = sp.Symbol('k')
    period = [sp.Integer(0), sp.Integer(1), k, -k, sp.Integer(-1)]
    a = [sp.Integer(0)]+[period[n % 5] for n in range(1, count+1)]
    beta = [sp.Integer(0)]*(count+1)
    beta[1] = sp.Integer(1)
    for n in range(2, count+1):
        beta[n] = sp.expand(-sum(a[d]*beta[n//d] for d in sp.divisors(n) if d > 1))
    for n in range(1, count+1):
        assert sp.expand(sum(a[d]*beta[n//d] for d in sp.divisors(n))) == (1 if n == 1 else 0)
    return a, beta


def dh_principal_model_certificate():
    a, beta = dh_reciprocal_coefficients()
    k = sp.Symbol('k')
    assert sp.expand(beta[6]-beta[2]*beta[3]) == -1-k**2
    assert sp.expand(beta[91]-beta[7]*beta[13]) == -1-k**2
    assert beta[4] == 1+k**2
    # |a_n|<=1 for the specified real k in (0,1). On sigma=3,
    # sum_{n>=2}|a_n|/n^3 <= 1/8+integral_2^infinity t^-3 dt = 1/4.
    # Thus the convolution inverse has l1(n^-3) norm at most 4/3.
    assert Q(1, 8)+Q(1, 8) == Q(1, 4)
    assert 1/(1-Q(1, 4)) == Q(4, 3)
    # Gaussian Mellin integral: with t=log(Z/n), center a0=5/6,
    # exp(-t^2/4)+(a0-s)*t integrates to exp((s-a0)^2).
    t, s, a0 = sp.symbols('t s a0')
    assert sp.expand(-t*t/4+(a0-s)*t+(t+2*(s-a0))**2/4-(s-a0)**2) == 0
    prior = json.loads((ROOT/ZERO_SOURCE).read_text())
    zero = prior['off_line_zero']
    assert zero['status'] == 'certified_one_simple_DH_zero_in_disk'
    assert F(zero['rouche_left']['hi']) < F(zero['rouche_right']['lo'])
    assert F(zero['center_real']['lo'])-F(zero['radius']) > F(1, 2)
    return dict(definition='H(s)=5^(-s)*(zeta(s,1/5)+k*zeta(s,2/5)-k*zeta(s,3/5)-zeta(s,4/5))',
                k='(sqrt(10-2*sqrt(5))-2)/(sqrt(5)-1)',
                reciprocal_convolution_checked_through=91,
                beta4=str(beta[4]), beta6=str(beta[6]), beta91=str(beta[91]),
                multiplicativity_defect='-1-k^2',
                reciprocal_l1_weight3_bound='4/3',
                model='f_H(Z)=Z^(5/6-c0)/(2*sqrt(pi))*sum_n beta_n*n^(-5/6)*exp(-log(Z/n)^2/4)',
                Mellin_transform='exp((s-5/6)^2)/H(s)',
                c0='(4+b)/6', correction_multiplier='1',
                universal_model_status='reformulation under stated inversion/reciprocal-growth hypotheses',
                half_plane_growth_DH_analogue='false by retained off-critical zero and the Mellin implication',
                retained_zero_source=str(ZERO_SOURCE),
                retained_zero_source_sha256=hashlib.sha256((ROOT/ZERO_SOURCE).read_bytes()).hexdigest(),
                retained_rouche_rational_inequality_rechecked=True,
                first_or_minimal_zero_claimed=False,
                actual_DH_metaplectic_probe_instantiated=False,
                actual_probe_GRH_equivalence_proved=False)


def combination_obstruction():
    """A linear combination of probes does not have reciprocal DH signal."""
    L1, L2, p = sp.symbols('L1 L2 p')
    q = 1-p
    linear_principal = p/L1+q/L2
    inverse_combination = 1/(p*L1+q*L2)
    difference = p*q*(L1-L2)**2/(L1*L2*(p*L1+q*L2))
    assert sp.cancel(linear_principal-inverse_combination-difference) == 0
    assert difference.subs({p: Q(1, 2), L1: 1, L2: 2}) == Q(1, 12)
    return dict(identity='p/L1+q/L2-1/(p*L1+q*L2)=p*q*(L1-L2)^2/(L1*L2*(p*L1+q*L2)), p+q=1',
                DH_weights='p=(1-i*k)/2, q=(1+i*k)/2; p*q=(1+k^2)/4',
                conclusion='Taking a linear combination of Hecke probes does not instantiate a probe whose principal signal is 1/DH',
                arithmetic_separator_proved=False)


def dh_gaussian_value():
    """One full infinite-model value enclosed by a finite sum plus a tail.

    This instantiates the model; a value at small Z says nothing about its
    large-Z growth. The tail uses the l1(n^-3) inverse bound, not cancellation.
    """
    from flint import arb, ctx

    _, beta = dh_reciprocal_coefficients(91)
    with ctx.workprec(256):
        k = ((10-2*arb(5).sqrt()).sqrt()-2)/(arb(5).sqrt()-1)
        assert 0 < k < 1
        z = arb(1)/100
        a0, c0 = arb(5)/6, arb(41)/60  # b=1/10
        prefactor = ((a0-c0)*z.log()).exp()/(2*arb.pi().sqrt())
        total = arb(0)
        for n in range(1, 92):
            p = sp.Poly(beta[n], sp.Symbol('k'))
            bn = sum((int(p.nth(j))*k**j for j in range(p.degree()+1)), arb(0)) if not p.is_zero else arb(0)
            total += bn*(-a0*arb(n).log()-(z.log()-arb(n).log())**2/4).exp()
        partial = prefactor*total
        u = arb(92).log()
        assert u > z.log()+2*(3-a0)
        tail = prefactor*(arb(4)/3)*((3-a0)*u-(u-z.log())**2/4).exp()
        enclosure = partial+arb(0, tail.upper())
        endpoints = lambda v: {'lo': str(v.lower().fmpq()), 'hi': str(v.upper().fmpq())}
        return dict(Z='1/100', b='1/10', terms=91, bits=256,
                    partial_sum=endpoints(partial), absolute_tail_bound=endpoints(tail),
                    infinite_sum_enclosure=endpoints(enclosure),
                    tail_argument='l1(beta_n*n^-3)<=4/3; Gaussian tail factor decreasing for n>=92',
                    large_Z_growth_tested=False,
                    actual_DH_metaplectic_probe_instantiated=False)


def replay_dh_zero():
    """Reevaluate one retained disk in Arb; no root search and no scan."""
    from flint import acb, acb_series, arb, ctx

    prior = json.loads((ROOT/ZERO_SOURCE).read_text())['off_line_zero']
    with ctx.workprec(768):
        k = ((10-2*arb(5).sqrt()).sqrt()-2)/(arb(5).sqrt()-1)
        assert 0 < k < 1
        x = arb(prior['center_real']['lo']).union(arb(prior['center_real']['hi']))
        y = arb(prior['center_imag']['lo']).union(arb(prior['center_imag']['hi']))
        center, r = acb(x.mid(), y.mid()), arb(prior['radius'])
        rectangle = acb(arb(center.real.mid(), r), arb(center.imag.mid(), r))
        def jet(z):
            old = ctx.cap
            try:
                ctx.cap = 2
                zz = acb_series([z, 1])
                return sum((v*zz.zeta(arb(j)/5) for j, v in
                            [(1, 1), (2, k), (3, -k), (4, -1)]),
                           acb_series([0]))*(-zz*arb(5).log()).exp()
            finally:
                ctx.cap = old
        fc, fbox = jet(center), jet(rectangle)
        derivative = acb(fc[1].real.mid(), fc[1].imag.mid())
        lhs = abs(fc[0])+r*abs(fbox[1]-derivative)
        rhs = r*abs(derivative)
        assert lhs < rhs and center.real-r > arb('1/2')
        assert not fbox[1].contains(0)
        weight = ((rectangle-arb(5)/6)**2).exp()
        assert abs(weight).is_finite() and abs(weight) > 0
        residue_enclosure = weight/fbox[1]
        assert not residue_enclosure.contains(0)
        endpoints = lambda v: {'lo': str(v.lower().fmpq()), 'hi': str(v.upper().fmpq())}
        return dict(status='retained_simple_DH_zero_and_nonzero_Gaussian_pole_replayed',
                    bits=768, radius=prior['radius'],
                    center_real=endpoints(center.real), center_imag=endpoints(center.imag),
                    rouche_left=endpoints(lhs), rouche_right=endpoints(rhs),
                    Gaussian_weight_abs=endpoints(abs(weight)),
                    nonzero_model_pole_residue=True,
                    model_growth_half_plane_analogue=False,
                    actual_DH_metaplectic_probe_instantiated=False,
                    first_or_minimal_zero_claimed=False,
                    trust_boundary='Arb/FLINT Hurwitz zeta derivative enclosures, not Lean')


def certificate():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    return dict(pricing=pricing_certificate(), DH_principal_model=dh_principal_model_certificate(),
                linear_probe_combination=combination_obstruction(),
                actual_probe_status='uninstantiated; no proved discriminator',
                whole_method_family_closed=False, new_arithmetic_estimate_proved=False,
                RH_claim=False, novelty_claim=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--replay-dh-zero', action='store_true')
    args = parser.parse_args()
    data = certificate()
    if args.replay_dh_zero:
        data['DH_zero_replay'] = replay_dh_zero()
        data['DH_Gaussian_value'] = dh_gaussian_value()
    text = json.dumps(data, indent=2)+'\n'
    if args.output:
        with args.output.open('x') as f:
            f.write(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
