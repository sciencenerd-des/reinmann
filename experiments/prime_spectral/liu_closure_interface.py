"""Exact printed-margin and principal-local-factor audit; no RH estimate.

Analytic conclusions use standard angular Hecke L-function theory as
spelled out in the note. This code verifies algebra and scalar bounds,
not analytic continuation, Hecke zero existence or target coprimality.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp

Q = sp.Rational


def remainder_certificate():
    beta, B, c0, rho = sp.symbols('beta B c0 rho', real=True)
    gap = beta-B
    # Xu--Sang Section 6.6: gamma=min{Delta,g*,ly/20,h/600,mu}/100,
    # rho=2*gamma, hence rho<=Delta/50.
    printed_vs_half = beta-c0-gap/50-(Q(1, 2)-c0)
    assert sp.expand(printed_vs_half-(B-Q(1, 2)+49*gap/50)) == 0
    assert Q(13, 15)-Q(1, 2) == Q(11, 30)
    # Even hypothetical B=1/2 in the same margin choice does not give an
    # absolute remainder bound below C(1/2), although it saves relative to C(beta).
    assert sp.expand(printed_vs_half.subs(B, Q(1, 2))-49*(beta-Q(1, 2))/50) == 0
    # Not just the proof's conservative gamma choice: Appendix C.4 retains
    # a principal-remainder branch C(beta)-h/600 (with losses suppressed).
    # Source admissibility gives beta>87/100 and h=1-lx+ell<1.
    assert Q(87, 100)-Q(1, 2)-Q(1, 600) == Q(221, 600)
    return dict(printed_rho_upper_bound='(beta_star-B(ell))/50',
                certified_exponent_minus_C_half_lower_bound='B(ell)-1/2+(49/50)*(beta_star-B(ell))',
                lower_bound_with_retained_cap='11/30',
                supplied_majorant_proves_requested_absolute_decay=False,
                actual_remainder_decay_disproved=False,
                optimistic_principal_branch='C_b(beta_star)-h/600',
                optimistic_principal_branch_gap_above_C_half='>221/600 when beta_star>87/100 and h<1',
                relative_remainder_could_suffice=True,
                missing_relative_obligation='Extend the SAME-probe family-uniform relative saving to the needed beta_star>1/2 range, with all contour and row estimates justified; original theorem requires beta_star>B(ell)>87/100.')


def local_correction_certificate():
    q, T, eta, psi, R, Y, V = sp.symbols('q T eta psi R Y V')
    # Independent transcription of OpenAI (old-eq:5.13a), j=0,rho=1.
    Pstar = ((R*(1-1/q)-eta*(q-1)*T*Y*V)/(1-V)-eta*T+Y*R)/(1-R)
    P0 = 1/(1-V)+Y/(1-Y)+Pstar
    Hraw = (1-V)*(1-Y)*P0/(1-eta*T)
    H = sp.cancel(Hraw.subs({Y: 1/q, V: 1/q, R: psi*q**3*T**6}))
    E = 1+(eta*T/q-psi*q**2*T**6)/(1-eta*T)
    factored = (1-q**-2)*E/(1-psi*q**3*T**6)
    assert sp.cancel(H-factored) == 0
    assert sp.cancel(H-(1-q**-2)*(1-(1-1/q)*eta*T-psi*q**2*T**6)
                     /((1-eta*T)*(1-psi*q**3*T**6))) == 0
    # q>=9 and sigma>=1/2: |E-1| <= (q^-3/2+q^-1)/(1-q^-1/2)
    # <= (1/27+1/9)/(1-1/3)=2/9<1. No phase cancellation assumed.
    tail_factor_bound = (Q(1, 27)+Q(1, 9))/(1-Q(1, 3))
    assert tail_factor_bound == Q(2, 9) < 1
    eps = sp.Symbol('eps', positive=True)
    sigma = Q(1, 2)+eps
    assert sp.expand(1+sigma-(Q(3, 2)+eps)) == 0
    assert sp.expand(6*sigma-2-(1+6*eps)) == 0
    # Euler L convergence before continuation: 6*sigma-3>1 iff sigma>2/3.
    assert sp.solve(sp.Eq(6*sp.Symbol('sigma')-3, 1))[0] == Q(2, 3)
    return dict(principal_local_identity_verified=True,
                E_local=str(E),
                H_local='(1-q^-2)*E_local/(1-psi(p)*q^(3-6s))',
                angular_character='psi_eta=conjugate(alpha)^6*eta^6; alpha(a)=a/|a|, alpha^6 generator independent',
                nonzero_angular_degree='-6 (up to embedding convention), since eta has finite order',
                E_local_uniform_defect_bound_for_q_at_least_9='2/9',
                E_normal_convergence_exponents=['3/2+epsilon','1+6*epsilon'],
                global_identity='G_eta(s)=zeta_F^S(2)^(-1)*L_F^S(6s-3,psi_eta)*E_eta(s)',
                initial_identity_region='Re(s)>2/3',
                continuation_region='Re(s)>1/2 using standard Hecke continuation',
                E_product_holomorphic_nonzero_on_half_plane=True,
                analytic_theory_proved_by_code=False)


def shifted_zero_certificate():
    u, s = sp.symbols('u s')
    assert sp.solve(sp.Eq(6*s-3, u), s) == [(u+3)/6]
    assert (Q(1, 2)+3)/6 == Q(7, 12)
    assert (1+3)/Q(6) == Q(2, 3)
    return dict(zero_map='rho -> (rho+3)/6',
                mapped_critical_line='7/12',
                standard_angular_Hecke_zero_theory_used=True,
                interpretation='Nontrivial angular Hecke zeros give correction zeros in Re(s)>1/2; nonvanishing on the whole half-plane is false in this printed correction system.',
                under_angular_GRH='Angular critical-line zeros map to Re(s)=7/12, not 1/2.',
                target_L_zero_or_common_zero_located=False,
                correction_obligation='No cancellation of target reciprocal poles: for example prove no common zeros of L_F^S(s,eta) and L_F^S(6s-3,psi_eta) in Re(s)>1/2, or change/re-normalize the signal with justified remainder.',
                numerical_angular_zero_scan_performed=False)


def certificate():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    return dict(remainder=remainder_certificate(),
                correction=local_correction_certificate(), zeros=shifted_zero_certificate(),
                direct_probe_GRH_implication_proved=False,
                DH_metaplectic_probe_instantiated=False,
                new_arithmetic_estimate_proved=False, RH_claim=False, novelty_claim=False,
                whole_method_family_closed=False)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    text = json.dumps(certificate(), indent=2)+'\n'
    if args.output:
        with args.output.open('x') as f:
            f.write(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
