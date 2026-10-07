"""Arb bounds for the normalized renewal mass and conditional endpoint traces.

Uses the written Wiener--Hopf formula and a proved whole-tail allowance.
No finite-dimensional eigenvector is treated as an actual Weil eigenfunction.
See TRACE_ENCLOSURES_STATE_CONVERGENCE_2026_10_07.md for analytic obligations.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx

from certified_weil import endpoints


def kappa(log_lambda, cutoff=128):
    """Enclose the ascending Wiener--Hopf factor for B=log(1+xi^2)/2."""
    ell = arb(log_lambda)
    if not ell.is_finite() or type(cutoff) is not int or cutoff < 16:
        raise ValueError('finite log(lambda) and integer cutoff >=16 required')

    def integrand(z, analytic):
        t = ell+z
        if t.real < -1:
            # log(1+w)/w = 2F1(1,1;2;-w): avoid loss of exp(2t) in 1+w.
            w = (2*t).exp()
            log_psi = 2*t-acb(2).log()+(-w).hypgeom_2f1(1, 1, 2).log(analytic=analytic)
        elif t.real > 1:
            log_psi = (t+(((-2*t).exp()+1).log(analytic=analytic)/2)).log(analytic=analytic)
        else:
            log_psi = ((((2*t).exp()+1).log(analytic=analytic)/2)).log(analytic=analytic)
        return log_psi/(2*acb.pi()*z.cosh())

    tol = arb(2)**-120
    value = sum((acb.integral(integrand, j, j+2, abs_tol=tol,
                              rel_tol=tol, eval_limit=100000)
                 for j in range(-cutoff, cutoff, 2)), acb(0))
    # |log(log(1+exp(2t))/2)| <= 2|t|+2, and sech z <= 2 exp(-|z|).
    tail = 4/arb.pi() * (abs(ell)+cutoff+2) * (-arb(cutoff)).exp()
    if (not value.is_finite() or not value.imag.contains(0)
            or not value.real.rad() < arb('1e-25')):
        raise ArithmeticError('Wiener--Hopf quadrature unresolved')
    return (value.real+arb(0, tail.upper())).exp()


def renewal_mass(distance, upper_h=('1/50', '1/20', '1/10', '1/4', '1/2', '1', '2'),
                 lower_h=('4', '8', '16', '32')):
    """Concavity and Laplace--Stieltjes bounds; not necessarily tight at fixed d."""
    d = arb(distance)
    if not d > 0 or not d.is_finite():
        raise ValueError('positive finite distance required')
    cache = {}

    def reciprocal(h):
        key = str(h)
        if key not in cache:
            h = arb(h)
            if not h > 0:
                raise ValueError('positive Laplace parameter required')
            cache[key] = 1/kappa((h/d).log())
        return cache[key]

    # Concavity: J(1/d) <= V(d) <= h J(h/d)/(1-exp(-h)).
    uppers = [arb(h)/(1-(-arb(h)).exp())*reciprocal(h) for h in upper_h]
    lowers = [reciprocal('1'), *[reciprocal(h)-(-arb(h)/2).exp()*reciprocal(arb(h)/2)
              for h in lower_h]]
    if not uppers or not lowers:
        raise ValueError('nonempty upper and lower parameter grids required')
    lo = max([arb(0), *(v.lower() for v in lowers)])
    hi = min(v.upper() for v in uppers)
    if not hi > lo or not lo > 0:
        raise ArithmeticError('positive renewal interval unresolved')
    return lo, hi


def conditional_trace(profile_lo, profile_hi, forcing_bound, mass_lo, mass_hi):
    """Trace interval from certified actual u(d) and localized ||F||_infinity.

    The input status is external: supplying trial-profile values does not
    certify an eigenfunction trace. Handles profiles of either sign.
    """
    p, q, m, v, w = map(arb, (profile_lo, profile_hi, forcing_bound, mass_lo, mass_hi))
    if not q >= p or not m >= 0 or not v > 0 or not w >= v:
        raise ValueError('ordered profile/mass bounds and nonnegative forcing required')
    quotients = [p/v, p/w, q/v, q/w]
    error = 2*m*w
    return (min(z.lower() for z in quotients)-error).lower(), (
        max(z.upper() for z in quotients)+error).upper()


def generate():
    rows = []
    with ctx.workprec(192):
        for label, d in [('1', arb(1)), ('exp(-8)', (-arb(8)).exp()),
                         ('exp(-32)', (-arb(32)).exp()),
                         ('exp(-128)', (-arb(128)).exp())]:
            lo, hi = renewal_mass(d)
            rows.append({'distance_label': label, 'distance': endpoints(d),
                         'renewal_mass': {'lo': str(lo.fmpq()), 'hi': str(hi.fmpq())},
                         'density_upper': str((hi/d).upper().fmpq())})
            print('renewal mass enclosed at', label, flush=True)
        # Explicit uniform constants on 2/3 <= L <= 6/5, including q=2 and q=3.
        length_lo, length_hi = arb(2)/3, arb(6)/5
        c = (2*arb.pi()).log()
        k_star = arb(5)/4+2*(length_hi/2).cosh()
        k_norm = length_hi*k_star
        prime_norm = 2*(arb(2).log()/arb(2).sqrt()+arb(3).log()/arb(3).sqrt())
        ground_upper = 1+(-length_lo).exp()/length_lo-c+k_norm
        heat_candidates = []
        for time in ('51/100', '13/25', '21/40', '53/100', '11/20', '3/5', '3/4', '1'):
            t = arb(time)
            C_t = ((t-arb(1)/2).gamma()/(2*arb.pi().sqrt()*t.gamma())).sqrt()
            bound = ((ground_upper+c+prime_norm+k_norm)*t).exp() * (
                C_t+t*length_hi.sqrt()*k_star)
            heat_candidates.append((time,bound))
        heat_time,state_bound = min(heat_candidates,key=lambda item:item[1].upper())
        # |lambda+c| <= max(k_norm+prime_norm, ground_upper+c).
        forcing_bound = (max((k_norm+prime_norm).upper(),
                             (ground_upper+c).upper())+k_norm+prime_norm+8)*state_bound
        forcing_l1 = arb(5)/4*forcing_bound+state_bound/(8*arb(1).exp())
        mass1_hi = arb(rows[0]['renewal_mass']['hi'])
        trace_bound = mass1_hi*(forcing_bound+forcing_l1)
        constants = {name: endpoints(value) for name, value in [
            ('length_lower', length_lo), ('length_upper', length_hi),
            ('K_operator_bound', k_norm), ('S_operator_bound', prime_norm),
            ('ground_eigenvalue_upper', ground_upper), ('unit_state_Linfty_bound', state_bound),
            ('cutoff_forcing_Linfty_bound', forcing_bound),
            ('cutoff_forcing_L1_bound', forcing_l1), ('absolute_endpoint_trace_bound', trace_bound)]}
        return {'status': 'renewal_mass_and_explicit_uniform_bounds_enclosed',
                'bits': 192, 'log_coordinate_cutoff': 128, 'rows': rows,
                'uniform_constants': constants, 'selected_heat_time': heat_time,
                'scope': 'Arb plus written analytic inputs. Coarse universal trace bound, not a computed minimizing-state trace, spectral gap certificate, new positive window, or Lean proof of the operator theorem.',
                'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = generate()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
