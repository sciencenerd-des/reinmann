"""External reflection/Beta Gamma majorants with a finite EM zeta enclosure.

Reflection alone gives a product identity. The Beta integral compares to the
half line or line one, where reflection gives an individual Gamma norm. Real
Gamma enclosures and the zeta EM remainder in this script are external to Lean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

from flint import acb, acb_series, arb, ctx
from xi_evaluator_comparison import zeta_em, zeta_error


def gamma_beta(s):
    x, y = s.real / 2, abs(s.imag) / 2
    if x.upper() <= arb("1/2"):
        anchor = arb("1/2")
        anchored = (arb.pi() / (arb.pi()*y).cosh()).sqrt()
    else:
        anchor = arb(1)
        anchored = (arb.pi()*y / (arb.pi()*y).sinh()).sqrt()
    return (x.gamma() / anchor.gamma() * anchored).upper()


def gamma_shift(s):
    w = s / 2
    denominator, bounds = arb(1), []
    for n in range(13):
        bounds.append((w.real+n).gamma().upper()/denominator)
        denominator *= abs(w+n).lower()
    return min(bound.upper() for bound in bounds)


def run(output, arcs):
    ctx.prec, ctx.cap = 192, 1
    start = time.monotonic()
    error = zeta_error(10, 8)
    beta_max, shift_max, zeta_max = arb(0), arb(0), arb(0)
    for k in range(arcs):
        lo, hi = 2*arb.pi()*k/arcs, 2*arb.pi()*(k+1)/arcs
        angle = arb((lo+hi)/2, (hi-lo)/2)
        # Functional equation and conjugation preserve |Xi|; fold to Re>=1/2.
        s = acb(arb("1/2")+abs(angle.cos()), 14+angle.sin())
        zet = abs(zeta_em(acb_series([s]), 10, 8)[0]) + error
        prefactor = abs(s*(s-1)/2) * (-s.real*arb.pi().log()/2).exp()
        beta_bound = prefactor * arb(gamma_beta(s)) * zet
        shift_bound = prefactor * arb(gamma_shift(s)) * zet
        beta_max = arb(max(beta_max.upper(), beta_bound.upper()))
        shift_max = arb(max(shift_max.upper(), shift_bound.upper()))
        zeta_max = arb(max(zeta_max.upper(), zet.upper()))
    result = {"status": "external_reflection_Beta_majorant", "centre": ["1/2", "14"],
              "circle_radius": 1, "arcs": arcs, "bits": ctx.prec,
              "reflection_Beta_Xi_upper": str(beta_max.upper()),
              "shift_product_Xi_upper": str(shift_max.upper()),
              "finite_EM_zeta_upper": str(zeta_max.upper()), "seconds": time.monotonic()-start,
              "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "zeta_source_sha256": hashlib.sha256(Path(__file__).with_name('xi_evaluator_comparison.py').read_bytes()).hexdigest(),
              "Lean_uniform_numeric_majorant_certified": False,
              "scope": "Interval arc cover, reflection and Beta comparison with external real Gamma and EM zeta enclosures. No inference divides by an upper Gamma bound. This is not a Lean strip certificate."}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--arcs', type=int, default=1024)
    a = p.parse_args()
    run(a.output, a.arcs)
