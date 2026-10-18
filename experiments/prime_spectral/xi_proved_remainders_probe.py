"""Arb hard-tile probe using only the new Lean-proved analytic jet errors.

Finite exp/log and series arithmetic remain external. Builtin Gamma/zeta are
independent references only; no native computation is imported into Lean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import statistics
import time

from flint import acb_series, arb, ctx
import xi_evaluator_comparison as previous


def run(output):
    ctx.prec = 192
    ctx.cap = 17
    truth = previous.reference()
    timings = []
    for _ in range(7):
        start = time.monotonic()
        s = acb_series([previous.CENTRE, 1])
        # N=21, B2..B12; six nonzero Bernoulli corrections in both models.
        zet = previous.zeta_em(s, 20, 6)
        gam = previous.gamma_stirling(s, 12, 7)
        zet = acb_series([previous.ball(zet[j], arb("1e-7")) for j in range(17)])
        gam = acb_series([previous.ball(gam[j], arb("4e-14")) for j in range(17)])
        jet = previous.prefactor(s) * gam * zet
        radius = arb("1/16")
        derivative = sum((j*abs(jet[j])*radius**(j-1) for j in range(1, 17)), arb(0))
        derivative += 1000*radius**16*(17-16*radius)/(1-radius)**2
        margin = abs(jet[0]).lower()-derivative.upper()*radius
        timings.append(time.monotonic()-start)
    row = previous.describe(jet, {"seconds": statistics.median(timings),
                                  "timings_seconds": timings}, truth)
    assert row["all_17_complex_radii_below_1e_8"] and margin > 0
    root = Path(__file__).resolve().parents[2]
    sources = [Path(__file__).resolve(), Path(previous.__file__).resolve()]
    sources += [root/"Reinmann"/(m+".lean") for m in
                ("StirlingAnalytic", "StirlingGamma", "ZetaJetRemainder", "XiLocalCauchy")]
    result = {
        "status": "external_hard_tile_with_Lean_proved_analytic_jet_errors",
        "centre": ["1/2", "14"], "jet_degree": 16, "precision_bits": 192,
        "zeta_terms": 20, "zeta_N": 21, "zeta_corrections": 6,
        "gamma_shift": 12, "gamma_retained_corrections": 6,
        "zeta_each_ordinary_coefficient_error": "1e-7",
        "zeta_error_theorem": "Reinmann.ZetaJetRemainder.zeta_coefficient_error_le",
        "Gamma_each_ordinary_coefficient_error": "4e-14",
        "Gamma_error_theorem": "Reinmann.StirlingAnalytic.gamma_coefficient_error_le",
        "unit_disk_radius": 1, "tile_radius": "1/16", "Xi_majorant": 1000,
        "row": row, "centre_modulus_lower": str(abs(jet[0]).lower()),
        "derivative_upper": str(derivative.upper()), "tile_margin_lower": str(margin.lower()),
        "Lean_finite_exp_log_jet_arithmetic_certified": False,
        "Lean_complete_hard_tile_certified": False,
        "Lean_complete_hard_tile_seconds": None,
        "source_sha256": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sources},
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+"\n")
    print(result["status"], row["maximum_complex_radius"], result["tile_margin_lower"], row["seconds"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    run(parser.parse_args().output)
