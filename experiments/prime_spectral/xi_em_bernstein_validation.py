"""Validate the Lean-proved B12 constant in the existing external Xi evaluator.

The Bernoulli bound is proved in Lean. The zeta/EM identity, complex Stirling
identity/error and numerical evaluation remain external in this experiment.
No Lean hard tile or zero-free rectangle is asserted.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import statistics
import time

from flint import acb_series, arb, ctx
import xi_evaluator_comparison as evaluator


def bernstein_zeta_error(terms):
    sigma = arb("-1/2")
    rising = math.prod(abs(evaluator.CENTRE + j).upper() + 1 for j in range(12))
    constant = arb(6112) / 15015 / math.factorial(12)
    return constant * rising * arb(terms + 1) ** (1 - sigma - 12) / (sigma + 11)


def run(output):
    ctx.prec = 192
    ctx.cap = 17
    truth = evaluator.reference()
    rows = []
    for terms in (10, 12, 16):
        timings = []
        for _ in range(7):
            start = time.monotonic()
            s = acb_series([evaluator.CENTRE, 1])
            zet = evaluator.zeta_em(s, terms, 6)
            gam = evaluator.gamma_stirling(s, 12, 8)
            ze = bernstein_zeta_error(terms)
            ge, _, _ = evaluator.gamma_error(12, 8)
            zet = acb_series([evaluator.ball(zet[j], ze) for j in range(17)])
            gam = acb_series([evaluator.ball(gam[j], ge) for j in range(17)])
            jet = evaluator.prefactor(s) * gam * zet
            timings.append(time.monotonic() - start)
        row = evaluator.describe(jet, {
            "terms": terms, "zeta_corrections": 6,
            "bernoulli_bound": "6112/15015", "bernoulli_order": 12,
            "zeta_uniform_error": str(ze.upper()),
            "gamma_uniform_error": str(ge.upper()),
            "seconds": statistics.median(timings), "timings_seconds": timings,
        }, truth)
        rows.append(row)
    if not rows[0]["all_17_complex_radii_below_1e_8"]:
        raise RuntimeError("Kernel-proved Bernoulli constant misses the target")
    root = Path(__file__).resolve().parents[2]
    bindings = [Path(__file__).resolve(), Path(evaluator.__file__).resolve(),
                root / "Reinmann/BernoulliBernsteinBounds.lean",
                root / "Reinmann/EulerMaclaurinTail.lean"]
    result = {
        "status": "Lean_B12_constant_external_evaluator_validation",
        "centre": ["1/2", "14"], "jet_degree": 16, "precision_bits": 192,
        "timing_repeats": 7, "timing_statistic": "median", "rows": rows,
        "Lean_B12_whole_interval_bound_proved": True,
        "Lean_EM_periodic_integral_bound_proved": True,
        "Lean_zeta_EM_identity_proved": False,
        "Lean_complex_Stirling_identity_and_error_proved": False,
        "Lean_complete_hard_tile_certified": False,
        "source_sha256": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in bindings},
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    for row in rows:
        print(row["terms"], row["maximum_complex_radius"], row["seconds"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    run(parser.parse_args().output)
