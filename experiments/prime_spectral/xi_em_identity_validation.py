"""Compare Lean's finiteModel formula with the archived six-correction model.

Arb consistency checks only. The Lean identity concerns the actual zeta
function; this script does not certify Gamma, jet arithmetic, or a hard tile.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

from flint import acb, acb_series, arb, ctx
import xi_evaluator_comparison as archived


def finite_model(s, N):
    value = sum(((-s * arb(n).log()).exp() for n in range(1, N)), acb_series([0]))
    value += ((1-s)*arb(N).log()).exp()/(s-1) + (-s*arb(N).log()).exp()/2
    rising = acb_series([1])
    for k in range(11):
        rising *= s+k
        value += arb.bernoulli(k+2)/math.factorial(k+2)*rising*((-s-k-1)*arb(N).log()).exp()
    return value


def run(output):
    ctx.prec = 192
    ctx.cap = 17
    rows = []
    for centre in (archived.CENTRE, acb(2, 1), acb(arb("-1/2"), 14),
                   acb(arb("1/2"), 13), acb(arb("1/2"), 15)):
        for N in (11, 13, 17):
            s = acb_series([centre, 1])
            model = finite_model(s, N)
            previous = archived.zeta_em(s, N-1, 6)
            assert all(model[j].overlaps(previous[j]) for j in range(17))
            error = (arb(6112)/15015/math.factorial(12) *
                     abs(math.prod((centre+j for j in range(12)), start=acb(1))) *
                     arb(N)**(-centre.real-11)/(centre.real+11))
            assert abs(centre.zeta()-model[0]) < error
            rows.append({"centre": str(centre), "N": N,
                         "all_17_model_coefficients_overlap": True,
                         "centre_error_inside_explicit_bound": True,
                         "centre_error_bound": str(error.upper())})
    root = Path(__file__).resolve().parents[2]
    sources = [Path(__file__).resolve(), Path(archived.__file__).resolve()]
    sources += [root/"Reinmann"/(m+".lean") for m in
                ("EulerMaclaurinFinite", "EulerMaclaurinZeta", "EulerMaclaurinAnalytic")]
    result = {"status": "formal_EM_model_matches_archived_evaluator",
              "precision_bits": 192, "ordinary_jet_degree": 16, "rows": rows,
              "Lean_complete_hard_tile_certified": False,
              "source_sha256": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in sources}}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+"\n")
    print(result["status"], len(rows), "centres/cutoffs; all 17 ordinary coefficients overlap")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    run(parser.parse_args().output)
