#!/usr/bin/env python3
"""Ball-arithmetic re-check of the numerical claims in rh_reduction_paper.tex.

Reads the rigorous FLINT enclosures of mu_0..mu_120 from
research/certified_xi/coefficients_120.json (exact rational endpoints) and
certifies, in Arb ball arithmetic:

  * mu_n > 0 for n = 0..120;
  * strict log-concavity mu_{n+1}^2 > mu_n mu_{n+2} for n = 0..118;
  * every contiguous zero-extended Toeplitz minor
        D_k(m) = det[mu_{m+i-j}]_{i,j<k},  mu_n = 0 for n < 0,
    with 1 <= k <= 16 and m + k - 1 <= 120, is strictly positive.

A claim is certified only when the whole output ball lies in (0, inf).
Trust boundary: FLINT/Arb and the classical identities behind the coefficient
enclosures. This is not a Lean certificate.

Requires python-flint==0.8.0.
"""
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

import flint

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "research" / "certified_xi" / "coefficients_120.json"
KMAX, NMAX, PREC = 16, 120, 8192


def ball(lo, hi):
    lo, hi = Fraction(lo), Fraction(hi)
    mid = (lo + hi) / 2
    rad = (hi - lo) / 2
    m = flint.arb(flint.fmpq(mid.numerator, mid.denominator))
    r = flint.arb(flint.fmpq(rad.numerator, rad.denominator))
    return m + r * flint.arb(0, 1)  # mid +/- rad, enclosing [lo, hi]


def main():
    flint.ctx.prec = PREC
    data = json.loads(SRC.read_text())
    coeffs = sorted(data["coefficients"], key=lambda c: c["n"])
    assert [c["n"] for c in coeffs] == list(range(NMAX + 1))
    mu = [ball(c["lo"], c["hi"]) for c in coeffs]

    def at(n):
        return mu[n] if n >= 0 else flint.arb(0)

    report = {"source": str(SRC.relative_to(ROOT)),
              "source_sha256": hashlib.sha256(SRC.read_bytes()).hexdigest(),
              "python_flint": flint.__version__, "prec_bits": PREC}

    report["positive_mu"] = all(x > 0 for x in mu)
    report["strict_log_concave_0_118"] = all(
        mu[n + 1] ** 2 - mu[n] * mu[n + 2] > 0 for n in range(NMAX - 1))

    failures, count, worst = [], 0, None
    for k in range(1, KMAX + 1):
        for m in range(0, NMAX - k + 2):
            M = flint.arb_mat(k, k, [at(m + i - j) for i in range(k) for j in range(k)])
            d = M.det()
            count += 1
            if not d > 0:
                failures.append((k, m, d.str(5, radius=True)))
            else:
                # relative radius of the certified determinant ball
                rel = d.rad() / abs(d.mid())
                if worst is None or rel > worst[0]:
                    worst = (rel, k, m)
    report["contiguous_minors_checked"] = count
    report["contiguous_minors_uncertified"] = failures
    report["worst_relative_radius"] = (
        {"value": flint.arb(worst[0]).str(3), "k": worst[1], "m": worst[2]}
        if worst else None)
    report["all_certified"] = (report["positive_mu"]
                               and report["strict_log_concave_0_118"]
                               and not failures)
    print(json.dumps(report, indent=2))
    return 0 if report["all_certified"] else 1


if __name__ == "__main__":
    sys.exit(main())
