#!/usr/bin/env python3
"""Lowest eigenvalue of the finite Weil matrix A_N(C) on [C^-1/2, C^1/2].

DIAGNOSTIC ONLY, not a certificate. Entries are Arb balls from
`closed_weil.entry_closed`; the eigenvalues come from Arb's approximate
eigensolver applied to the ball midpoints. The output decides feasibility:
it measures the margin that a rigorous infinite-rank positivity proof
would have to beat on each window.

For a fixed window, the finite-rank minima decrease to the infimum of the
form as N grows. The script records them for several N, so saturation is
visible.

Usage: python window_lowest_eigenvalue_probe.py OUT.json
Requires python-flint==0.8.0.
"""
from __future__ import annotations

import json
import sys
import time

from flint import acb_mat, arb, ctx

from closed_weil import entry_closed
from weil_matrix import prime_powers

WINDOWS = ("1.9", "2.2", "2.5", "3.2", "4.5", "6.5", "9.5", "17.5")
RANKS = (8, 16, 32, 48)
PREC = 900


def lowest(C: str, N: int) -> tuple[str, str]:
    length = arb(C).log()
    c = float(C)
    powers = [(p, q) for p, q in prime_powers(int(c)) if p < c]
    idx = list(range(-N, N + 1))
    d = 2 * N + 1
    rows = [[None] * d for _ in range(d)]
    for a in range(d):
        for b in range(a, d):
            rows[a][b] = rows[b][a] = entry_closed(
                idx[a], idx[b], length, powers, terms=60).mid()
    ev = sorted(e.real.mid() for e in acb_mat(rows).eig(algorithm="approx"))
    return ev[0].str(6), ev[1].str(6)


def main() -> None:
    ctx.prec = PREC
    out = {"status": "floating_diagnostic_not_certificate", "prec_bits": PREC,
           "windows": {}}
    for C in WINDOWS:
        primes = sorted({q for p, q in prime_powers(int(float(C))) if p < float(C)})
        rec = {"primes": primes, "ranks": {}}
        for N in RANKS:
            t = time.time()
            l0, l1 = lowest(C, N)
            rec["ranks"][N] = {"lambda_min": l0, "lambda_2": l1,
                               "seconds": round(time.time() - t, 1)}
            print(C, N, l0, l1, flush=True)
        out["windows"][C] = rec
    json.dump(out, open(sys.argv[1], "w"), indent=1)


if __name__ == "__main__":
    main()
