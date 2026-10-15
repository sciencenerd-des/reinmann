#!/usr/bin/env python3
"""Plot the reduction paper from exact coefficient endpoints.

The midpoint plots illustrate the data; Arb checks every included determinant
sign before plotting. Run with python-flint==0.8.0 and matplotlib.
"""
import json
import math
from fractions import Fraction
from pathlib import Path

import flint
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from certify_reduction_minors import ball, SRC, PREC, NMAX, KMAX


def main():
    flint.ctx.prec = PREC
    records = sorted(json.loads(SRC.read_text())["coefficients"], key=lambda c: c["n"])
    assert [c["n"] for c in records] == list(range(NMAX + 1))
    mu = [ball(c["lo"], c["hi"]) for c in records]
    assert all(x > 0 for x in mu)
    mid = [(Fraction(c["lo"]) + Fraction(c["hi"])) / 2 for c in records]
    out = Path(__file__).resolve().parent / "figures"
    out.mkdir(exist_ok=True)
    plt.rcParams.update({"font.size": 10, "axes.spines.top": False,
                         "axes.spines.right": False, "savefig.dpi": 180})

    fig, ax = plt.subplots(figsize=(9, 3.5))
    logs = [math.log10(x.numerator) - math.log10(x.denominator) for x in mid]
    ax.plot(range(NMAX + 1), logs, color="#2455a4", linewidth=1.7)
    ax.set(xlabel="Coefficient index n", ylabel=r"$\log_{10}\mu_n$",
           title="Positive ordinary Taylor coefficients, n = 0,...,120")
    ax.grid(alpha=.2)
    fig.tight_layout()
    fig.savefig(out / "rh_reduction_coefficients.png")
    plt.close(fig)

    ns = list(range(NMAX - 1))
    ratios = [mid[n + 1] ** 2 / (mid[n] * mid[n + 2]) for n in ns]
    slack = [Fraction((2*n+3)*(2*n+4), (2*n+1)*(2*n+2)) for n in ns]
    fig, axes = plt.subplots(1, 2, figsize=(11, 3.8))
    axes[0].plot(ns, [float(x) for x in ratios], label=r"$R_n$", color="#2455a4")
    axes[0].plot(ns, [(n+2)/(n+1) for n in ns], "--", color="#b34b33",
                 label=r"Classical Jensen: $(n+2)/(n+1)$")
    axes[0].axhline(1, color="#666666", linestyle=":", label="Log-concavity: 1")
    axes[0].set(xlabel="Index n", ylabel="Coefficient ratio", title="Ordinary coefficients")
    axes[1].plot(ns, [float(r/s) for r, s in zip(ratios, slack)],
                 label=r"$H_n=R_n/s_n$", color="#2455a4")
    axes[1].plot(ns, [float(1/s) for s in slack], ":", color="#666666",
                 label=r"Log-concavity: $1/s_n$")
    axes[1].plot(ns, [float(Fraction(int(n+2), int(n+1))/s) for n, s in zip(ns, slack)],
                 "--", color="#b34b33", label=r"Classical Jensen: $(n+2)/((n+1)s_n)$")
    axes[1].axhline(1, color="#40805b", linestyle="-.", label="Moment convexity: 1")
    axes[1].set(xlabel="Index n", ylabel="Moment ratio", title="Unweighted kernel moments")
    for ax in axes:
        ax.grid(alpha=.2)
        ax.legend(fontsize=8, loc="best")
    fig.tight_layout()
    fig.savefig(out / "rh_reduction_ratios.png")
    plt.close(fig)

    grid = np.full((KMAX, NMAX + 1), np.nan)
    normalized = grid.copy()
    count = 0
    log10 = flint.arb(10).log()
    for k in range(1, KMAX + 1):
        for m in range(NMAX - k + 2):
            matrix = flint.arb_mat(k, k, [mu[m+i-j] if m+i-j >= 0 else 0
                                         for i in range(k) for j in range(k)])
            det = matrix.det()
            if not det > 0:
                raise ArithmeticError(f"Uncertified determinant k={k}, m={m}")
            value = float(det.mid().log() / log10)
            grid[k-1, m] = value
            normalized[k-1, m] = value - k * logs[m]
            count += 1
    assert count == 1816
    fig, axes = plt.subplots(1, 2, figsize=(11, 4))
    for ax, data, title in zip(axes, [grid, normalized],
                              [r"$\log_{10}D_k(m)$", r"$\log_{10}(D_k(m)/\mu_m^k)$"]):
        plot = ax.imshow(data, origin="lower", aspect="auto", interpolation="nearest",
                         extent=[-.5, NMAX+.5, .5, KMAX+.5], cmap="viridis")
        ax.set(xlabel="Offset m", ylabel="Order k", title=title)
        fig.colorbar(plot, ax=ax, shrink=.85)
    fig.tight_layout()
    fig.savefig(out / "rh_reduction_minors.png")
    plt.close(fig)
    print(f"Wrote three figures to {out}; all {count} determinant balls positive.")


if __name__ == "__main__":
    main()
