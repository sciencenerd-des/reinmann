#!/usr/bin/env python3
"""Figures added in the October 2026 manuscript revision.

Each figure is drawn from data already in the repository: certified Xi
coefficients, the Weil eigenfamily certificate, and the Davenport-Heilbronn
atlas and attribution records. They are illustrations; none of them is a
certificate.

    python3 paper/generate_revision_figures.py [name ...]

Names: lambda0, hef, weil, fekete, dh. The DH figures read the controls
records from the worktree given by $DH_ROOT (default: this repository).
Requires matplotlib, numpy and mpmath.
"""
from __future__ import annotations

import ast
import json
import math
import os
import sys
from fractions import Fraction
from pathlib import Path

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from matplotlib.patches import Circle, Rectangle

sys.path.insert(0, str(Path(__file__).resolve().parent))
import generate_paper_figures as gp  # shared palette, rcParams and save()

BLUE, RED, GREEN, AMBER, GREY, PURPLE = gp.BLUE, gp.RED, gp.GREEN, gp.AMBER, gp.GREY, gp.PURPLE
ROOT = gp.ROOT
DH_ROOT = Path(os.environ.get("DH_ROOT", ROOT))


def frac_mid(ball):
    return (Fraction(ball["lo"]) + Fraction(ball["hi"])) / 2


# ------------------------------------------------- reduction: Lambda_0 trap
def lambda0_figure():
    mp.mp.dps = 30

    def Xi(t):
        s = mp.mpf(1) / 2 + 1j * t
        return mp.re(s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s))

    ts = np.linspace(0, 40, 1601)
    xi = np.array([float(Xi(t)) for t in ts])
    xi0 = float(Xi(0))
    zeros = [float(mp.im(mp.zetazero(k))) for k in range(1, 7)]
    fig, axes = plt.subplots(1, 2, figsize=(7.2, 2.8))
    ax = axes[0]
    ax.plot(ts, xi, color=BLUE, lw=1.2, label=r"$\Xi(t)=\xi(\frac{1}{2}+it)$")
    ax.axhline(0.5, color=RED, lw=1.0, ls="--", label=r"level $\frac{1}{2}$ (never reached)")
    ax.plot(zeros, [0] * len(zeros), "o", color="black", ms=3, label="zeta zeros")
    ax.set(xlabel="$t$", ylabel=r"$\Xi(t)$", title=r"(a) $|\Xi(t)|\leq\xi(\frac{1}{2})<\frac{1}{2}$")
    ax.legend(loc="center right", bbox_to_anchor=(1.0, 0.30), fontsize=6.6)
    ins = ax.inset_axes([0.47, 0.58, 0.33, 0.30])
    tz = np.linspace(0, 1.2, 121)
    ins.plot(tz, [float(Xi(t)) for t in tz], color=BLUE, lw=1.0)
    ins.axhline(0.5, color=RED, lw=0.9, ls="--")
    ins.set_ylim(0.488, 0.5015)
    ins.set_xlim(0, 1.2)
    ins.tick_params(labelsize=5.5)
    ins.annotate("", xy=(0.08, 0.5), xytext=(0.08, xi0),
                 arrowprops=dict(arrowstyle="<->", color=GREEN, lw=0.8))
    ins.text(0.14, 0.4985, r"gap $0.0029$", fontsize=5.8, color=GREEN)
    ax = axes[1]
    lam0 = (1 - 2 * xi) / (ts ** 2 + 0.25)
    ax.semilogy(ts, lam0, color=BLUE, lw=1.2, label=r"$\Lambda_0(\frac{1}{2}+it)$")
    ax.semilogy(ts, (1 - 2 * xi0) / (ts ** 2 + 0.25), color=GREY, lw=0.9, ls="--",
                label=r"$(1-2\xi(\frac{1}{2}))/(t^2+\frac{1}{4})$")
    ax.semilogy(zeros, [1 / (z ** 2 + 0.25) for z in zeros], "o", color="black", ms=3,
                label=r"value $1/(t^2+\frac{1}{4})$ at zeros")
    ax.set(xlabel="$t$", ylabel=r"$\Lambda_0(\frac{1}{2}+it)$ (log)", title=r"(b) $\Lambda_0>0$ on the whole line")
    ax.legend(loc="upper right", fontsize=6.4)
    fig.tight_layout()
    gp.save(fig, "rh_reduction_lambda0")
    return {"xi_half": xi0, "min_one_minus_two_xi": float((1 - 2 * xi).min())}


# ------------------------------------------------------- HEF: Turan transport
def hef_figure():
    mu = gp.load_mu(200)  # Xi normalization; Turan ratios are scale invariant
    N = len(mu)
    gam = [mp.factorial(n) * mu[n] for n in range(N)]
    dbar = [float(gam[n + 1] ** 2 / (gam[n] * gam[n + 2]) - 1) for n in range(N - 2)]
    M = [mu[n] * mp.factorial(2 * n) for n in range(N)]
    raw = [float((M[n + 1] ** 2 - M[n] * M[n + 2]) / (M[n] * M[n + 2])) for n in range(N - 2)]
    rho = [M[n + 1] / M[n] / 4 for n in range(N - 1)]  # de Bruijn normalization H_0(z)=Xi(z/2)/8
    d2 = [float(rho[n + 2] - 2 * rho[n + 1] + rho[n]) for n in range(N - 3)]

    mp.mp.dps = 30

    def Phi(u):
        return mp.fsum((2 * mp.pi ** 2 * k ** 4 * mp.exp(9 * u) - 3 * mp.pi * k ** 2 * mp.exp(5 * u))
                       * mp.exp(-mp.pi * k ** 2 * mp.exp(4 * u)) for k in range(1, 12))

    def turan(t, nmax=9):
        Ms = [mp.quad(lambda u: Phi(u) * mp.exp(t * u * u) * u ** (2 * m), [0, 0.25, 0.5, 1, 2, 3])
              for m in range(nmax + 3)]
        g = [mp.factorial(m) * Ms[m] / mp.factorial(2 * m) for m in range(nmax + 3)]
        return [float(g[n + 1] ** 2 / (g[n] * g[n + 2]) - 1) for n in range(nmax + 1)]

    tgrid = np.linspace(-0.4, 0.4, 17)
    flow = np.array([turan(float(t)) for t in tgrid])

    fig, axes = plt.subplots(1, 3, figsize=(7.4, 2.6))
    ns = np.arange(N - 2)
    ax = axes[0]
    ax.loglog(ns[1:] + 1, dbar[1:], color=BLUE, lw=1.2, label=r"$\bar\Delta(n,0)$, $\gamma_n=n!\mu_n$")
    ax.loglog(ns[1:] + 1, [-x for x in raw[1:]], color=RED, lw=1.0, ls="--",
              label=r"$-\bar\Delta_{\rm raw}(n,0)$, raw moments")
    ax.set(xlabel="$n+1$", ylabel="magnitude", title="(a) correct sign vs. raw moments")
    ax.legend(fontsize=6.0, loc="lower left")
    ax = axes[1]
    for n, col in ((0, BLUE), (2, GREEN), (5, AMBER), (9, PURPLE)):
        ax.plot(tgrid, flow[:, n], color=col, lw=1.1, label=f"$n={n}$")
    ax.axvline(0, color=GREY, lw=0.6, ls=":")
    ax.set(xlabel="heat-flow time $t$", ylabel=r"$\bar\Delta(n,t)$", title=r"(b) $\bar\Delta(n,t)$ increases in $t$")
    ax.legend(fontsize=6.2, loc="center right", bbox_to_anchor=(1.0, 0.62))
    ax = axes[2]
    ax.loglog(np.arange(len(d2)) + 1, [-x for x in d2], color=GREEN, lw=1.2)
    ax.set(xlabel="$n+1$", ylabel=r"$-\Delta^2\rho_n(0)$", title=r"(c) $\Delta^2\rho_n(0)<0$, $n\leq196$")
    fig.tight_layout()
    gp.save(fig, "hef_turan_transport")
    return {"dbar_min": min(dbar), "dbar_all_positive": all(x > 0 for x in dbar),
            "raw_all_negative": all(x < 0 for x in raw), "d2rho_all_negative": all(x < 0 for x in d2),
            "n_dbar_at_197": 197 * dbar[197]}


# ------------------------------------------------------------- Weil figures
def weil_figures():
    src = ROOT / "research" / "prime_spectral" / "weil_eigenfamily_17_19_8_degree64.json"
    fam = json.loads(src.read_text())
    centre = float(frac_mid(fam["log_support_center"])) if isinstance(fam["log_support_center"], dict) \
        else float(Fraction(fam["log_support_center"]))
    cells = []
    for c in fam["cells"]:
        off, hw = float(Fraction(c["center_offset"])), float(Fraction(c["half_width"]))
        rng = c["uniform_candidate_eigenvalue_ranges"]
        rng = rng if isinstance(rng, list) else ast.literal_eval(rng)  # stored as a repr string
        lo, hi = float(Fraction(rng[0]["lo"])), float(Fraction(rng[0]["hi"]))
        rad = float(Fraction(c["uniform_eigenvalue_disk_radius_upper"]))
        cells.append((centre + off - hw, centre + off + hw, lo - rad, hi + rad))
    Lmin, Lmax = math.log(17), math.log(19)
    cstar, delta, R = 0.5 * (Lmin + Lmax), 0.5 * (Lmax - Lmin), 0.25

    fig, axes = plt.subplots(1, 2, figsize=(7.2, 3.0), gridspec_kw={"width_ratios": [1, 1.25]})
    ax = axes[0]
    ax.add_patch(Circle((cstar, 0), R, fill=False, color=BLUE, lw=1.1))
    th = np.linspace(0, 2 * np.pi, 49)[:-1]
    for a in th:  # schematic boundary-rectangle cover of the Cauchy circle
        x, y = cstar + R * np.cos(a), R * np.sin(a)
        ax.add_patch(Rectangle((x - 0.012, y - 0.012), 0.024, 0.024, fill=False, color=BLUE, lw=0.4, alpha=0.7))
    edges = np.linspace(Lmin, Lmax, 33)
    ax.plot([Lmin, Lmax], [0, 0], color=RED, lw=2.4, solid_capstyle="butt")
    for e in edges:
        ax.plot([e, e], [-0.012, 0.012], color="black", lw=0.5)
    ax.plot([cstar], [0], "k+", ms=6)
    ax.annotate(r"$R_*=\frac{1}{4}$", xy=(cstar + R * np.cos(0.9), R * np.sin(0.9)), xytext=(cstar + 0.05, 0.31),
                fontsize=7, arrowprops=dict(arrowstyle="-", lw=0.5))
    ax.annotate(r"$\log17$", xy=(Lmin, 0), xytext=(Lmin - 0.13, -0.09), fontsize=7,
                arrowprops=dict(arrowstyle="-", lw=0.5))
    ax.annotate(r"$\log19$", xy=(Lmax, 0), xytext=(Lmax + 0.02, -0.09), fontsize=7,
                arrowprops=dict(arrowstyle="-", lw=0.5))
    ax.text(cstar, 0.035, r"32 subcells, $\delta<0.0556$", ha="center", fontsize=6.5, color=RED)
    ax.text(cstar, -0.2, r"$q=\delta/R_*<0.223$", ha="center", fontsize=6.5)
    ax.set(xlim=(cstar - 0.33, cstar + 0.33), ylim=(-0.33, 0.33), aspect="equal",
           xlabel=r"$\mathrm{Re}\,L$", ylabel=r"$\mathrm{Im}\,L$", title="(a) Cauchy disk and real cell")
    ax = axes[1]
    for a, b, lo, hi in cells:
        ax.add_patch(Rectangle((math.exp(a), lo), math.exp(b) - math.exp(a), hi - lo,
                               color=BLUE, alpha=0.55, lw=0))
    ax.axhspan(2.259e-26, 1.380e-24, color=GREY, alpha=0.12, lw=0, label=r"uniform $\lambda_0$ range")
    ax.axhline(4.043e-23, color=RED, lw=0.9, ls="--", label=r"ground gap $>4.04\times10^{-23}$")
    ax.set(yscale="log", xlim=(17, 19), ylim=(1e-26, 1e-22), xlabel="$C$",
           ylabel=r"$\lambda_0(C)$", title=r"(b) per-subcell $\lambda_0$ enclosures")
    ax.plot([], [], color=BLUE, lw=6, alpha=0.55, label="subcell enclosure")
    ax.legend(fontsize=6.3, loc="upper left")
    fig.tight_layout()
    gp.save(fig, "weil_cell_geometry")

    marks = [
        (4.870e-41, "Taylor operator error", GREY),
        (4.456e-40, "isolation disk radius", GREY),
        (8.687e-21, "eigenvector distance $d$", PURPLE),
        (4.043e-23, "certified ground gap", RED),
        (9.006e-23, "direct far-block energy", GREEN),
        (9.491e-12, "omitted-mode forcing $\\ell^2$", AMBER),
        (2.906, "uncoupled entrywise bound", BLUE),
    ]
    fig, ax = plt.subplots(figsize=(7.2, 2.3))
    ax.set_xscale("log")
    ax.set_xlim(1e-42, 1e2)
    ax.set_ylim(-1, 1.9)
    ax.axhline(0, color="black", lw=0.8)
    ax.axvspan(2.259e-26, 1.380e-24, ymin=0.25, ymax=0.47, color=BLUE, alpha=0.35, lw=0)
    ax.text(5e-26, -0.62, r"$\lambda_0\in[2.3\times10^{-26},1.4\times10^{-24}]$", fontsize=6.6, ha="center")
    layout = {0: (0.45, "right"), 1: (0.95, "left"), 2: (1.45, "center"), 3: (0.95, "right"),
              4: (0.45, "left"), 5: (0.95, "center"), 6: (0.95, "center")}
    for i, (x, lab, col) in enumerate(marks):
        h, ha = layout[i]
        ax.plot([x, x], [0, h], color=col, lw=1.1)
        ax.plot([x], [0], "o", color=col, ms=3)
        ax.text(x, h + 0.05, f"{lab}\n{x:.2e}", fontsize=6.0, ha=ha, color=col)
    ax.annotate("", xy=(9.491e-12, -0.3), xytext=(4.043e-23, -0.3),
                arrowprops=dict(arrowstyle="<->", color=RED, lw=0.9))
    ax.text(6e-18, -0.25, r"$\approx 2.3\times10^{11}$: forcing $\gg$ gap", fontsize=6.6, color=RED, ha="center")
    ax.set_yticks([])
    ax.grid(False)
    for s in ("left", "top", "right"):
        ax.spines[s].set_visible(False)
    ax.set_xlabel("magnitude (log scale)")
    fig.tight_layout()
    gp.save(fig, "weil_scale_bar")
    return {"cells": len(cells)}


# ---------------------------------------------------- two-routes: Fekete grids
def _grid(ax, rows, cols, entry, colors, title, zero_cells=()):
    for i, r in enumerate(rows):
        for j, c in enumerate(cols):
            col = colors.get((r, c), "white")
            ax.add_patch(Rectangle((j, -i - 1), 1, 1, facecolor=col, edgecolor=GREY, lw=0.6))
            if (r, c) in zero_cells:
                ax.add_patch(Rectangle((j, -i - 1), 1, 1, facecolor="none", edgecolor=RED, lw=0, hatch="////"))
            ax.text(j + 0.5, -i - 0.5, entry(r, c), ha="center", va="center", fontsize=6.6)
        ax.text(-0.25, -i - 0.5, f"{r}", ha="right", va="center", fontsize=6.4, color=GREY)
    for j, c in enumerate(cols):
        ax.text(j + 0.5, 0.25, f"{c}", ha="center", va="bottom", fontsize=6.4, color=GREY)
    ax.set_xlim(-0.9, len(cols) + 0.1)
    ax.set_ylim(-len(rows) - 0.3, 0.9)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title(title, fontsize=8)


def fekete_figure():
    mu = lambda r, c: (r"$\mu_{%d}$" % (r - c)) if r >= c else "$0$"
    fig, axes = plt.subplots(1, 4, figsize=(7.4, 2.9), gridspec_kw={"width_ratios": [1.0, 1.0, 1.0, 1.0]})
    rows = list(range(0, 7))
    cols = [0, 1, 2]
    colors = {}
    for r in (1, 2, 5):
        for c in cols:
            colors[(r, c)] = "#cfdcf0"
    for c in cols:
        colors[(3, c)] = "#f6dcb0"
    _grid(axes[0], rows, cols, mu, colors, "(a) gap-shrinking step")
    axes[0].text(1.5, -7.75, "rows $\\{1,2,5\\}$ + inserted $s=3$", ha="center", fontsize=6.2)
    axes[0].text(1.5, -8.45, "$M_t\\,S=M_0\\,S'+M_{\\rm last}\\,S''$", ha="center", fontsize=6.4)
    axes[0].text(1.5, -9.15, "$M_0$: $\\{2,3,5\\}$, $M_{\\rm last}$: $\\{1,2,3\\}$", ha="center", fontsize=6.0)
    rsel, csel = (1, 2, 5), (0, 3, 4)
    zero = {(r, c) for r in (1, 2) for c in (3, 4)}
    _grid(axes[1], rsel, csel, mu, {(r, c): "#f3d2cb" for (r, c) in zero},
          "(b) dominance fails: $\\det=0$", zero_cells=zero)
    axes[1].text(1.5, -3.75, "$r_1=2<c_1=3$:", ha="center", fontsize=6.2)
    axes[1].text(1.5, -4.45, "$(a{+}1)\\times(k{-}a)=2\\times2$ zero block", ha="center", fontsize=6.0)
    axes[1].text(1.5, -5.15, "$2+2>k=3$ $\\Rightarrow$ every term vanishes", ha="center", fontsize=6.0)
    _grid(axes[2], (5, 6, 7), (0, 2, 3), mu, {(r, c): "#d6ead9" for r in (5, 6, 7) for c in (0, 2, 3)},
          "(c) contiguous rows")
    _grid(axes[3], (4, 5, 7), (0, 1, 2), mu, {(r, c): "#d6ead9" for r in (4, 5, 7) for c in (0, 1, 2)},
          "initial columns")
    axes[2].text(1.5, -3.75, "rows $5,6,7$; cols $0,2,3$", ha="center", fontsize=6.2)
    axes[3].text(1.5, -3.75, "rows $R_j=7-c_{2-j}$", ha="center", fontsize=6.2)
    axes[2].annotate("", xy=(4.15, -1.5), xytext=(3.2, -1.5), xycoords="data",
                     arrowprops=dict(arrowstyle="->", color=GREEN, lw=1.0))
    axes[2].text(3.67, -1.05, "reverse +\ntranspose", ha="center", fontsize=5.6, color=GREEN)
    fig.tight_layout(w_pad=0.6)
    gp.save(fig, "two_routes_fekete_grids")


# ------------------------------------------------------------- DH figures
def dh_figures():
    sector = DH_ROOT / "research" / "prime_spectral" / "verification_2026_10_12_sector"
    line = json.loads((sector / "line_brackets_H340.json").read_text())["brackets"]
    disks = json.loads((sector / "offline_disks_H340.json").read_text())["roots"]
    gam_line = sorted(float((Fraction(b["lo"]) + Fraction(b["hi"])) / 2) for b in line)
    off = sorted((float(frac_mid(d["imag"])), float(frac_mid(d["real"])) - 0.5) for d in disks)

    fig, ax = plt.subplots(figsize=(7.0, 3.6))
    w_line = np.array(gam_line) ** 2
    ax.plot(w_line, np.zeros_like(w_line), "|", color=BLUE, ms=7, mew=0.8, label="235 critical-line zeros ($\\psi=0$)")
    w_off = [g * g + b * b for g, b in off]
    psi_off = [2 * math.atan(abs(b) / g) for g, b in off]
    ax.plot(w_off, psi_off, "o", color=RED, ms=4, label="7 off-line pairs (upper member)")
    g0, b0 = off[0]
    ax.annotate(r"$0.8085+85.70i$, $\psi=0.0072$", xy=(w_off[0], psi_off[0]),
                xytext=(4e2, 0.0105), fontsize=6.8, arrowprops=dict(arrowstyle="->", lw=0.6))
    ax.axhline(math.pi / 436, color=GREEN, lw=1.0, label=r"$\pi/436$: wedge for PF$_{435}$")
    ax.axhline(math.pi / 437, color=GREEN, lw=0.8, ls=":", label=r"$\pi/437$ (PF$_{436}$ not guaranteed)")
    W = np.logspace(math.log10(340 ** 2), 5.6, 60)
    ax.plot(W, [2 * math.atan(1 / math.sqrt(x)) for x in W], color=GREY, lw=1.0, ls="--",
            label=r"above height 340: $\psi\leq2\arctan(1/\gamma)$")
    ax.axvline(64, color=AMBER, lw=1.0)
    ax.text(64 * 1.08, 0.0108, r"$|w|=64$", color=AMBER, fontsize=6.8)
    ax.plot([gam_line[0] ** 2], [0], "s", color=AMBER, ms=5, label=r"dominant pole $a=\gamma_1^2\approx25.9$")
    ax.axvspan(1, g0 * g0 + b0 * b0, color=BLUE, alpha=0.05, lw=0)
    ax.text(1.2e2, 0.0024, "43 line zeros with $|w|<|w_0|$\n$\\Rightarrow$ split at shift $s^*=44$",
            fontsize=6.6, color=BLUE)
    ax.set(xscale="log", xlim=(10, 4e5), ylim=(-0.0006, 0.0125),
           xlabel=r"$|w|$, folded variable $w=(\rho-\frac{1}{2})^2$ (log scale)",
           ylabel=r"deviation $\psi$ from $\arg w=\pi$ (rad)",
           title="Folded DH zeros on log-radial axes: Schoenberg wedge, dominant pole and split pair")
    ins = ax.inset_axes([0.60, 0.50, 0.22, 0.42])
    ins.axhline(math.pi / 436, color=GREEN, lw=1.0)
    ins.axhline(math.pi / 437, color=GREEN, lw=0.8, ls=":")
    ins.plot(w_off[:1], psi_off[:1], "o", color=RED, ms=4)
    ins.set_xscale("log")
    ins.set_xlim(w_off[0] / 1.15, w_off[0] * 1.15)
    ins.set_ylim(0.007175, 0.007220)
    ins.tick_params(labelsize=5.2)
    ins.set_title(r"zoom: $\pi/437<\psi<\pi/436$", fontsize=6.2)
    fig.legend(*ax.get_legend_handles_labels(), fontsize=6.2, ncol=3, loc="lower center",
               bbox_to_anchor=(0.5, -0.02), frameon=False)
    fig.tight_layout(rect=(0, 0.13, 1, 1))
    gp.save(fig, "dh_folded_wedge")

    calib = DH_ROOT / "research" / "prime_spectral" / "verification_2026_10_13_calibration"
    att = json.loads((calib / "zero_attribution.json").read_text())
    names = {"dh5": "DH5", "q13_label2": "DH13(2)", "epstein5": "Epstein5", "q17_label3": "DH17(3)",
             "q7_label3": "DH7(3)", "q13_label6": "DH13(6)", "epstein6": "Epstein6"}
    rows = []
    for c in att["controls"]:
        w = c["witnesses"][0]
        q = w["off_line_quartets"][w["dominant_negative_quartet_index"]]
        rows.append((names.get(c["name"], c["name"]), float(frac_mid(q["quartet_contribution"])),
                     float(frac_mid(w["finite_line_sum"])), float(frac_mid(w["finite_total"])),
                     float(frac_mid(w["geometric_full_quotient"]))))
    fig, ax = plt.subplots(figsize=(7.2, 2.9))
    x = np.arange(len(rows))
    wd = 0.2
    series = [("dominant off-line quartet", 1, RED), ("critical-line sum (atlas)", 2, BLUE),
              ("finite atlas total $P_H$", 3, AMBER), ("certified quotient $Q$", 4, "black")]
    for k, (lab, idx, col) in enumerate(series):
        vals = [r[idx] for r in rows]
        ax.bar(x + (k - 1.5) * wd, [abs(v) for v in vals], wd, color=col, alpha=0.8, label=lab,
               hatch=None if k == 1 else "", edgecolor="white", lw=0.3)
        for xi_, v in zip(x + (k - 1.5) * wd, vals):
            ax.text(xi_, abs(v) * 1.6, "$+$" if v > 0 else "$-$", ha="center", fontsize=6.5, color=col)
    ax.set_yscale("log")
    ax.set_ylim(1e-45, 1e6)
    ax.set_xticks(x, [f"{r[0]}\n$|P_H/Q|\\approx{abs(r[3] / r[4]):.0f}$" for r in rows])
    ax.set_ylabel("magnitude (log); sign above bar")
    ax.set_title("Finite-atlas attribution: the off-line quartet is largely cancelled by on-line zeros, "
                 "and $P_H$ still exceeds $Q$ by $10^{2.4}$ to $10^{4.1}$", fontsize=8)
    ax.legend(fontsize=6.2, ncol=4, loc="upper center")
    fig.tight_layout()
    gp.save(fig, "dh_attribution_bars")
    return {"ratios": {r[0]: abs(r[3] / r[4]) for r in rows},
            "quartet_over_line": {r[0]: abs(r[1] / r[2]) for r in rows}}


def main(names):
    every = ["lambda0", "hef", "weil", "fekete", "dh"]
    names = names or every
    report = {}
    if "lambda0" in names:
        report["lambda0"] = lambda0_figure()
    if "hef" in names:
        report["hef"] = hef_figure()
    if "weil" in names:
        report["weil"] = weil_figures()
    if "fekete" in names:
        fekete_figure()
    if "dh" in names:
        report["dh"] = dh_figures()
    print(json.dumps(report, indent=1, default=str))


if __name__ == "__main__":
    main(sys.argv[1:])
