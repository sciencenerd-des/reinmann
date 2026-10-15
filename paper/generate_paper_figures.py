#!/usr/bin/env python3
"""Regenerate the explanatory figures shared by the five manuscripts.

Every plotted number is recomputed here from a stated source:

  * Xi coefficients: midpoints of the rigorous Arb enclosures in
    research/certified_xi/coefficients_{120,200}.json (relative accuracy
    >= 943 bits), evaluated in mpmath at 60 digits;
  * Weil matrix: the closed formulas of weil_infinite_rank_tail_paper.tex,
    via the independent mpmath implementation in weil_tail_crosscheck.py;
  * zeta values: mpmath at 20-30 digits.

The plots illustrate the data.  They are not certificates; the certificates
are the scripts cited in each paper.  Usage:

    python3 paper/generate_paper_figures.py [name ...]

Requires matplotlib, numpy and mpmath.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from matplotlib.patches import Patch, Rectangle

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE / "figures"
OUT.mkdir(exist_ok=True)

# One palette for all papers.
BLUE, RED, GREEN, AMBER, GREY, PURPLE = (
    "#2455a4", "#b34b33", "#40805b", "#c98a1b", "#666666", "#6b4c9a")
plt.rcParams.update({
    "font.size": 9, "axes.titlesize": 9.5, "axes.labelsize": 9,
    "legend.fontsize": 7.5, "xtick.labelsize": 8, "ytick.labelsize": 8,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.grid": True, "grid.alpha": 0.18, "savefig.bbox": "tight",
    "savefig.pad_inches": 0.03, "pdf.fonttype": 42, "mathtext.fontset": "cm",
    # Computer Modern text to match the LaTeX body; cmr10 lacks a minus glyph,
    # so tick labels are drawn through mathtext.
    "font.family": "serif", "font.serif": ["cmr10"], "axes.formatter.use_mathtext": True,
    "axes.unicode_minus": False,
})


def save(fig, name):
    fig.savefig(OUT / f"{name}.pdf")
    plt.close(fig)
    print("wrote", (OUT / f"{name}.pdf").relative_to(ROOT))


# ---------------------------------------------------------------- Xi data
def load_mu(nmax=200):
    src = ROOT / "research" / "certified_xi" / f"coefficients_{nmax}.json"
    recs = sorted(json.loads(src.read_text())["coefficients"], key=lambda r: r["n"])
    mp.mp.dps = 60
    out = []
    for r in recs:
        mid = (Fraction(r["lo"]) + Fraction(r["hi"])) / 2
        out.append(mp.mpf(mid.numerator) / mid.denominator)
    return out


def contiguous_minor(mu, k, m):
    at = lambda n: mu[n] if n >= 0 else mp.mpf(0)
    return mp.det(mp.matrix([[at(m + i - j) for j in range(k)] for i in range(k)]))


# ------------------------------------------------------- frontier (k, m)
def frontier_map(name, conditional_pf58):
    """Where the strict contiguous ladder D_k(m) > 0 is known, and where not."""
    fig, ax = plt.subplots(figsize=(6.4, 3.9))
    k = np.logspace(0, 4, 400)
    top = 1e30
    # Open region first so that known regions overlay it.
    ax.fill_between(k, 1, top, color=RED, alpha=0.10, lw=0)
    # Cubic wedge (external preprint): m >= 1e18 k^3.
    wedge = np.minimum(1e18 * k**3, top)
    ax.fill_between(k, wedge, top, facecolor="none", edgecolor=AMBER,
                    hatch="////", lw=0, alpha=0.9)
    ax.plot(k, wedge, color=AMBER, lw=1.4)
    # Katkova: every minor of order <= 43 is nonnegative, at every shift.
    ax.fill_between([1, 43], 1, top, color=GREEN, alpha=0.22, lw=0)
    ax.axvline(43, color=GREEN, lw=1.2)
    # Certified strict block of this programme: k <= 16, m <= 121 - k.
    kk = np.arange(1, 17)
    ax.fill_between(kk, 1, 121 - kk + 1, step="post", color=BLUE, alpha=0.75, lw=0)
    if conditional_pf58:
        ax.axvline(58, color=GREEN, lw=1.0, ls="--")
        ax.text(62, 3e2, "PF$_{58}$ if $\\zeta\\neq0$ on\n$\\mathrm{Re}\\,s>7/8$\n(external claim)",
                fontsize=6.8, color=GREEN, va="bottom")
    ax.set(xscale="log", yscale="log", xlim=(1, 1e4), ylim=(1, top),
           xlabel="order $k$ of the contiguous minor $D_k(m)$",
           ylabel="shift $m+1$")
    ax.text(5.5, 1e9, "nonnegative at every\nshift for $k\\leq43$\n[Katkova 2007]",
            fontsize=7.2, color="#1f5a35", ha="center")
    ax.text(1.15, 160, "strict, Arb-certified\n$k\\leq16,\\ m\\leq121-k$", fontsize=6.8,
            color=BLUE, va="bottom")
    ax.text(2.2e3, 2e27, "strict for $m\\geq10^{18}k^3$\n(external preprint,\nnot re-checked)",
            fontsize=7.2, color="#8a5a00", ha="center", va="top",
            bbox=dict(fc="white", ec="none", alpha=0.85, pad=1))
    ax.text(1.3e3, 3e6, "OPEN\nunbounded order,\nmoderate shift", fontsize=9,
            color=RED, ha="center", fontweight="bold")
    ax.set_title("The strict contiguous ladder: what is known, and the open wedge")
    save(fig, name)


# ---------------------------------------------------------- order 3 gap
def order3_gap(mu):
    ms = list(range(2, len(mu) - 2))
    g = [float(contiguous_minor(mu, 3, m) / mu[m] ** 3) for m in ms]
    assert all(x > 0 for x in g)
    ms_a, g_a = np.array(ms), np.array(g)
    fit = ms_a >= 40
    slope, icept = np.polyfit(np.log(ms_a[fit]), np.log(g_a[fit]), 1)

    fig, axes = plt.subplots(1, 2, figsize=(7.2, 2.9), gridspec_kw=dict(width_ratios=[1, 1.25]))
    ax = axes[0]
    pre = ms_a <= 118
    ax.loglog(ms_a[pre], g_a[pre], ".", ms=3.2, color=BLUE, label="$m\\leq118$ (121 coefficients)")
    ax.loglog(ms_a[~pre], g_a[~pre], ".", ms=3.2, color=PURPLE, label="$118<m\\leq198$ (201 coefficients)")
    mline = np.logspace(np.log10(40), np.log10(200), 50)
    ax.loglog(mline, np.exp(icept) * mline**slope, "--", color=GREY, lw=1,
              label=f"fit $\\propto m^{{{slope:.2f}}}$ ($m\\geq40$)")
    ax.set(xlabel="shift $m$", ylabel="$G_3(m)=D_3(m)/\\mu_m^3$",
           title="(a) the first open rung is positive but thin")
    ax.legend(loc="lower left")

    ax = axes[1]
    m_ext = np.logspace(0.3, 20, 300)
    ax.loglog(ms_a, g_a, color=BLUE, lw=1.6, label="computed $G_3(m)$")
    ax.loglog(m_ext[m_ext > 200], np.exp(icept) * m_ext[m_ext > 200] ** slope, ":",
              color=GREY, lw=1.2, label="power-law extrapolation (not a bound)")
    ax.axvspan(198, 2.7e19, color=RED, alpha=0.10, lw=0)
    ax.axvspan(2.7e19, 1e20, color=AMBER, alpha=0.30, lw=0)
    ax.text(3e9, 1e-6, "uncertified wedge\n$198<m<2.7\\times10^{19}$", color=RED,
            ha="center", fontsize=7.5)
    ax.text(2.7e19, 1e-30, "cubic-wedge\ntail", color="#8a5a00", ha="right", fontsize=7)
    ax.set(xlim=(2, 1e20), xlabel="shift $m$ (log scale)",
           title="(b) the scale of the remaining order-3 gap")
    ax.legend(loc="lower left")
    fig.tight_layout()
    save(fig, "two_routes_order3_gap")
    return slope


# ---------------------------------------------------- Turan route kill
def turan_landscape(mu):
    """Five-term windows obeying every order-2 and order-3 Turan inequality.

    Two populations: log-uniform windows (large margins) and perturbed
    log-quadratic windows, which reach the nearly geometric regime where the
    Xi windows live.  Only windows passing all five inequalities are kept.
    """
    rng = np.random.default_rng(20261010)
    n = 1_500_000
    wide = np.exp(rng.uniform(np.log(1e-3), np.log(3.0), size=(n, 5)))
    th = np.exp(rng.uniform(np.log(1e-4), np.log(2.0), n))
    k = np.arange(5) - 2
    eps = rng.normal(size=(n, 5)) * (th * np.exp(rng.uniform(np.log(1e-3), 0, n)))[:, None]
    near = np.exp(-th[:, None] * k**2 / 2 + rng.normal(size=n)[:, None] * k + eps)
    b = np.vstack([wide, near])
    b /= b[:, 2:3]
    t2 = np.stack([b[:, j] ** 2 - b[:, j - 1] * b[:, j + 1] for j in (1, 2, 3)], 1)

    def t3(a0, a1, a2, a3):
        return 4 * (a1**2 - a0 * a2) * (a2**2 - a1 * a3) - (a1 * a2 - a0 * a3) ** 2

    ok = (t2 > 0).all(1) & (t3(*b[:, 0:4].T) >= 0) & (t3(*b[:, 1:5].T) >= 0)
    b = b[ok]

    def margin_of(w):
        return np.min(np.stack([1 - w[:, j - 1] * w[:, j + 1] / w[:, j] ** 2 for j in (1, 2, 3)], 1), 1)

    def d3(w):
        b0, b1, b2, b3, b4 = w.T
        return (b2**3 + b0 * b3**2 + b1**2 * b4 - 2 * b1 * b2 * b3 - b0 * b2 * b4) / b2**3

    margin, D = margin_of(b), d3(b)
    witness = np.array([[0.01, 1, 1.25, 1, 0.01]])
    wD, wm = float(d3(witness)[0]), float(margin_of(witness)[0])
    assert abs(wD * 1.25**3 - (45 / 64 - 31 / 25 + 79 / 8000)) < 1e-12

    xm, xd = [], []
    for m in range(2, len(mu) - 2):
        w = [mu[m + j] for j in (-2, -1, 0, 1, 2)]
        xm.append(float(min(1 - w[j - 1] * w[j + 1] / w[j] ** 2 for j in (1, 2, 3))))
        xd.append(float(contiguous_minor(mu, 3, m) / mu[m] ** 3))

    fig, ax = plt.subplots(figsize=(6.4, 3.6))
    neg = D < 0
    keep = rng.random(len(D)) < 0.25  # thin the cloud for a light PDF
    ax.scatter(margin[~neg & keep], D[~neg & keep], s=0.5, color=BLUE, alpha=0.15, lw=0, rasterized=True)
    ax.scatter(margin[neg & keep], D[neg & keep], s=0.5, color=RED, alpha=0.15, lw=0, rasterized=True)
    ax.plot(xm, xd, "-", color="black", lw=1.8)
    ax.annotate("$\\Xi$ windows $m=2,\\ldots,198$", (xm[60], xd[60]), xytext=(2.5e-2, 3e-7),
                fontsize=7.5, arrowprops=dict(arrowstyle="->", lw=0.7))
    ax.plot(wm, wD, "*", ms=12, color=AMBER, mec="black", mew=0.6, zorder=5)
    ax.annotate("Lean witness $(\\frac{1}{100},1,\\frac{5}{4},1,\\frac{1}{100})$", (wm, wD),
                xytext=(3e-3, -0.25), fontsize=7.5, arrowprops=dict(arrowstyle="->", lw=0.7))
    ax.axhline(0, color=GREY, lw=0.8)
    ax.set_xscale("log")
    ax.set_yscale("symlog", linthresh=1e-8)
    ax.set(xlim=(1e-4, 1), ylim=(-1, 2),
           xlabel="smallest normalized order-2 Turán margin $\\min_j(1-b_{j-1}b_{j+1}/b_j^2)$",
           ylabel="$D_3/b_2^3$ (symmetric log)",
           title="Windows satisfying every order-2 and order-3 Turán inequality")
    ax.legend(handles=[Patch(color=BLUE, alpha=0.6, label=f"$D_3>0$ ({(~neg).sum():,})"),
                       Patch(color=RED, alpha=0.6, label=f"$D_3<0$ ({neg.sum():,})")],
              loc="upper left", title="feasible samples", title_fontsize=7)
    save(fig, "two_routes_turan_landscape")
    bins = [(1e-4, 1e-2), (1e-2, 1e-1), (1e-1, 1)]
    return {"feasible": int(len(D)), "negative": int(neg.sum()),
            "negative_fraction_by_margin": {f"{lo:g}-{hi:g}": round(float(neg[(margin >= lo) & (margin < hi)].mean()), 3)
                                            for lo, hi in bins},
            "xi_margin_range": (min(xm), max(xm))}


# ------------------------------------------------------------- Weil tail
def weil_model():
    sys.path.insert(0, str(HERE))
    argv, sys.argv = sys.argv, sys.argv[:1]  # the module reads argv at import
    try:
        import weil_tail_crosscheck as wt  # independent mpmath implementation
    finally:
        sys.argv = argv
    return wt


def weil_constants():
    Lmin, Lmax = math.log(17), math.log(19)
    E = math.exp(-Lmin / 2) / (1 - math.exp(-2 * Lmin))
    P = sum(math.log(p) / math.sqrt(a) for a, p in [(2, 2), (4, 2), (8, 2), (16, 2), (3, 3), (9, 3),
                                                     (5, 5), (7, 7), (11, 11), (13, 13), (17, 17)])
    BR = (math.pi / 2 + min(2, Lmax / math.pi)) / (2 * math.pi) + E / math.pi
    return Lmin, Lmax, E, P, BR


def weil_figures():
    wt = weil_model()
    mp.mp.dps = 40
    B = 3.157010  # Proposition 3.6 / Table of constants
    data = {}
    for C in (17, 18, 19):
        W = wt.Weil(C, terms=40)
        E, Q = mp.eigsy(W.even_block(8))
        order = sorted(range(9), key=lambda i: E[i])
        u = [Q[i, order[0]] for i in range(9)]
        if u[0] < 0:
            u = [-x for x in u]
        data[C] = dict(W=W, eig=[E[i] for i in order], u=u,
                       S=u[0] + mp.sqrt(2) * mp.fsum(u[1:]))

    # Forcing R_n for 9 <= n <= NMAX at C = 17 (worst cell side).
    NMAX = 3000
    d = data[17]
    W, u = d["W"], d["u"]
    mp.mp.dps = 30
    bK = [W.b(i) for i in range(9)]
    ns = np.arange(9, NMAX + 1)
    R, lead = [], []
    for n in ns:
        bn = W.b(int(n))
        r = mp.sqrt(2) * bn * d["S"] / n
        lead.append(abs(float(r)))
        r += 2 * bn / n * mp.fsum(u[i] * i * i / (n * n - i * i) for i in range(1, 9))
        r -= 2 * mp.fsum(i * bK[i] * u[i] / (n * n - i * i) for i in range(1, 9))
        R.append(float(r))
    R, lead = np.abs(np.array(R)), np.array(lead)
    tail = np.sqrt(np.cumsum((R**2)[::-1])[::-1])  # tail[j] = ||R_{n >= ns[j]}|| up to NMAX
    l1 = abs(float(u[0])) + math.sqrt(2) * sum(abs(float(x)) for x in u[1:])

    fig, axes = plt.subplots(1, 3, figsize=(7.4, 3.2), gridspec_kw=dict(width_ratios=[0.8, 1, 1.15]))
    ax = axes[0]
    j = np.arange(9)
    for C, col, off in ((17, BLUE, -0.25), (18, GREEN, 0), (19, RED, 0.25)):
        ax.bar(j + off, [float(x) for x in data[C]["u"]], width=0.25, color=col, label=f"$C={C}$")
    ax.axhline(0, color=GREY, lw=0.6)
    ax.set(xlabel="even mode $j$", ylabel="$u_j(C)$", title="(a) rank-8 ground state")
    ax.legend(loc="upper right", fontsize=6.5)
    sexp = abs(float(data[17]["S"]))
    e = math.floor(math.log10(sexp))
    ax.text(0.97, 0.06, "boundary sum at $C=17$:\n$S=u_0+\\sqrt{2}\\sum_{j\\geq1}u_j$\n$\\approx%.1f\\times10^{%d}$" % (sexp / 10**e, e),
            transform=ax.transAxes, fontsize=6.6, ha="right", va="bottom")

    ax = axes[1]
    ax.loglog(ns, R, color=BLUE, lw=0.9, label="$|R_n|$, coupled (direct)")
    ax.loglog(ns, lead, color=GREEN, lw=0.9, ls="--", label="$\\sqrt{2}\\,|b_nS|/n$ term")
    ax.loglog(ns, 2 * np.sqrt(2) * B * l1 / (ns - 8), color=RED, lw=0.9,
              label="entrywise bound $2\\sqrt{2}B\\|u\\|_1/(n-8)$")
    ax.set(xlabel="omitted index $n$", ylabel="size", title="(b) omitted-mode forcing, $C=17$")
    ax.legend(loc="upper center", bbox_to_anchor=(0.5, -0.22), fontsize=6.2, frameon=False)

    ax = axes[2]
    J = ns - 1
    ax.loglog(J, tail, color=BLUE, lw=1.4, label="$\\|R_{n>J}\\|$ (direct sum to $n\\leq%d$)" % NMAX)
    Jc = np.arange(9, NMAX)
    ax.loglog(Jc, 2 * math.sqrt(2) * B * l1 / np.sqrt(Jc - 8), color=RED, lw=1.2,
              label="uncoupled bound $2\\sqrt{2}B\\|u\\|_1/\\sqrt{J-8}$")
    ax.plot([64], [9.491e-12], "*", ms=10, color=AMBER, mec="black", mew=0.5,
            label="certified: $<9.491\\times10^{-12}$ on $[17,19]$")
    ax.plot([64], [2.906], "s", ms=4.5, color=RED)
    ax.annotate("", xy=(64, 1.5e-11), xytext=(64, 2.0), arrowprops=dict(arrowstyle="<->", lw=0.8))
    ax.text(75, 3e-6, "$\\approx3\\times10^{11}$", fontsize=7.5)
    ax.set(xlabel="cut-off $J$", ylabel="tail norm", ylim=(1e-15, 20),
           title="(c) order of operations matters")
    ax.legend(loc="upper center", bbox_to_anchor=(0.45, -0.22), fontsize=6.2, frameon=False)
    fig.tight_layout(w_pad=0.6)
    save(fig, "weil_forcing_tail")

    # Displacement sequence split into pole / archimedean / prime parts.
    W = data[18]["W"]
    mp.mp.dps = 25
    nn = np.arange(1, 401)
    L = W.L
    pole, arch, prime = [], [], []
    for n in nn:
        w = W.w(int(n))
        D = mp.cosh(L / 2) - 1
        pole.append(float(2 * D / mp.pi * w / (mp.mpf(1) / 4 + w**2)))
        a = mp.im(mp.digamma(mp.mpf(1) / 4 + 1j * mp.pi * n / L)) / (2 * mp.pi)
        a -= mp.fsum(mp.exp(-(2 * k + mp.mpf(1) / 2) * L) * w / ((2 * k + mp.mpf(1) / 2) ** 2 + w**2)
                     for k in range(40)) / mp.pi
        arch.append(float(a))
        prime.append(float(mp.fsum(mp.log(p) / mp.sqrt(q) * mp.sin(w * mp.log(q))
                                   for q, p in W.powers) / mp.pi))
    pole, arch, prime = map(np.array, (pole, arch, prime))
    _, _, _, P, BR = weil_constants()
    fig, ax = plt.subplots(figsize=(6.4, 2.8))
    ax.plot(nn, prime, color=PURPLE, lw=0.8, label="prime part $b^{\\Pi}_n$ ($p^a\\leq17$)")
    ax.plot(nn, pole, color=RED, lw=1.2, label="pole part $b^P_n$")
    ax.plot(nn, arch, color=GREEN, lw=1.2, label="archimedean part $b^{\\mathbb{R}}_n$")
    ax.plot(nn, pole + arch + prime, color="black", lw=1.0, label="$b_n=nA_{n0}$")
    for s in (1, -1):
        ax.axhline(s * B, color=GREY, ls="--", lw=0.8)
    ax.text(400, -B * 0.92, "$\\pm B=\\pm3.157$ (uniform on $[17,19]$)", ha="right", va="bottom", fontsize=7)
    ax.set(xscale="log", xlabel="index $n$", ylabel="$b_n$",
           title="Displacement sequence at $C=18$: bounded, but rows decay only like $1/|i-j|$")
    ax.legend(loc="upper left", ncol=2, fontsize=6.8)
    ax.set_ylim(-3.6, 4.4)
    save(fig, "weil_displacement")

    # High-mode coercivity: actual diagonal versus the proved lower bounds.
    Lmin, Lmax, E, P, BR = weil_constants()
    def delta(n):
        return math.log(n / Lmax) - Lmax / (math.pi * n) - 1 / (4 * n) - Lmax * (1 + E) / (2 * math.pi**2 * n**2)
    off = 2 * math.pi * BR + 2 * P
    pole_neg = 2 * math.sinh(Lmax / 2) - Lmax
    beta_e = lambda n: delta(n) - off
    beta_f = lambda n: beta_e(n) - pole_neg
    assert beta_e(18_612_929) > 1 > beta_e(18_612_928)
    assert beta_f(60_879_750) > 1 > beta_f(60_879_749)
    n0 = np.unique(np.logspace(0, 9, 400).astype(np.int64))
    mp.mp.dps = 20
    nd = np.unique(np.logspace(0.5, 5, 28).astype(int))
    Ann = {C: [float(data[C]["W"].diag(int(n))) for n in nd] for C in (17, 19)}

    fig, ax = plt.subplots(figsize=(6.4, 3.0))
    ax.semilogx(nd, Ann[17], "o", ms=3, color=BLUE, label="actual diagonal $A_{nn}$, $C=17$")
    ax.semilogx(nd, Ann[19], "s", ms=3, color=PURPLE, mfc="none", label="actual diagonal $A_{nn}$, $C=19$")
    ax.semilogx(n0, [delta(x) for x in n0], color=GREEN, lw=1.2,
                label="$\\delta(n)\\leq -H_{nn}$ (archimedean, proved)")
    ax.semilogx(n0, [beta_e(x) for x in n0], color=BLUE, lw=1.4, label="$\\beta_{\\rm even}(n_0)$")
    ax.semilogx(n0, [beta_f(x) for x in n0], color=RED, lw=1.4, label="$\\beta_{\\rm full}(n_0)$")
    ax.axhline(1, color="black", lw=0.8, ls=":")
    for x, c, lab in ((18_612_929, BLUE, "18,612,929"), (60_879_750, RED, "60,879,750")):
        ax.axvline(x, color=c, lw=0.7, ls="--")
        ax.text(x * 0.8, -9.5, lab, rotation=90, fontsize=6.8, color=c, ha="right", va="bottom")
    ax.annotate("", xy=(3, 1), xytext=(3, 1 - off), arrowprops=dict(arrowstyle="<->", lw=0.8))
    ax.text(3.6, 1 - off / 2, "off-diagonal + prime budget\n$2\\pi B_{\\mathbb{R}}+2\\mathcal{P}\\approx%.2f$" % off,
            fontsize=6.8, va="center")
    ax.set(xlim=(1, 1e9), ylim=(-12, 22), xlabel="mode index $n$ / far-block start $n_0$",
           ylabel="value", title="High-mode coercivity: $\\log n$ growth beats a rank-independent budget")
    ax.legend(loc="upper left", fontsize=6.6, ncol=2)
    save(fig, "weil_coercivity")

    # What is and is not controlled along the Fourier index.
    fig, ax = plt.subplots(figsize=(6.6, 1.65))
    ax.set_xscale("log")
    ax.set(xlim=(0.8, 3e8), ylim=(0, 3))
    ax.grid(False)
    for s in ("left", "top", "right"):
        ax.spines[s].set_visible(False)
    ax.set_yticks([])
    def band(x0, x1, y, h, col, txt, **kw):
        ax.add_patch(Rectangle((x0, y), x1 - x0, h, color=col, alpha=kw.pop("alpha", 0.75), lw=0))
        ax.text(math.sqrt(x0 * x1), y + h / 2, txt, ha="center", va="center", fontsize=7, **kw)
    band(1, 9, 1.9, 0.9, GREEN, "retained\n$0\\leq j\\leq8$", color="white")
    band(9, 18_612_929, 1.9, 0.9, RED, "intermediate modes: inverse response NOT controlled",
         color="white", alpha=0.55)
    band(18_612_929, 3e8, 1.9, 0.9, BLUE, "coercive\n$>\\|x\\|^2$", color="white")
    band(65, 3e8, 0.55, 0.9, AMBER, "forcing tail $\\|R_{n>64}\\|<9.491\\times10^{-12}$ (all omitted indices)",
         alpha=0.6)
    ax.text(1, 0.15, "ground state certified on $C\\in[17,19]$, $\\lambda_0\\in[2.26\\times10^{-26},1.38\\times10^{-24}]$",
            fontsize=6.6)
    ax.set_xlabel("even Fourier index $j+1$ (log scale)")
    save(fig, "weil_mode_map")

    return dict(S={C: float(data[C]["S"]) for C in data},
                eig0={C: float(data[C]["eig"][0]) for C in data},
                tail64=float(tail[ns.tolist().index(65)]),
                beta=(beta_e(18_612_929), beta_f(60_879_750)))


# ----------------------------------------------------------- same height
def same_height_figures():
    mp.mp.dps = 20
    zeros = [float(mp.im(mp.zetazero(k))) for k in range(1, 11)]

    fig, axes = plt.subplots(1, 2, figsize=(7.0, 3.1), gridspec_kw=dict(width_ratios=[0.95, 1.25]))
    ax = axes[0]
    ax.axvspan(0, 1, color=GREY, alpha=0.07)
    ax.axvline(0.5, color=BLUE, lw=1)
    ax.plot([0.5] * len(zeros), zeros, "o", color=BLUE, ms=4.5, label="first ten zeros (all on the line)")
    g_star = 55.0
    for x, lab in ((0.3, "$\\beta$"), (0.7, "$1-\\beta$")):
        ax.plot(x, g_star, "o", ms=8, mfc="white", mec=RED, mew=1.6)
        ax.text(x, g_star - 2.2, lab, ha="center", va="top", color=RED, fontsize=8)
    ax.annotate("", xy=(0.675, g_star), xytext=(0.325, g_star),
                arrowprops=dict(arrowstyle="<->", color=RED, lw=1, ls="--"))
    ax.text(0.03, 67.0, "excluded configuration: a fiber $\\mathcal{Z}_{\\gamma}$ with two\n"
            "real parts, forced in mirror pairs by $s\\mapsto1-\\bar s$;\n"
            "its energy $E(\\gamma)=\\sum(\\beta-\\frac{1}{2})^2=0.08>0$",
            color=RED, fontsize=6.6, va="top", bbox=dict(fc="white", ec=RED, lw=0.5, pad=2))
    ax.set(xlim=(0, 1), ylim=(10, 68), xlabel="$\\sigma=\\mathrm{Re}\\,s$", ylabel="$\\gamma=\\mathrm{Im}\\,s$",
           title="(a) RH $\\Leftrightarrow$ every fiber has one real part")
    ax.legend(loc="lower right", fontsize=6.6)

    ax = axes[1]
    sig = np.linspace(0.02, 0.98, 241)
    for gz, col in zip(zeros[:4], (BLUE, GREEN, PURPLE, AMBER)):
        vals = [float(mp.log(abs(mp.zeta(mp.mpc(s, gz))))) for s in sig]
        ax.plot(sig, vals, color=col, lw=1.2, label=f"$\\gamma={gz:.3f}$")
    ax.axvline(0.5, color=GREY, lw=0.7, ls="--")
    ax.set(xlabel="$\\sigma$", ylabel="$\\log|\\zeta(\\sigma+i\\gamma)|$", ylim=(-9, 2.5),
           title="(b) horizontal slices through the first four zeros")
    ax.legend(loc="lower right", fontsize=6.8)
    ax.text(0.04, -8.3, "each slice vanishes only at $\\sigma=\\frac{1}{2}$", fontsize=7)
    fig.tight_layout()
    save(fig, "same_height_fibers")

    # The falsified global convexity target.
    g = 0.5
    f = lambda x: float(abs(mp.zeta(mp.mpc(x, g))) ** 2)
    xs = np.linspace(0.05, 0.99, 400)
    ys = np.array([f(x) for x in xs])
    x0, x1 = 0.66, 0.98
    m = (x0 + x1) / 2
    chord = lambda x: f(x0) + (f(x1) - f(x0)) * (x - x0) / (x1 - x0)
    fig, axes = plt.subplots(1, 2, figsize=(7.0, 2.8))
    ax = axes[0]
    ax.plot(xs, ys, color=BLUE, lw=1.4, label="$|\\zeta(x+0.5i)|^2$")
    ax.plot([x0, x1], [f(x0), f(x1)], "o-", color=RED, ms=3.5, lw=1, label="chord on $[0.66,0.98]$")
    ax.plot(m, f(m), "o", color="black", ms=4, label="$x=0.82$")
    ax.set(xlabel="$x$", ylabel="$|\\zeta(x+0.5i)|^2$", title="(a) the slice at height $\\gamma=0.5$")
    ax.legend(loc="upper left", fontsize=6.8)
    ax = axes[1]
    xz = np.linspace(x0, x1, 200)
    gap = np.array([f(x) - chord(x) for x in xz])
    ax.plot(xz, gap, color=BLUE, lw=1.4)
    ax.fill_between(xz, 0, gap, where=gap > 0, color=RED, alpha=0.25, lw=0,
                    label="above the chord: convexity fails")
    ax.axhline(0, color=GREY, lw=0.8)
    ax.plot(m, f(m) - chord(m), "o", color="black", ms=4)
    ax.annotate("$3.00929-2.99978=%.5f$" % (f(m) - chord(m)), (m, f(m) - chord(m)),
                xytext=(0.665, 0.035), fontsize=7.5, arrowprops=dict(arrowstyle="->", lw=0.7))
    ax.set(xlabel="$x$", ylabel="$f(x)-\\mathrm{chord}(x)$",
           title="(b) a convex $f$ would stay $\\leq0$ here")
    ax.legend(loc="lower right", fontsize=6.8)
    fig.tight_layout()
    save(fig, "same_height_convexity")


# ------------------------------------------------------------------- HEF
def hef_figures(mu):
    mp.mp.dps = 30

    def Phi(u):
        return mp.fsum((2 * mp.pi**2 * n**4 * mp.exp(9 * u) - 3 * mp.pi * n**2 * mp.exp(5 * u))
                       * mp.exp(-mp.pi * n**2 * mp.exp(4 * u)) for n in range(1, 12))

    us = np.linspace(0, 0.8, 321)
    ph = np.array([float(Phi(u)) for u in us])
    fig, axes = plt.subplots(1, 2, figsize=(7.0, 2.8))
    ax = axes[0]
    for t, col in ((-20, PURPLE), (-10, BLUE), (0, "black"), (10, GREEN), (20, AMBER)):
        ax.plot(us, ph * np.exp(t * us**2), color=col, lw=1.6 if t == 0 else 1.0,
                label=f"$t={t:+d}$" if t else "$t=0$ ($\\Xi$)")
    ax.set(xlabel="$u$", ylabel="$\\Phi(u)e^{tu^2}$", title="(a) heat-flow deformation of the kernel")
    ax.legend(fontsize=6.8)
    ax = axes[1]
    ax.semilogy(us, ph, color="black", lw=1.4)
    ax.set(xlabel="$u$", ylabel="$\\Phi(u)$ (log scale)", title="(b) $\\Phi>0$ with double-exponential decay")
    ax.set_ylim(1e-60, 10)
    fig.tight_layout()
    save(fig, "hef_kernel_flow")

    # Classical (factorial-normalized) Jensen polynomials and their Hermite limit.
    gam = [mp.factorial(n) * mu[n] for n in range(len(mu))]
    fig, axes = plt.subplots(1, 3, figsize=(7.2, 2.7), sharey=True)
    worst_imag = 0.0
    for ax, d in zip(axes, (3, 5, 8)):
        H = np.sort(np.polynomial.hermite.hermroots([0] * d + [1]))
        H = (H - H.mean()) / H.std()
        nmax = len(mu) - d - 1
        ns = np.arange(0, nmax + 1)
        roots = []
        for n in ns:
            coeffs = [mp.binomial(d, j) * gam[n + j] for j in range(d, -1, -1)]
            r = mp.polyroots(coeffs, maxsteps=200, extraprec=200)
            worst_imag = max(worst_imag, max(float(abs(mp.im(z)) / (abs(z) + 1e-300)) for z in r))
            x = np.sort([float(mp.re(z)) for z in r])
            roots.append((x - x.mean()) / x.std())
        roots = np.array(roots)
        for i in range(d):
            ax.plot(ns, roots[:, i], color=BLUE, lw=1)
            ax.axhline(H[i], color=RED, lw=0.7, ls="--")
        ax.set(xscale="log", xlabel="shift $n+1$", title=f"degree $d={d}$")
    axes[0].set_ylabel("standardized real roots")
    axes[0].plot([], [], color=BLUE, label="roots of $J^{\\rm cl}_{d,n}$")
    axes[0].plot([], [], color=RED, ls="--", label="Hermite $H_d$ zeros")
    axes[0].legend(loc="lower left", fontsize=6.3)
    fig.tight_layout()
    save(fig, "hef_hermite_limit")
    return worst_imag


def main(names):
    every = ["frontier", "order3", "turan", "weil", "same", "hef"]
    names = names or every
    mu = load_mu(200) if {"order3", "turan", "hef"} & set(names) else None
    report = {}
    if "frontier" in names:
        frontier_map("reduction_frontier_map", conditional_pf58=True)
        frontier_map("two_routes_frontier_map", conditional_pf58=False)
    if "order3" in names:
        report["order3_slope"] = order3_gap(mu)
    if "turan" in names:
        report["turan_negative_of_feasible"] = turan_landscape(mu)
    if "weil" in names:
        report["weil"] = weil_figures()
    if "same" in names:
        same_height_figures()
    if "hef" in names:
        report["hef_max_relative_imag_root"] = hef_figures(mu)
    print(json.dumps(report, indent=1, default=str))


if __name__ == "__main__":
    main(sys.argv[1:])
