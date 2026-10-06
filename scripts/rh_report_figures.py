"""
High-precision numerical figures for the RH reduction report.

Samples the Polya-frequency / Toeplitz total-positivity premise: xi Taylor coefficients b_0..b_M for M=120
(b_120 ~ 1e-449), computed by a numerically stable Cauchy-circle extraction and
compared at two precisions (not certified), then used to test:
  (1) order-1: mu_n > 0;
  (2) order-2 Turan ratio + log-concavity over the full range;
  (3) Toeplitz / Polya-frequency minors det[mu_{m+i-j}] up to order KMAX;
  (4) Jensen polynomial hyperbolicity for d=2..DMAX.

xi(s) = (s(s-1)/2) pi^{-s/2} Gamma(s/2) zeta(s);  mu_n = (-1)^n b_n.
Outputs PNGs + research/figures/STATS.txt.
"""

import os, time
import mpmath as mp
import numpy as np
import matplotlib as mpl
import matplotlib.pyplot as plt

M       = 120     # number of coefficients b_0..b_M
KMAX    = 16      # Toeplitz minor orders
DMAX    = 6       # Jensen polynomial degrees
DPS_HI  = 620
DPS_LO  = 520
R_HI    = 33
R_LO    = 42
DPS_AN  = 120     # analysis precision (minors, roots)

OUT = os.path.join(os.path.dirname(__file__), "..", "research", "figures")
os.makedirs(OUT, exist_ok=True)

mpl.rcParams.update({
    "figure.dpi": 150, "savefig.dpi": 150, "font.size": 11,
    "axes.titlesize": 13, "axes.titleweight": "bold", "axes.grid": True,
    "grid.alpha": 0.3, "axes.spines.top": False, "axes.spines.right": False,
    "figure.facecolor": "white", "axes.facecolor": "white", "font.family": "DejaVu Sans",
})
ACCENT="#2A6FDB"; ACCENT2="#D7263D"; GREEN="#1B998B"; GREY="#5c5c5c"


def xi(s):
    return (s * (s - 1) / 2) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def coeffs_cauchy(M, dps, radius):
    mp.mp.dps = dps
    f = lambda t: xi(mp.mpf("0.5") + 1j * t)
    K = 4 * M + 16
    r = mp.mpf(radius)
    vals = [f(r * mp.expjpi(mp.mpf(2 * j) / K)) for j in range(K)]
    b = []
    for n in range(M + 1):
        k = 2 * n
        s = sum(vals[j] * mp.expjpi(mp.mpf(-2 * j * k) / K) for j in range(K))
        b.append((s / (K * r ** k)).real)
    return b


def agree(x, y):
    return 999.0 if y == 0 else float(-mp.log10(abs((x - y) / y)))


CACHE = os.path.join(OUT, f"coeffs_M{M}.txt")
if os.path.exists(CACHE):
    print("loading cached coefficients from", CACHE)
    mp.mp.dps = DPS_AN
    lines = open(CACHE).read().strip().splitlines()
    min_cert = float(lines[0].split("=")[1])
    b = [mp.mpf(s) for s in lines[1:]]
    cert = [min_cert] * (M + 1)  # Cached global agreement only; per-coefficient values unavailable.
else:
    print(f"computing b_0..b_{M} (Cauchy, dps={DPS_HI}) ...")
    t0 = time.time(); b = coeffs_cauchy(M, DPS_HI, R_HI); print("  primary  %.0fs" % (time.time() - t0))
    t0 = time.time(); b2 = coeffs_cauchy(M, DPS_LO, R_LO); print("  control  %.0fs" % (time.time() - t0))
    cert = [agree(b[n], b2[n]) for n in range(M + 1)]
    min_cert = min(cert)
    with open(CACHE, "w") as fh:
        fh.write(f"min_cert={min_cert}\n")
        for n in range(M + 1):
            fh.write(mp.nstr(b[n], 115) + "\n")
    mp.mp.dps = DPS_AN
    b = [mp.mpf(mp.nstr(b[n], 110)) for n in range(M + 1)]

mu = [((-1) ** n) * b[n] for n in range(M + 1)]

stats = []
stats.append(f"coefficients cross-precision agreement >= (not certified) {min_cert:.0f} significant digits (n=0..{M})")
stats.append(f"order-1: mu_n > 0 for all n=0..{M}: {all(mu[n] > 0 for n in range(M+1))}")
print(stats[0]); print(stats[1])


def toeplitz_minor(seq, k, m):
    A = mp.zeros(k, k)
    for i in range(k):
        for j in range(k):
            idx = m + i - j
            A[i, j] = seq[idx] if 0 <= idx < len(seq) else mp.mpf(0)
    return mp.det(A)


# ---------------- Figure 1 : coefficients to record depth
fig, ax = plt.subplots(1, 2, figsize=(11, 4.2))
ns = list(range(M + 1))
ax[0].semilogy(ns, [abs(float(b[n])) for n in ns], "-", color=ACCENT, lw=1.6)
ax[0].semilogy(ns, [abs(float(b[n])) for n in ns], ".", color=ACCENT, ms=3)
ax[0].set_xlabel("n"); ax[0].set_ylabel(r"$|b_n|$ (log scale)")
ax[0].set_title(r"(a) $\xi$ coefficients to $n=%d$  ($|b_{%d}|\approx10^{%d}$)" %
                (M, M, int(mp.floor(mp.log10(abs(b[M]))))))
ax[1].plot(ns, cert, "-", color=GREEN, lw=1.4)
ax[1].axhline(30, color=GREY, ls=":", lw=1)
ax[1].set_xlabel("n"); ax[1].set_ylabel("significant digits")
ax[1].set_title("(b) cross-precision agreement (not certification) of $b_n$")
fig.tight_layout(); fig.savefig(os.path.join(OUT, "fig1_coefficients.png")); plt.close(fig)
print("fig1 done")

# ---------------- Figure 2 : Turan / log-concavity over the full range
R = [float(mu[n + 1] ** 2 / (mu[n] * mu[n + 2])) for n in range(M - 1)]
inv_s = [float(((2*n+1)*(2*n+2)) / mp.mpf((2*n+3)*(2*n+4))) for n in range(M - 1)]
xs = list(range(M - 1))
turan_ok = all(mu[n] * mu[n + 2] <= mu[n + 1] ** 2 for n in range(M - 1))
logconc_ok = all(R[n] > 1 for n in range(M - 1))
stats.append(f"order-2 Turan holds for all n=0..{M-2}: {turan_ok}")
stats.append(f"mu log-concave (R_n>1) for all n=0..{M-2}: {logconc_ok}")
fig, ax = plt.subplots(1, 2, figsize=(11, 4.2))
ax[0].plot(xs, R, "-", color=ACCENT, lw=1.6, label=r"$R_n=\mu_{n+1}^2/(\mu_n\mu_{n+2})$")
ax[0].plot(xs, inv_s, "--", color=ACCENT2, lw=1.4, label=r"slack threshold $1/s_n$")
ax[0].axhline(1.0, color=GREY, lw=1, ls=":")
ax[0].fill_between(xs, inv_s, R, color=GREEN, alpha=0.15)
ax[0].set_xlabel("n"); ax[0].set_ylim(0, 2.3)
ax[0].set_title(r"(a) Order-2 over $n\leq%d$: $R_n>1>1/s_n$ throughout" % (M - 2))
ax[0].legend(frameon=False, fontsize=9, loc="upper right")
ax[1].semilogy(xs, [R[n] - 1 for n in xs], "-", color=ACCENT, lw=1.5, label=r"$R_n-1$ (log-concavity margin)")
ax[1].semilogy(xs, [1 - inv_s[n] for n in xs], "--", color=ACCENT2, lw=1.5, label=r"$1-1/s_n\sim 8/(2n)^2$")
ax[1].set_xlabel("n"); ax[1].set_title("(b) both margins shrink to 0 (asymptotic tie)")
ax[1].legend(frameon=False, fontsize=9)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "fig2_turan_margin.png")); plt.close(fig)
print("fig2 done")

# ---------------- Figure 3 : Polya-frequency minors to order KMAX
print("computing Toeplitz minors up to order %d ..." % KMAX)
grid = np.full((KMAX, M + 1), np.nan)
allpos = True
for k in range(1, KMAX + 1):
    for m in range(k - 1, M - (k - 1) + 1):
        d = toeplitz_minor(mu, k, m)
        if d <= 0:
            allpos = False
        if d > 0:
            grid[k - 1, m] = float(mp.log10(d))
stats.append(f"ALL contiguous Toeplitz (PF) minors orders k=1..{KMAX}, all offsets, strictly positive: {allpos}")
print("  all minors positive:", allpos)
fig, ax = plt.subplots(1, 2, figsize=(11, 4.4))
im = ax[0].imshow(grid, aspect="auto", origin="lower", cmap="viridis",
                  extent=[-0.5, M + 0.5, 0.5, KMAX + 0.5])
ax[0].set_xlabel("offset m"); ax[0].set_ylabel("order k"); ax[0].set_yticks(range(2, KMAX + 1, 2))
ax[0].set_title(r"(a) $\log_{10}\det[\mu_{m+i-j}]$ to order %d (all $>0$)" % KMAX)
plt.colorbar(im, ax=ax[0], label=r"$\log_{10}$ minor")
ks = list(range(1, KMAX + 1))
norm = [float(mp.log10(toeplitz_minor(mu, k, k - 1) / mu[k - 1] ** k)) for k in ks]
ax[1].plot(ks, norm, "o-", color=ACCENT)
ax[1].set_xlabel("order k"); ax[1].set_ylabel(r"$\log_{10}(\det_k/\mu_m^{\,k})$")
ax[1].set_title("(b) scale-normalized principal minors (sampled orders only)")
fig.tight_layout(); fig.savefig(os.path.join(OUT, "fig3_toeplitz_minors.png")); plt.close(fig)
print("fig3 done")

# ---------------- Figure 4 : Jensen hyperbolicity at scale
print("computing Jensen roots d=2..%d ..." % DMAX)
fig, ax = plt.subplots(1, 2, figsize=(11, 4.2))
cmap = plt.cm.viridis(np.linspace(0, 0.85, DMAX - 1))
worst = 0.0
for idx, d in enumerate(range(2, DMAX + 1)):
    nn = list(range(0, M - d + 1))
    maxim = []
    for n in nn:
        cef = [mp.binomial(d, k) * mp.factorial(n + k) * b[n + k] for k in range(d + 1)]
        roots = mp.polyroots(list(reversed(cef)), maxsteps=400, extraprec=400)
        mi = float(max(abs(r.imag) for r in roots)) + 1e-320
        maxim.append(mi); worst = max(worst, mi)
    ax[0].semilogy(nn, maxim, "-", color=cmap[idx], lw=1.3, label=f"d={d}")
ax[0].set_xlabel("shift n"); ax[0].set_ylabel(r"$\max|\mathrm{Im\ root}|$")
ax[0].set_title(r"(a) Numerical Jensen roots: $d\leq%d$, $n\leq%d$" % (DMAX, M - 2))
ax[0].legend(frameon=False, ncol=2, fontsize=9)
stats.append(f"Uncertified Jensen root diagnostic for d=2..{DMAX}, n=0..{M-DMAX}: worst |Im root| = {worst:.2e}")
for idx, d in enumerate(range(2, DMAX + 1)):
    cef = [mp.binomial(d, k) * mp.factorial(k) * b[k] for k in range(d + 1)]
    roots = mp.polyroots(list(reversed(cef)), maxsteps=400, extraprec=400)
    ax[1].scatter([float(r.real) for r in roots], [float(r.imag) for r in roots],
                  s=40, color=cmap[idx], label=f"d={d}", zorder=3)
ax[1].axhline(0, color=GREY, lw=1)
ax[1].set_xlabel("Re(root)"); ax[1].set_ylabel("Im(root)")
ax[1].set_title("(b) numerical sample Jensen roots")
ax[1].legend(frameon=False, fontsize=8, ncol=2)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "fig4_jensen_hyperbolic.png")); plt.close(fig)
print("fig4 done")

with open(os.path.join(OUT, "STATS.txt"), "w") as fh:
    fh.write("RH reduction: uncertified high-precision diagnostic summary\n")
    fh.write("=" * 52 + "\n")
    for s in stats:
        fh.write("- " + s + "\n")
print("\n".join(stats))
print("done.")
