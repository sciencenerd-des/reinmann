"""
Generate publication-quality figures for the RH reduction report.

Foreign-tool evidence (numerics on Riemann's xi) for the machine-checked reduction
  RH  <=>  for all k,m:  0 <= det[ mu_{m+i-j} ]   (Polya-frequency / Toeplitz TP),
mu_n = (-1)^n b_n,  b_n = [t^{2n}] xi(1/2+it),
xi(s) = (s(s-1)/2) pi^{-s/2} Gamma(s/2) zeta(s).

Outputs PNGs into research/figures/.
"""

import os
import mpmath as mp
import numpy as np
import matplotlib as mpl
import matplotlib.pyplot as plt

mp.mp.dps = 80
N = 12
KMAX = 6
OUT = os.path.join(os.path.dirname(__file__), "..", "research", "figures")
os.makedirs(OUT, exist_ok=True)

mpl.rcParams.update({
    "figure.dpi": 150, "savefig.dpi": 150, "font.size": 11,
    "axes.titlesize": 13, "axes.titleweight": "bold", "axes.grid": True,
    "grid.alpha": 0.3, "axes.spines.top": False, "axes.spines.right": False,
    "figure.facecolor": "white", "axes.facecolor": "white",
    "font.family": "DejaVu Sans",
})
ACCENT = "#2A6FDB"; ACCENT2 = "#D7263D"; GREEN = "#1B998B"; GREY = "#5c5c5c"


def xi(s):
    return (s * (s - 1) / 2) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


print("computing xi Taylor coefficients (dps=%d) ..." % mp.mp.dps)
coeffs = mp.taylor(lambda t: xi(mp.mpf("0.5") + 1j * t), 0, 2 * N + 1)
b = [coeffs[2 * n].real for n in range(N + 1)]
mu = [((-1) ** n) * b[n] for n in range(N + 1)]


def toeplitz_minor(seq, k, m):
    A = mp.zeros(k, k)
    for i in range(k):
        for j in range(k):
            idx = m + i - j
            A[i, j] = seq[idx] if 0 <= idx < len(seq) else mp.mpf(0)
    return mp.det(A)


# ---------------------------------------------------------------- Figure 1
fig, ax = plt.subplots(1, 2, figsize=(11, 4.2))
ns = list(range(N + 1))
ax[0].semilogy(ns, [abs(float(b[n])) for n in ns], "o-", color=ACCENT, label=r"$|b_n|$")
ax[0].set_xlabel("n"); ax[0].set_ylabel(r"$|b_n|$  (log scale)")
ax[0].set_title(r"(a) $\xi$ Taylor coefficients: factorial decay")
ax[0].legend(frameon=False)
signs = [1 if b[n] > 0 else -1 for n in ns]
ax[1].stem(ns, signs, basefmt=" ", linefmt=GREY, markerfmt="o")
ax[1].set_ylim(-1.6, 1.6); ax[1].set_yticks([-1, 1]); ax[1].set_yticklabels(["−", "+"])
ax[1].set_xlabel("n"); ax[1].set_title(r"(b) sign of $b_n$  ($\mu_n=(-1)^n b_n>0$)")
fig.tight_layout(); fig.savefig(os.path.join(OUT, "fig1_coefficients.png")); plt.close(fig)
print("fig1 done")

# ---------------------------------------------------------------- Figure 2
R = [float(mu[n + 1] ** 2 / (mu[n] * mu[n + 2])) for n in range(N - 1)]
inv_s = [float(((2 * n + 1) * (2 * n + 2)) / mp.mpf((2 * n + 3) * (2 * n + 4))) for n in range(N - 1)]
s = [float(((2 * n + 3) * (2 * n + 4)) / mp.mpf((2 * n + 1) * (2 * n + 2))) for n in range(N - 1)]
xs = list(range(N - 1))
fig, ax = plt.subplots(1, 2, figsize=(11, 4.2))
ax[0].plot(xs, R, "o-", color=ACCENT, label=r"$R_n=\mu_{n+1}^2/(\mu_n\mu_{n+2})$")
ax[0].plot(xs, inv_s, "s--", color=ACCENT2, label=r"slack threshold $1/s_n$")
ax[0].axhline(1.0, color=GREY, lw=1, ls=":")
ax[0].fill_between(xs, inv_s, R, color=GREEN, alpha=0.18, label="Turán margin")
ax[0].set_xlabel("n"); ax[0].set_title("(a) Order-2 Turán: ratio vs slack threshold")
ax[0].legend(frameon=False, fontsize=9)
ax[0].annotate(r"$R_n>1$: $\mu$ log-concave", (xs[3], R[3]), (xs[3] + 1, R[3] + 0.4),
               arrowprops=dict(arrowstyle="->", color=GREY), fontsize=9, color=GREY)
ax[1].plot(xs, s, "o-", color=GREEN)
ax[1].axhline(1.0, color=GREY, lw=1, ls=":")
ax[1].set_xlabel("n"); ax[1].set_ylabel(r"$s_n$")
ax[1].set_title(r"(b) slack factor $s_n=\frac{(2n+3)(2n+4)}{(2n+1)(2n+2)}\downarrow 1$")
fig.tight_layout(); fig.savefig(os.path.join(OUT, "fig2_turan_margin.png")); plt.close(fig)
print("fig2 done")

# ---------------------------------------------------------------- Figure 3
grid = np.full((KMAX, N + 1), np.nan)
allpos = True
for k in range(1, KMAX + 1):
    for m in range(k - 1, N + 1):
        if m + (k - 1) <= N:
            d = toeplitz_minor(mu, k, m)
            if d <= 0:
                allpos = False
            grid[k - 1, m] = float(mp.log10(d)) if d > 0 else np.nan
fig, ax = plt.subplots(1, 2, figsize=(11, 4.4))
im = ax[0].imshow(grid, aspect="auto", origin="lower", cmap="viridis",
                  extent=[-0.5, N + 0.5, 0.5, KMAX + 0.5])
ax[0].set_xlabel("offset m"); ax[0].set_ylabel("order k")
ax[0].set_yticks(range(1, KMAX + 1))
ax[0].set_title("(a) $\\log_{10}\\det[\\mu_{m+i-j}]$  (all entries > 0)")
plt.colorbar(im, ax=ax[0], label=r"$\log_{10}$ of minor")
# leading contiguous principal minors normalized by diagonal entry
ks = list(range(1, KMAX + 1))
norm = []
for k in ks:
    m = k - 1
    d = toeplitz_minor(mu, k, m)
    norm.append(float(mp.log10(d / mu[m] ** k)))
ax[1].plot(ks, norm, "o-", color=ACCENT)
ax[1].set_xlabel("order k"); ax[1].set_ylabel(r"$\log_{10}(\det_k/\mu_m^{\,k})$")
ax[1].set_title("(b) scale-normalized principal minors (> 0 at all orders)")
fig.tight_layout(); fig.savefig(os.path.join(OUT, "fig3_toeplitz_minors.png")); plt.close(fig)
print("fig3 done; all minors positive:", allpos)

# ---------------------------------------------------------------- Figure 4
fig, ax = plt.subplots(1, 2, figsize=(11, 4.2))
colors = {2: ACCENT, 3: GREEN, 4: ACCENT2}
for d in (2, 3, 4):
    maxim = []
    nn = list(range(0, N - d + 1))
    for n in nn:
        cef = [mp.binomial(d, k) * b[n + k] for k in range(d + 1)]
        roots = mp.polyroots(list(reversed(cef)), maxsteps=300, extraprec=300)
        maxim.append(float(max(abs(r.imag) for r in roots)) + 1e-300)
    ax[0].semilogy(nn, maxim, "o-", color=colors[d], label=f"d={d}")
ax[0].set_xlabel("shift n"); ax[0].set_ylabel(r"$\max|\mathrm{Im}\ \mathrm{root}|$")
ax[0].set_title("(a) Jensen polynomials hyperbolic (roots real)")
ax[0].legend(frameon=False)
# scatter of roots for a sample
for d, off in zip((2, 3, 4), (0, 0, 0)):
    cef = [mp.binomial(d, k) * b[off + k] for k in range(d + 1)]
    roots = mp.polyroots(list(reversed(cef)), maxsteps=300, extraprec=300)
    re = [float(r.real) for r in roots]; im = [float(r.imag) for r in roots]
    ax[1].scatter(re, im, s=60, color=colors[d], label=f"d={d}, n={off}", zorder=3)
ax[1].axhline(0, color=GREY, lw=1)
ax[1].set_xlabel("Re(root)"); ax[1].set_ylabel("Im(root)")
ax[1].set_title("(b) Jensen roots lie on the real axis")
ax[1].legend(frameon=False, fontsize=9)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "fig4_jensen_hyperbolic.png")); plt.close(fig)
print("fig4 done")

print("All figures written to", os.path.abspath(OUT))
