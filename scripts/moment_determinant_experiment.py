"""
Experimental attack on the moment-determinant ladder (foreign tool: numerics).

Verified reduction (Reinmann/XiMomentKernel.lean):
  RH  <=>  for all k,m:  0 <= det[ mu_{m+i-j} ]   (Polya-frequency / Toeplitz TP)
where mu_n = (-1)^n * b_n, b_n = [t^{2n}] Xi_R(t), Xi_R(t) = xi(1/2 + i t),
xi(s) = (s(s-1)/2) pi^{-s/2} Gamma(s/2) zeta(s).

This script computes the actual xi Taylor coefficients to high precision and tests:
  (1) order-1: mu_n > 0  (must hold from Phi>0);
  (2) order-2 Turan and the slack margin;
  (3) contiguous Toeplitz minors det[mu_{m+i-j}] for k=1..K  (the PF ladder);
  (4) Jensen polynomial hyperbolicity for d=2,3,4 (all real roots).

It reports MARGINS, to locate where the inequalities are tight (the analytic frontier).
"""

import mpmath as mp

mp.mp.dps = 80
N = 12           # compute b_0 .. b_N
KMAX = 6         # Toeplitz minors up to this order
DMAX = 4         # Jensen polynomials up to this degree


def xi(s):
    return (s * (s - 1) / 2) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


# Taylor coefficients c_k of f(t) = xi(1/2 + i t); b_n = c_{2n} (real, even fn).
f = lambda t: xi(mp.mpf("0.5") + 1j * t)
coeffs = mp.taylor(f, 0, 2 * N + 1)
b = [coeffs[2 * n].real for n in range(N + 1)]
mu = [((-1) ** n) * b[n] for n in range(N + 1)]

print("=== xi Taylor data (dps=%d) ===" % mp.mp.dps)
for n in range(N + 1):
    print(f"  b[{n:2d}] = {mp.nstr(b[n], 8):>14}   mu[{n:2d}] = {mp.nstr(mu[n], 8):>14}")

print("\n=== (1) order-1 minors: mu_n > 0 ? ===")
print("  all positive:", all(mu[n] > 0 for n in range(N + 1)))

print("\n=== (2) order-2 Turan  mu_{n+1}^2 >= mu_n mu_{n+2}, with slack ===")
print("  n :   ratio R_n = mu_{n+1}^2/(mu_n mu_{n+2})   threshold 1/s_n   margin R_n-1/s_n")
for n in range(N - 1):
    R = mu[n + 1] ** 2 / (mu[n] * mu[n + 2])
    s = ((2 * n + 3) * (2 * n + 4)) / mp.mpf((2 * n + 1) * (2 * n + 2))
    thr = 1 / s
    print(f"  {n:2d}:   R={mp.nstr(R,10):>13}   1/s={mp.nstr(thr,10):>13}   margin={mp.nstr(R-thr,6):>11}  {'OK' if R>=thr else 'FAIL'}")


def toeplitz_minor(seq, k, m):
    A = mp.zeros(k, k)
    for i in range(k):
        for j in range(k):
            idx = m + i - j
            A[i, j] = seq[idx] if 0 <= idx < len(seq) else mp.mpf(0)
    return mp.det(A)


print("\n=== (3) contiguous Toeplitz minors det[mu_{m+i-j}]  (PF ladder) ===")
for k in range(1, KMAX + 1):
    row = []
    for m in range(k - 1, k - 1 + 5):
        if m + (k - 1) <= N:
            d = toeplitz_minor(mu, k, m)
            row.append((m, d))
    cells = "  ".join(f"m={m}:{mp.nstr(d,4)}({'+' if d>0 else '-' if d<0 else '0'})" for m, d in row)
    print(f"  k={k}: {cells}")


def jensen_roots(d, n):
    # J_{d,n}(X) = sum_{k=0}^d C(d,k) b_{n+k} X^k ; mpmath polyroots wants high->low
    cef = [mp.binomial(d, k) * b[n + k] for k in range(d + 1)]
    cef_hl = list(reversed(cef))
    try:
        roots = mp.polyroots(cef_hl, maxsteps=200, extraprec=200)
    except Exception as e:
        return None
    return roots


print("\n=== (4) Jensen polynomial hyperbolicity (all roots real?) ===")
for d in range(2, DMAX + 1):
    print(f"  degree d={d}:")
    for n in range(0, N - d + 1):
        roots = jensen_roots(d, n)
        if roots is None:
            print(f"    n={n}: polyroots failed")
            continue
        max_im = max(abs(r.imag) for r in roots)
        print(f"    n={n:2d}: max|Im root| = {mp.nstr(max_im, 4):>12}  {'real' if max_im < mp.mpf(10)**(-20) else 'COMPLEX'}")

print("\nDone.")
