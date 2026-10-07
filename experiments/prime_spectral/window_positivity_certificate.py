#!/usr/bin/env python3
"""Certified positivity of the semilocal Weil form on a window.

Window: test functions f on [0, L] (L = log C), i.e. supported in
[C^{-1/2}, C^{1/2}] multiplicatively. With F(t) = int_0^L f(x) e^{-itx} dx,

    Q(f) = Pole(f) + (1/2pi) int_R |F(t)|^2 Psi(t) dt,
    Psi(t) = Re psi(1/4 + it/2) - log pi - sum_{n<C} 2 Lambda(n) n^{-1/2} cos(t log n),
    Pole(f) = 2 Re( alpha_{+}(f) conj alpha_{-}(f) ),  alpha_s(f) = int_0^L f e^{s x/2 * 2}...

(precisely alpha_s(f) = int_0^L f(x) e^{s x} dx with s = +-1/2). This is the
repository's matrix A(C) written in frequency form; experiments/prime_spectral
closed_weil.py gives the same entries (checked to ~1e-10 in development).

Proof chain (every step is enclosed in Arb ball arithmetic):

1. Re psi(1/4 + i y) increases in |y| (series), so for |t| >= T
   Psi(t) >= beta := Psi_R(T) - A_L > 0, where A_L = sum 2 Lambda(n) n^{-1/2}.
   Hence Q(f) >= R(f) := Pole(f) + (1/2pi) int_{|t|<T} |F|^2 (Psi - beta) + beta ||f||^2.
2. Legendre basis p_n(x) = sqrt((2n+1)/L) P_n(2x/L - 1) of L^2[0, L], with
   p_n^(t) = sqrt((2n+1) L) e^{-itL/2} (-i)^n j_n(tL/2). The block n <= N is
   assembled by panel Gauss-Legendre quadrature with rigorous Arb nodes and
   weights. The Bernstein-ellipse error bound (Trefethen) is added to each
   entry as a ball radius.
3. A ball LDL^T certifies R_NN - lambda0 I > 0 (even and odd blocks decouple).
4. Tails, via |j_n(x)| <= x^n/(2n+1)!! and |i_n(x)| <= x^n/(2n+1)!! e^{x^2/(2(2n+3))}:
   R(f) >= (min(lambda0, beta - eps_D) - eps_B) ||f||^2 for all f in L^2[0, L].

Usage: window_positivity_certificate.py --L 1.163 --T 100 --N 140 --out cert.json
L is a decimal or rational giving log C exactly. Requires python-flint==0.8.0.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

from flint import acb, arb, arb_mat, ctx


def rat(s: str) -> Fraction:
    return Fraction(s)


def arb_q(q: Fraction) -> arb:
    return arb(q.numerator) / q.denominator


def prime_power_weights(L: arb):
    """All (n, Lambda(n) n^{-1/2}, log n) with 1 < n and log n < L (decided in Arb)."""
    bound = int(L.exp().upper().floor().unique_fmpz()) + 1
    out = []
    for p in range(2, bound + 1):
        if any(p % q == 0 for q in range(2, int(p ** 0.5) + 1)):
            continue
        a, n = 1, p
        while True:
            ln = a * arb(p).log()
            if ln < L:
                out.append((n, arb(p).log() / arb(n).sqrt(), ln))
            elif not (ln > L):
                raise ArithmeticError(f"cannot decide log {n} vs L")
            else:
                break
            a, n = a + 1, n * p
    return out


def digamma_shifted(z, K=12):
    """psi(z) = psi(z+K) - sum_{k<K} 1/(z+k): tight enclosures for small Re z."""
    v = acb.digamma(z + K)
    for k in range(K):
        v -= 1 / (z + k)
    return v


def psi_R(t):
    """Re psi(1/4 + it/2) - log pi, analytically continued in t."""
    q = acb(1) / 4
    return (digamma_shifted(q + acb(0, 1) * t / 2) + digamma_shifted(q - acb(0, 1) * t / 2)) / 2 - acb(arb.pi()).log()


def psi_full(t, weights):
    v = psi_R(t)
    for _, w, ln in weights:
        v -= 2 * w * (ln * t).cos()
    return v


def sph_j_series(n: int, z: arb) -> arb:
    """j_n(z) = z^n/(2n+1)!! * sum_k (-z^2/2)^k / (k! (2n+3)(2n+5)...(2n+2k+1)).

    The alternating tail is bounded once the term ratio drops below 1/2."""
    with ctx.workprec(ctx.prec + 256):
        return _sph_j_series(n, z)


def _sph_j_series(n: int, z: arb) -> arb:
    lead = z ** n / double_factorial_odd(n)
    s, t, k = arb(1), arb(1), 0
    while True:
        k += 1
        t = t * (-(z * z) / 2) / (k * (2 * n + 2 * k + 1))
        s += t
        ratio = (z * z) / (2 * (k + 1) * (2 * n + 2 * k + 3))
        if ratio < arb(1) / 2 and abs(t) < abs(s) * arb(2) ** (-ctx.prec):
            s += arb(0, (2 * abs(t)).upper())
            return lead * s


def sph_j_table(N: int, z: arb) -> list:
    """j_0..j_N at z, each evaluated directly.

    Arb's Bessel J is used first. If its ball is wide, as happens at large
    order for some arguments, the value is recomputed from the power series
    with guard bits that cover the series cancellation (about e^{z/2}).
    Recurrences are avoided: in the oscillatory range ball arithmetic cannot
    see the error cancellation, and radii grow exponentially."""
    half = arb(1) / 2
    pref = (arb.pi() / (2 * z)).sqrt()
    out = []
    for n in range(N + 1):
        v = pref * z.bessel_j(n + half)
        if not v.rad() < arb(2) ** (-200):
            extra = int(z.upper().unique_fmpz() if False else float(z.mid())) + 256
            with ctx.workprec(ctx.prec + extra):
                v = _sph_j_series(n, z)
        out.append(v)
    return out


def rect_bound(c, a_e, b_e, weights, beta, nx=12, ny=6) -> arb:
    """Upper bound of |Psi(t) - beta| on [c-a_e, c+a_e] x [-b_e, b_e] by sub-boxes."""
    best = arb(0)
    for ix in range(nx):
        for iy in range(ny):
            xr = (2 * ix + 1 - nx) * a_e / nx
            yr = (2 * iy + 1 - ny) * b_e / ny
            box = acb(arb((c + xr).mid(), (a_e / nx).upper()), arb(yr.mid(), (b_e / ny).upper()))
            v = abs(psi_full(box, weights) - beta)
            if not v.is_finite():
                raise ArithmeticError(f"enclosure failed near t={c}")
            if v.upper() > best:
                best = arb(v.upper())
    return best


def double_factorial_odd(n: int) -> arb:
    r = arb(1)
    for k in range(1, 2 * n + 2, 2):
        r *= k
    return r


def tail_sum(Z: arb, N: int) -> arb:
    """Upper bound for s_N = sum_{n>N} (2n+1) (Z^n/(2n+1)!!)^2."""
    n = N + 1
    term = (2 * n + 1) * (Z ** n / double_factorial_odd(n)) ** 2
    r = Z ** 2 / ((2 * n + 1) * (2 * n + 3))
    if not r < arb(1) / 2:
        raise ValueError("N too small for geometric tail bound")
    return term / (1 - r)


def ldl_certify(M):
    """Rump-style verified positive definiteness of a symmetric ball matrix M.

    Factor mid(M) - s I = Lt Lt^T in point arithmetic (radii discarded), then
    bound E = M - s I - Lt Lt^T in ball arithmetic. If ||E||_F < s, every
    symmetric matrix in M satisfies M >= (s - ||E||_F) I > 0. Returns that
    certified lower bound, or None.
    """
    n = M.nrows()
    mid = [[M[i, j].mid() for j in range(n)] for i in range(n)]
    # crude lower estimate of lambda_min(mid) to choose s
    ev = sorted(e.real.mid() for e in arb_mat(mid).eig(algorithm="approx"))
    if not ev[0] > 0:
        return None
    s = arb(ev[0]) / 2
    A = [[mid[i][j] - (s if i == j else 0) for j in range(n)] for i in range(n)]
    Lt = [[arb(0)] * n for _ in range(n)]
    for j in range(n):
        d = A[j][j]
        for k in range(j):
            d = (d - Lt[j][k] * Lt[j][k]).mid()
        if not d > 0:
            return None
        Lt[j][j] = d.sqrt().mid()
        for i in range(j + 1, n):
            v = A[i][j]
            for k in range(j):
                v = (v - Lt[i][k] * Lt[j][k]).mid()
            Lt[i][j] = (v / Lt[j][j]).mid()
    # Exact per-entry dot products: arb_mat multiplication loses accuracy on
    # matrices with a huge dynamic range (rigorous but very loose enclosures).
    fro = arb(0)
    for i in range(n):
        for j in range(i + 1):
            p = arb(0)
            for k in range(j + 1):
                p += Lt[i][k] * Lt[j][k]
            e = M[i, j] - (s if i == j else 0) - p
            u = arb(abs(e).upper())
            fro += u * u if i == j else 2 * u * u
    fro = arb(fro.upper()).sqrt()
    margin = s - fro
    if not margin > 0:
        print(f"verified Cholesky failed: s={s.str(5)} ||E||_F={fro.str(5)}", file=sys.stderr)
        return None
    return margin


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", required=True, help="log C, exact decimal or rational")
    ap.add_argument("--T", required=True, type=int)
    ap.add_argument("--N", required=True, type=int)
    ap.add_argument("--h", default="1/2", help="panel width")
    ap.add_argument("--rho", default="3", help="Bernstein ellipse parameter")
    ap.add_argument("--nq", type=int, default=36, help="Gauss nodes per panel")
    ap.add_argument("--prec", type=int, default=320)
    ap.add_argument("--lambda-fraction", default="1/2")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    ctx.prec = a.prec
    t0 = time.time()

    Lq, hq, rhoq = rat(a.L), rat(a.h), rat(a.rho)
    L, h, rho = arb_q(Lq), arb_q(hq), arb_q(rhoq)
    T, N, nq = a.T, a.N, a.nq
    weights = prime_power_weights(L)
    A_L = sum((2 * w for _, w, _ in weights), arb(0))
    beta = psi_R(acb(T)).real - A_L
    if not beta > 0:
        sys.exit(f"beta not positive: {beta}")

    # ---- quadrature nodes (rigorous Gauss-Legendre) and ellipse error bound
    gl = [arb.legendre_p_root(nq, k, weight=True) for k in range(nq)]
    npan = int(Fraction(T) / hq)
    if Fraction(npan) * hq != Fraction(T):
        sys.exit("T must be a multiple of h")
    a_e = h / 2 * (rho + 1 / rho) / 2
    b_e = h / 2 * (rho - 1 / rho) / 2
    if not b_e < arb(1) / 2:
        sys.exit("ellipse reaches digamma poles")
    gauss_factor = arb(64) / 15 * rho ** (-2 * nq) / (rho ** 2 - 1)
    bess_ell = (b_e * L / 2).exp()          # |j_n(z)| <= e^{|Im z|}
    E_q = arb(0)                            # sum over panels of the per-panel error / |weights|
    nodes, wts = [], []
    for k in range(npan):
        lo = h * k
        c = lo + h / 2
        Mpsi = rect_bound(c, a_e, b_e, weights, beta)
        E_q += h / 2 * gauss_factor * Mpsi.upper() * bess_ell ** 2
        for x, w in gl:
            nodes.append(c + h / 2 * x)
            wts.append(h / 2 * w)
    Q = len(nodes)

    # ---- Bessel table j_n(t L / 2), n = 0..N, by direct evaluation
    half = arb(1) / 2
    J = [[None] * Q for _ in range(N + 1)]
    for q, t in enumerate(nodes):
        col = sph_j_table(N, t * L / 2)
        for n in range(N + 1):
            J[n][q] = col[n]
    WPsi = [wts[q] * (psi_full(acb(nodes[q]), weights).real - beta) for q in range(Q)]

    # ---- pole vectors e_{s,n} = sqrt((2n+1) L) e^{sL/2} i_n(sL/2)
    def i_sph(n, x):
        return (arb.pi() / (2 * x)).sqrt() * x.bessel_i(n + half) if x > 0 else \
            (-1) ** n * (arb.pi() / (2 * (-x))).sqrt() * (-x).bessel_i(n + half)
    ep = [((2 * n + 1) * L).sqrt() * (L / 4).exp() * i_sph(n, L / 4) for n in range(N + 1)]
    em = [((2 * n + 1) * L).sqrt() * (-L / 4).exp() * i_sph(n, -L / 4) for n in range(N + 1)]

    blocks = {}
    lam_cert = None
    for par in (0, 1):
        idx = [n for n in range(N + 1) if n % 2 == par]
        d = len(idx)
        Jp = arb_mat([[J[n][q] for q in range(Q)] for n in idx])
        JW = arb_mat([[J[n][q] * WPsi[q] for q in range(Q)] for n in idx])
        G = JW * Jp.transpose()
        R = arb_mat(d, d)
        for i, m in enumerate(idx):
            for j, n in enumerate(idx):
                scale = L / arb.pi() * ((2 * m + 1) * (2 * n + 1)) ** half
                sign = 1 if ((m - n) // 2) % 2 == 0 else -1
                val = scale * sign * (G[i, j] + arb(0, (E_q).upper()))
                val += em[m] * ep[n] + ep[m] * em[n]
                if i == j:
                    val += beta
                R[i, j] = val
        rmax = max(((R[i, j].rad(), i, j) for i in range(d) for j in range(d)), key=lambda x: x[0])
        print(f"parity {par}: max entry radius {rmax[0].str(3)} at {rmax[1:]} ; E_q {E_q.str(3)} ; G rad there {G[rmax[1], rmax[2]].rad().str(3)}", file=sys.stderr)
        bad = [(i, j) for i in range(d) for j in range(d) if not R[i, j].is_finite()]
        if bad:
            print(f"non-finite entries in parity {par}: {bad[:6]} ... ({len(bad)})", file=sys.stderr)
            print("sample:", R[bad[0][0], bad[0][1]], "G:", G[bad[0][0], bad[0][1]], "ep/em:", ep[idx[bad[0][0]]], em[idx[bad[0][0]]], file=sys.stderr)
        ev = sorted(e.real.mid() for e in arb_mat([[R[i, j].mid() for j in range(d)] for i in range(d)]).eig(algorithm="approx"))
        lam0 = arb(ev[0]) * arb_q(rat(a.lambda_fraction))
        shifted = arb_mat([[R[i, j] - (lam0 if i == j else 0) for j in range(d)] for i in range(d)])
        piv = ldl_certify(shifted)
        blocks[par] = {"dim": d, "approx_lambda_min": ev[0].str(8), "approx_lambda_2": ev[1].str(8),
                       "lambda0_certified": lam0.str(8), "ldl_ok": piv is not None,
                       "min_pivot": None if piv is None else piv.str(5)}
        if piv is None:
            print(json.dumps(blocks, indent=1)); sys.exit("LDL certification failed")
        lam_cert = lam0 if lam_cert is None or lam0 < lam_cert else lam_cert

    # ---- tail and coupling bounds
    Z = arb(T) * L / 2
    sN = tail_sum(Z, N)
    psiR0 = psi_R(acb(0)).real
    M_T = (abs(psiR0) if abs(psiR0) > abs(beta + A_L) else abs(beta + A_L)) + A_L + beta
    x = L / 4
    E_gt = (L * tail_sum(x, N) * (x ** 2 / (2 * N + 5)).exp()).sqrt() * (L / 4).exp()
    E_le = max((sum((ep[n] ** 2 for n in range(N + 1)), arb(0))).sqrt().upper(),
               (sum((em[n] ** 2 for n in range(N + 1)), arb(0))).sqrt().upper())
    eps_D = M_T * arb(T) / arb.pi() * L * sN + 2 * E_gt ** 2
    eps_B = M_T * (arb(T) / arb.pi() * L * sN).sqrt() + 2 * E_le * E_gt
    final = (lam_cert if lam_cert < beta - eps_D else beta - eps_D) - eps_B
    ok = final > 0

    out = {
        "status": "certified" if ok else "not_certified",
        "statement": ("Q(f) >= c ||f||^2 for every f in L^2[0, L] with "
                      "int |F|^2 log(2+|t|) dt < infinity (Weil form on [C^{-1/2}, C^{1/2}], C = e^L)"),
        "L": a.L, "C_approx": L.exp().str(12),
        "prime_powers": [n for n, _, _ in weights], "A_L": A_L.str(10),
        "T": T, "beta": beta.str(10), "N": N, "panels": npan, "nodes": Q,
        "nq": nq, "rho": a.rho, "h": a.h, "quadrature_error_per_entry_unscaled": E_q.str(5),
        "blocks": blocks, "M_T": M_T.str(6), "s_N": sN.str(5),
        "eps_D": eps_D.str(5), "eps_B": eps_B.str(5),
        "c_lower_bound": final.str(8), "prec_bits": a.prec, "python_flint": "0.8.0",
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "seconds": round(time.time() - t0, 1),
        "trust_boundary": "FLINT/Arb ball arithmetic and the written proof chain; not a Lean certificate.",
    }
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(json.dumps(out, indent=1))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
