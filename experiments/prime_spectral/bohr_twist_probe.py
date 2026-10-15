#!/usr/bin/env python3
"""Bohr-twisted Weil window form: replace p^{-it} by e^{i theta_p} p^{-it}
(theta_{p^k}=k theta_p). Diagnostic only (approx eigenvalues)."""
import sys, itertools, time
sys.path.insert(0, '.')
from flint import arb, acb, acb_mat, ctx
from closed_weil import entry_closed
from weil_matrix import prime_powers
ctx.prec = 600

def arch_matrix(L, N):
    idx = list(range(-N, N+1)); d = len(idx)
    M = [[None]*d for _ in range(d)]
    for a in range(d):
        for b in range(a, d):
            M[a][b] = M[b][a] = acb(entry_closed(idx[a], idx[b], L, [], terms=60).mid())
    return idx, M

def shift_matrix(L, a, idx):
    # <e_j, T_a e_k>, e_k = exp(2 pi i k x/L)/sqrt(L) on [0,L]
    d = len(idx); T = [[None]*d for _ in range(d)]
    for r, j in enumerate(idx):
        for c, k in enumerate(idx):
            ph = (-2*acb.pi()*1j*k*a/L).exp() if False else acb(0, -2*arb.pi()*k*a/L).exp()
            if j == k:
                T[r][c] = ph*(L-a)/L
            else:
                t = acb(0, 2*arb.pi()*(k-j)*a/L).exp()
                T[r][c] = ph*(1-t)/acb(0, 2*arb.pi()*(k-j))
    return T

def setup(C, N):
    L = arb(C).log(); c = float(C)
    pw = [(q, p) for q, p in prime_powers(int(c)) if q < c]
    idx, A = arch_matrix(L, N)
    shifts = [(q, p, shift_matrix(L, arb(q).log(), idx)) for q, p in pw]
    return L, idx, A, pw, shifts

def lam(setupdata, theta):
    L, idx, A, pw, shifts = setupdata
    d = len(idx)
    M = [[A[r][c] for c in range(d)] for r in range(d)]
    for q, p, T in shifts:
        k = 0; qq = q
        while qq > 1: qq //= p; k += 1
        w = arb(p).log()/arb(q).sqrt()
        ph = acb(0, k*theta.get(p, 0.0)).exp()
        for r in range(d):
            for c in range(d):
                M[r][c] -= w*(ph*T[r][c] + (ph*T[c][r]).conjugate())
    ev = sorted(e.real.mid() for e in acb_mat(M).eig(algorithm="approx"))
    return ev[0]

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'check':
        C, N = sys.argv[2], 8
        S = setup(C, N)
        L, idx, A, pw, shifts = S
        # compare theta=0 against closed_weil with primes
        worst = 0
        for r, j in enumerate(idx):
            for c, k in enumerate(idx):
                ref = entry_closed(j, k, L, pw, terms=60).mid()
                mine = A[r][c]
                for q, p, T in shifts:
                    w = arb(p).log()/arb(q).sqrt()
                    mine -= w*(T[r][c] + T[c][r].conjugate())
                worst = max(worst, abs(float((mine - ref).real.mid())), abs(float(mine.imag.mid())))
        print('max entry mismatch', worst)
    else:
        C, N = sys.argv[2], int(sys.argv[3])
        t = time.time(); S = setup(C, N); print('setup', round(time.time()-t,1), 'pw', S[3], flush=True)
        ps = sorted({p for q, p in S[3]})
        import math
        print('theta=0', lam(S, {}).str(5), flush=True)
        grid = [0, math.pi/4, math.pi/2, 3*math.pi/4, math.pi]
        best = None
        for th in itertools.product(grid, repeat=len(ps)):
            v = lam(S, dict(zip(ps, th)))
            if best is None or v < best[0]: best = (v, th)
            print([round(x,3) for x in th], v.str(5), flush=True)
        print('MIN', best[0].str(6), best[1])
