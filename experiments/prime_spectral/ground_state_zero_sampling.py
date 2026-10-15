import sys, json, math, cmath
sys.path.insert(0, '.')
from flint import arb, acb, acb_mat, ctx
from closed_weil import entry_closed
from weil_matrix import prime_powers
ctx.prec = 1000
C = sys.argv[1]; N = int(sys.argv[2]); c = float(C)
L = (arb(int(round(c*100)))/100).log(); Lf = float(L)
pw = [(q,p) for q,p in prime_powers(int(c)) if q < c]
idx = list(range(-N, N+1)); d = len(idx)
M = acb_mat(d, d)
for a in range(d):
    for b in range(a, d):
        v = entry_closed(idx[a], idx[b], L, pw, terms=60).mid()
        M[a, b] = v; M[b, a] = v
E, R = M.eig(right=True, algorithm="approx")
order = sorted(range(d), key=lambda i: float(E[i].real.mid()))
zs = json.load(open(sys.argv[3]))
import mpmath as mp
mp.mp.dps = 60
CO = {}
def coeffs(i):
    if i not in CO:
        col = order[i]
        CO[i] = [mp.mpc(R[r, col].real.mid().str(60, radius=False), R[r, col].imag.mid().str(60, radius=False)) for r in range(d)]
    return CO[i]
def Fhat(i, t):
    cs = coeffs(i)
    s = mp.mpc(0)
    for r, k in enumerate(idx):
        ck = cs[r]
        w = 2*mp.pi*k/Lf - t
        e = (mp.expj(w*Lf) - 1)/(1j*w) if abs(w) > 1e-30 else mp.mpf(Lf)
        s += ck*e/mp.sqrt(Lf)
    return s
for i in (0, 1):
    print('eigen', i, float(E[order[i]].real.mid()), ' window 2piC = %.1f' % (2*math.pi*c))
    ref = max(abs(Fhat(i, t)) for t in [0.5*j for j in range(0, 400)])
    row = []
    for g in zs[:16]:
        row.append('%.1f:%.1e' % (g, float(abs(Fhat(i, g))/ref)))
    mids = ['%.1f:%.1e' % ((a+b)/2, float(abs(Fhat(i, (a+b)/2))/ref)) for a, b in zip(zs[:8], zs[1:9])]
    print('  |F(gamma)|/max :', ' '.join(row))
    print('  midpoints      :', ' '.join(mids))
