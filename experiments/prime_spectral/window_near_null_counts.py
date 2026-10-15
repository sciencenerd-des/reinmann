import sys
sys.path.insert(0, '.')
from flint import arb, acb_mat, ctx
from closed_weil import entry_closed
from weil_matrix import prime_powers
ctx.prec = int(sys.argv[3])
C = sys.argv[1]; N = int(sys.argv[2])
L = arb(C).log(); c = float(C)
pw = [(q,p) for q,p in prime_powers(int(c)) if q < c]
idx = list(range(-N, N+1)); d = len(idx)
M = [[None]*d for _ in range(d)]
for a in range(d):
    for b in range(a, d):
        M[a][b] = M[b][a] = entry_closed(idx[a], idx[b], L, pw, terms=60).mid()
ev = sorted(float(e.real.mid()) for e in acb_mat(M).eig(algorithm="approx"))
import math
print('%5s N%d 2C-7/4=%.2f  n<1e-3:%d n<1e-2:%d n<0.1:%d n<0.3:%d | plunge:%s' % (C, N, 2*c-1.75,
  sum(e<1e-3 for e in ev), sum(e<1e-2 for e in ev), sum(e<0.1 for e in ev), sum(e<0.3 for e in ev),
  ' '.join('%.3g'%e for e in ev if 1e-5 < e < 1.0)), flush=True)
