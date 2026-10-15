import sys, json
sys.path.insert(0, '.')
from flint import arb, acb_mat, ctx
from closed_weil import entry_closed
from weil_matrix import prime_powers
ctx.prec = 500
N = 32
out = {}
for C in sys.argv[1:]:
    c = float(C); L = (arb(int(round(c*100)))/100).log()
    pw = [(q,p) for q,p in prime_powers(int(c)) if q < c]
    idx = list(range(-N, N+1)); d = len(idx)
    M = [[None]*d for _ in range(d)]
    for a in range(d):
        for b in range(a, d):
            M[a][b] = M[b][a] = entry_closed(idx[a], idx[b], L, pw, terms=60).mid()
    ev = sorted(float(e.real.mid()) for e in acb_mat(M).eig(algorithm="approx"))
    out[C] = ev[:30]
    print(json.dumps({C: ev[:30]}), flush=True)
