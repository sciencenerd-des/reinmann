import sys, math, itertools
sys.path.insert(0, '.'); sys.path.insert(0, sys.argv[0].rsplit('/',1)[0])
from bohr_twist_probe import setup, lam
from flint import arb, acb
def pole_entry(i, j, L):
    om = 2*arb.pi()*i/L; et = 2*arb.pi()*j/L
    if i == j:
        r = (arb(1)/4 - om**2)/(arb(1)/4 + om**2)**2
        return 4/L*((L/2).cosh()-1)*r
    d = arb.pi()*(i-j)
    return (2*(L/2).cosh()-2)/d*(om/(arb(1)/4+om**2) - et/(arb(1)/4+et**2))
mode, C, N = sys.argv[1], sys.argv[2], int(sys.argv[3])
Sd = setup(C, N); L, idx, A, pw, sh = Sd
ps = sorted({p for q,p in pw})
if mode == 'eps':
    print('lam0', lam(Sd, {}).str(6))
    for e in [1e-1,1e-2,1e-3,1e-4,1e-5,1e-6,1e-8,1e-10,1e-12,1e-14]:
        print('eps', e, lam(Sd, {2: e}).str(6), flush=True)
else:
    for r in range(len(idx)):
        for c in range(len(idx)):
            A[r][c] = A[r][c] - acb(pole_entry(idx[r], idx[c], L).mid())
    print('nopole theta=0', lam(Sd, {}).str(5))
    grid = [0, math.pi/4, math.pi/2, 3*math.pi/4, math.pi]
    vals = []
    for th in itertools.product(grid, repeat=len(ps)):
        v = lam(Sd, dict(zip(ps, th))); vals.append((float(v), th))
    vals.sort(); print('nopole min', vals[0], 'max', vals[-1])
