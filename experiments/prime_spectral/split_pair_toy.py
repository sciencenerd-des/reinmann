# Toy test: F(z)=prod_k (1+z/a_k) * (1+z/w)(1+z/conj w), a_k=k^2 (k=1..60), |w|=R between a_10 and a_11.
# D_{r,s} = det(mu_{s+i-j})_{r x r} = det(h_{r+i-j})_{s x s}, h_n=[z^n] 1/F(-z).
# Prediction: s* = 11 (pair splits the modulus ordering) oscillates in sign with period 2*pi/phi in r;
# neighbouring shifts stay positive.
import mpmath as mp
mp.mp.dps = 2600
K, R, phi, NMAX = 60, mp.mpf('110.25'), mp.mpf('0.05'), 900
xs = [mp.mpf(1)/(k*k) for k in range(1, K+1)]
w = R*mp.expj(phi); xs_c = [1/w, 1/mp.conj(w)]
h = [mp.mpf(1)] + [mp.mpf(0)]*NMAX
for x in xs + xs_c:                      # multiply by 1/(1-xz)
    for n in range(1, NMAX+1):
        h[n] = h[n] + x*h[n-1]
h = [mp.re(v) for v in h]
def D(r, s):
    M = mp.matrix(s, s)
    for i in range(s):
        for j in range(s):
            k = r+i-j
            M[i, j] = h[k] if 0 <= k <= NMAX else 0
    return mp.det(M)
for s in (10, 11, 12):
    signs = ''.join('+' if D(r, s) > 0 else '-' for r in range(20, 880, 10))
    print('s=%d' % s, signs, flush=True)
print('predicted period in r: %.1f' % float(2*mp.pi/phi))
