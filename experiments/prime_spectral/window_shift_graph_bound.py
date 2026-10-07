#!/usr/bin/env python3
# Floating diagnostic (not a certificate) for CERTIFIED_WINDOW_POSITIVITY_2026_10_07.md.
"""Compare the comb supremum A_L with the per-prime window shift-graph bound.

On L^2[0,L], S_p = sum_a w_{p^a} (T_{a log p} + T_{-a log p}) acts on each orbit
x + Z log p within [0,L]. On an orbit with k points it is the weighted graph with
edge weight w_{p^a} between points at distance a. ||S_p|| = max over the possible
k of lambda_max. ||S|| <= sum_p ||S_p|| (triangle inequality across primes).
"""
import math, numpy as np
def ppowers(C):
    out=[]
    for p in range(2,int(C)+1):
        if all(p%q for q in range(2,int(p**.5)+1)):
            a=1
            while p**a < C: out.append((p,a)); a+=1
    return out
def report(C):
    L=math.log(C); A=0; sig=0; tri=0
    for p in sorted({p for p,_ in ppowers(C)}):
        lp=math.log(p); kmax=int(L//lp)+1   # max orbit size (L/lp non-integer)
        W=np.zeros((kmax,kmax))
        for (q,a) in ppowers(C):
            if q!=p: continue
            w=lp/q**(a/2); A+=2*w
            tri+=w*2*math.cos(math.pi/(max(1,int(L//(a*lp))+1)+1)) if int(L//(a*lp))+1>1 else 0
            for i in range(kmax-a): W[i,i+a]=W[i+a,i]=w
        sig+=max(np.linalg.eigvalsh(W)) if kmax>1 else 0
    # coercivity frequency: Re psi(1/4+it/2)-log(pi) ~ log(t/(2*pi))
    print(f"C={C:6.2f} L={L:.3f}  A_L={A:.3f}  triangle={tri:.3f}  per-prime={sig:.3f}  "
          f"T(A_L)~{2*math.pi*math.exp(A):9.0f}  T(per-prime)~{2*math.pi*math.exp(sig):7.0f}  ratio {math.exp(A-sig):6.1f}")
for C in (2.2,3.2,4.95,7.389,8.37,9.5,10.8,12.2,16.9,19):
    report(C)
