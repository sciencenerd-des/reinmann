# A modulated packet theorem, with an explicit local infinite tail

This extends the [previous packet note](WINDOW_PACKET_THEOREM_2026_10_12.md): the packet is local in ordinate, its size is \(O(\log\gamma_0)\) for a fixed radius, and Turán replaces inverse-Vandermonde conditioning by an explicit partial-sum hypothesis. It does **not** establish a universal \(\Phi\). The checked scalar calculator is [localized_packet_bound.py](../../experiments/prime_spectral/localized_packet_bound.py).

## Modulation and the local count

Retain the normalized B-spline transform \(H(z)=(\sinh(az/q)/(az/q))^q\), \(q\ge2\). Modulate the physical test by \(e^{-i\gamma_0x}\). Its translated Gram kernel, after removing the harmless translation phase, is
\[
 K_{\gamma_0}(t)=\sum_\rho H(\rho-\tfrac12-i\gamma_0)^2
                    e^{t(\rho-\tfrac12-i\gamma_0)}.
\]
Full-window positivity still implies \(|K_{\gamma_0}(t)|\le Q_{\gamma_0}=K_{\gamma_0}(0)\) for \(0\le t\le S-2a\), \(S=\log C\). The weight is a complex square.

Put \(\Gamma=|\gamma_0|\ge e\), \(R\ge1\), and let \(n_{\gamma_0}(u)\) count **all** nontrivial zeta zeros, with multiplicity, in \(|\gamma-\gamma_0|\le u\). Without RH,
\[
 n_{\gamma_0}(u)\le100u\log(10(\Gamma+u+2)),\qquad u\ge1. \tag{1}
\]
Here is an explicit derivation from [Hasanalizade–Shen–Wong, Corollary 1.2](https://arxiv.org/pdf/2107.06506). Write \(N(v)=F(v)+E(v)\), \(F(v)=v\log(v/(2\pi e))/(2\pi)\), and \(|E(v)|\le0.3611\log v+9.3675\) for \(v\ge e\). If \(u<\Gamma-e\), subtract the bounds at \(\Gamma-u\) and \(\Gamma+u\), interpreting a zero at the lower endpoint by a left limit. The main term is at most \(u\log(10(\Gamma+u+2))\); the two errors are at most \(0.7222\log(10(\Gamma+u+2))+18.735\), which is less than \(99u\) times that logarithm. If \(u\ge\Gamma-e\), use \(n_{\gamma_0}(u)\le2N(\Gamma+u)\le10(\Gamma+u)\log(10(\Gamma+u))\). Since \(\Gamma+u\le2u+e<5u\), this is at most \(100u\log(10(\Gamma+u+2))\). Negative centers follow by conjugation. Thus a fixed-radius complete packet has \(O(\log\Gamma)\) elements.

## Every omitted zero is in the tail

For \(|\gamma-\gamma_0|>R\), the unconditional critical-strip bound gives
\[
 |H(\rho-\tfrac12-i\gamma_0)|^{2}
 \le(q/a)^{2q}e^a|\gamma-\gamma_0|^{-2q}.
\]
For \(u\ge R\), bound the logarithm in (1) by
\(\log(Bu)\), \(B=10(1+(\Gamma+2)/R)\). Stieltjes integration by parts, including the nonpositive lower boundary term, proves
\[
 |E_{\gamma_0}(t)|\le \mathcal T_{\rm loc}
 =(q/a)^{2q}e^{a+t/2}\,100(2q)R^{1-2q}
 \left[\frac{\log(10(\Gamma+R+2))}{2q-1}
       +\frac1{(2q-1)^2}\right]. \tag{2}
\]
The bound includes zeros just outside the packet; they are not silently absorbed into an old absolute-height tail. For fixed filter and \(R\), its ordinate dependence is logarithmic, but it still grows as \(e^{t/2}\).

## Turán in place of Vandermonde inversion

Let the complete local packet have distinct centered, modulated nodes \(z_j\), multiplicities \(d_j\), weights \(w_j=d_jH(z_j)^2\), and order the nodes by decreasing real part. Let \(b_*=\max_j\Re z_j\ge0\). For a step \(h>0\), define
\[
 A_*=\min_{1\le J\le m}\left|\sum_{j=1}^Jw_j\right|.
\]
Assume \(A_*>0\), and choose \(M\ge0\) such that \(2a+(M+m)h\le S\). Turán's second main theorem, after normalizing \(e^{hz_j}\) by its largest modulus, supplies some \(M+1\le\nu\le M+m\) with
\[
 \left|\sum_jw_j e^{\nu hz_j}\right|
 \ge2 A_*e^{b_*\nu h}
       \left(\frac{m}{8e(M+m)}\right)^m .
\]
Consequently every right-hand zero in the packet satisfies
\[
 \beta-\tfrac12\le b_*
 \le\frac{
 \log[(Q_{\gamma_0}+\mathcal T_{\rm loc}(a,q,\Gamma,R,(M+m)h))/(2A_*)]
 +m\log[8e(M+m)/m]}{(M+1)h}. \tag{3}
\]
The exact partial-sum factor is essential; see the authors' treatment in [Montgomery–Vaughan, Appendix K, Theorem K.3 and Corollary K.4](https://personal.science.psu.edu/rcv4/571s25/Vol3.pdf). It is not a lower bound in terms of a single weight for arbitrary complex coefficients.

## Why this is not the universal theorem

The local zero count and the local infinite tail are now explicit. What remains is a **joint choice of filter and support allocation** for which (i) the tail in (2) is small enough at the final translation, (ii) the ordered partial sums in (3) have a uniform lower bound, and (iii) \(Q_{\gamma_0}\) has a usable geometric-side upper bound. A small fixed filter keeps local weights close to positive multiplicities, but leaves an \(e^{t/2}\) tail; merely increasing \(S\) then recovers only a trivial horizontal bound. A stronger filter can suppress the tail but changes the phases of the complex weights. Neither property can be assumed independently.

An \(O(\log\Gamma\log\log\Gamma)\) numerator is therefore a target for these simultaneous estimates, not a proved consequence of counting \(O(\log\Gamma)\) nearby zeros.

An alternative detector is worth checking before optimizing this particular spline. [Lemke Oliver–Thorner, §4.2, Lemmas 4.2–4.4](https://lemkeoliver.github.io/papers/15-AutoLFZDE.pdf) localize logarithmic-derivative power sums, control omitted zeros dyadically, and apply an unweighted Turán inequality to reciprocal zero distances. This avoids a free complex coefficient at each node. Transferring that method here would require a compactly supported Weil test realizing the reciprocal-distance detector, with a controlled truncation error and geometric norm. The logarithmic-derivative identity alone does not supply such a test, and replacing \(H(z_j)^2\) by 1 in (3) is invalid. This is a proposed alternative construction, not a consequence of their zero-density theorem.

## Bombieri 2000 comparison

[Bombieri, Remarks on Weil's quadratic functional I](https://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0), especially §§3 and 8–13, directly studies this finite-to-infinite problem. Theorems 8–9 determine finite spectral negative indices; §§10–11 explain why negative eigenvalues can collapse to zero and limiting exponential systems can have interval dependencies. Theorem 12 supplies small-support positivity. Section 13 tests fictitious off-line zeros numerically. These are direct prior art for the packet/eigenvector program. Those sections do not supply the missing uniform estimates above; no novelty claim is made for Turán's inequality or local zero counting.
