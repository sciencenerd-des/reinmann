# Nonzero Fourier limits force growth of the origin-normalized vector

The [coupled rank-energy law](COUPLED_RANK_SCHUR_RECURRENCE_2026_09_24.md)
suggested bounding the norm of the origin-normalized Weil ground
vector. At each *fixed* support this can help telescope coupling
energies. A bound **uniform over growing supports is incompatible with
any locally convergent, nonzero Fourier profile limit**, including the
proposed Xi limit. This note proves that restriction and corrects the
target for an all-rank budget. It neither proves profile convergence
nor RH.

## Exact Parseval identity

Use the [positive-kernel normalization](POSITIVE_KERNEL_2026_09_22.md)
on \([-L/2,L/2]\):

\[
 g(t)=c_0+2\sum_{n=1}^{N}(-1)^n c_n\cos(2\pi nt/L),
 \qquad p(t)=\frac{g(t)}{Lc_0},\qquad \int p(t)\,dt=1.
\]

The same origin-normalized vector in the orthonormal even Fourier
basis is

\[
 v=(1,\sqrt2 c_1/c_0,\ldots,\sqrt2 c_N/c_0).
\]

Cosine orthogonality gives the **exact** identity

\[
 \|v\|_2^2=1+2\sum_{n=1}^{N}(c_n/c_0)^2
             =L\int_{-L/2}^{L/2}p(t)^2\,dt.        \tag{1}
\]

Identity (1) holds even when \(g\) changes sign, provided \(c_0\ne0\).
For the Fourier profile \(P(x)=\int p(t)e^{-ixt}\,dt\), Plancherel
also gives

\[
 \|v\|_2^2=\frac{L}{2\pi}\int_{\mathbb R}|P(x)|^2\,dx. \tag{1a}
\]

Suppose \(L_j\to\infty\) and \(P_j\to F\) locally uniformly on the
real axis, with \(F(0)=1\). Continuity gives a fixed \(\delta>0\)
such that \(|F(x)|\ge3/4\) for \(|x|\le\delta\). Eventually
\(|P_j(x)|\ge1/2\) there; (1a) then yields
\(\|v_j\|_2^2\ge \delta L_j/(4\pi)\). Thus a support-uniform
origin-vector norm bound is impossible for *any* intended locally
uniform Xi profile limit, independently of kernel positivity.
For the unit ground vector \(u_j=v_j/\|v_j\|_2\), its zeroth Fourier
coordinate therefore satisfies
\(|u_{j,0}|^2\le4\pi/(\delta L_j)\). In particular, the central
coordinate cannot retain a fixed positive lower bound along that
limit. The [unit-vector strip transfer](STRIP_RESIDUAL_TRANSFER_2026_09_23.md)
must pay for this shrinking normalization; the
[origin-constrained transfer](ORIGIN_SCHUR_RESOLVENT_2026_09_24.md)
avoids that denominator but still needs a coupled resolvent estimate.

When \(g>0\), \(p\) is a probability density and positivity supplies
further effective inequalities. For any \(R>0\)
and \(m=\nu([-R,R])\), Cauchy-Schwarz on the interval of length
\(2R\) yields

\[
 \|v\|_2^2\ge \frac{Lm^2}{2R}.                 \tag{2}
\]

If a family with \(L_j\to\infty\) is tight, choose a fixed \(R\)
containing at least half its probability mass for all sufficiently
large \(j\). Then (2) forces \(\|v_j\|_2^2\ge L_j/(8R)\to\infty\).
Weak convergence to **any** probability measure, including the
proposed Xi theta measure, implies such tightness. Thus a
support-uniform constant \(K\) in the rank-energy inequality is not
merely unproved on that route: it cannot hold.

There are two explicit versions of (2). If the variance
\(V=\int t^2p(t)\,dt>0\), Chebyshev at \(R=\sqrt{5V}\) gives
\(m\ge4/5\), hence

\[
 \|v\|_2^2\ge \frac{8L}{25\sqrt{5V}}.         \tag{3}
\]

Therefore the uniform variance bound sought for quotient compactness
would itself force at least linear growth of \(\|v\|_2^2\).
Alternatively, the even positive kernel has
\(P(i)=\mathbb E\cosh T\). If \(P(i)\le M\), then
\(\Pr\{|T|>R\}\le2Me^{-R}\). Choosing \(R=\log(4M)\) gives

\[
 \|v\|_2^2\ge\frac{L}{8\log(4M)}.            \tag{4}
\]

On a path with \(N/L^2\to\infty\), the exterior grid factor tends to
one at \(i\), so a uniform one-point quotient bound \(R(i)\le M_0\)
also bounds \(P(i)=R(i)G(i)\) eventually. Equation (4) then forces
linear origin-norm growth on the very path contemplated by the
[Euler-region uniqueness gate](PRIME_EULER_REGION_UNIQUENESS_2026_09_23.md).

## Consequence for the all-rank energy law

At fixed support, the conditional bound
\(\sum q_k^*S_k^{-1}q_k\le K_C(\lambda_{N_a}-\lambda_{N_b})\)
remains valid with \(K_C=\sup_k\|v_{C,N_k}\|_2^2\), if finite.
Across growing supports on any successful local Xi profile path,
\(K_C\) must grow at least on the order of \(L=\log C\).
Consequently a support-uniform rank budget cannot be obtained by
assuming a constant \(K_C\). It needs a compensating eigenvalue-shift
rate, a weighted dual-resolvent estimate, or direct cancellation in
the coupled profile pairing. The rank-energy law does give a
scale-free *normalized energy* budget without any constant \(K_C\);
it does not yet control the profile pairing. None of those further
profile estimates is proved here.

For orientation, the existing finite certificates give these readable
values. Their coefficient and variance input enclosures are in the
linked artifacts; the table
does not assert a trend along an infinite path.

| Cutoff, modes | \(\|v\|_2^2\), approximate | Lower bound (3), approximate | Input certificates |
|:--|--:|--:|:--|
| 13, 4 | `2.379354` | `1.221958` | [Schur vector](ground_schur_13_4.json), [kernel](positive_kernel_13_4.json) |
| 13, 8 | `2.873800` | `1.472675` | [Schur vector](ground_schur_13_8.json), [kernel](positive_kernel_13_8.json) |
| 13, 16 | `3.227510` | `1.658657` | [isolated kernel](isolated_kernel_13_16.json) |
| 23, 16 | `3.620107` | `1.854049` | [isolated kernel](isolated_kernel_23_16.json) |

The Parseval and probability inequalities are exact written proofs.
The finite numbers are interval-derived diagnostics, not a proof of
uniform variance, weak convergence, or RH.
