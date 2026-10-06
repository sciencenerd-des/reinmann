# An origin-constrained Weil resolvent for the missing profile estimate

The [strip residual theorem](STRIP_RESIDUAL_TRANSFER_2026_09_23.md)
requires a candidate Rayleigh quotient below the second even Weil
eigenvalue. The exact projected prolate candidate fails that finite gate
at cutoff 13 through mode 16. The origin-constrained identity below
compares profiles without that Rayleigh hypothesis. It does **not**
establish the still-missing all-support estimate.

## Exact Schur identity

Write a finite even Weil matrix in the orthonormal Fourier basis as

\[
 A=\begin{pmatrix}a&b^*\\ b&C\end{pmatrix},\qquad
 F_0(x)=x_0.
\]

Assume its least eigenvalue \(\lambda_0\) is simple, with eigenvector
whose zeroth coordinate is nonzero. Put \(T=C-\lambda_0I\). The
Rayleigh principle shows \(T\) is strictly positive: equality in
\(x^*(A-\lambda_0I)x\ge0\) for a vector \(x=(0,h)\) would make it a
least eigenvector, contrary to its nonzero zeroth coordinate. Hence
the **origin-normalized** ground vector and its scalar secular equation
are exactly

\[
 v=\begin{pmatrix}1\\-T^{-1}b\end{pmatrix},\qquad
 a-\lambda_0-b^*T^{-1}b=0.                         \tag{1}
\]

This solves for the Fourier profile directly, without first normalizing
the vector at the support boundary. If \(F_z\) is the centered Fourier
functional from the strip theorem, then \(P_v(z)=F_z(v)\), because
\(F_0(v)=1\). The finite quotient real-zero theorem still requires its
separate boundary and positive-metric gates; (1) does not replace them.

For **any** candidate \(w=(1,u)\) in the same even space, define its
origin-constrained Weil residual

\[
 r_H=P_H(A-\lambda_0I)w=b+Tu,\qquad H=\ker F_0.
\]

Since \(u-v_H=T^{-1}r_H\), exact linear algebra gives the
cancellation-preserving transfer

\[
 P_w(z)-P_v(z)=F_z(0,T^{-1}r_H).                 \tag{2}
\]

The residual component in the zeroth coordinate plays no role. In
particular, (2) remains valid when the candidate Rayleigh quotient
lies *above* the second even eigenvalue. A crude consequence is

\[
 |P_w(z)-P_v(z)|\le
 \|F_z|_H\|\,\|r_H\|/\kappa,\qquad
 \kappa=\lambda_{\min}(C)-\lambda_0>0.          \tag{3}
\]

A sharper, positive-form version is

\[
 |P_w(z)-P_v(z)|^2\le
 \langle f_z,T^{-1}f_z\rangle
 \langle r_H,T^{-1}r_H\rangle,                   \tag{4}
\]

where \(f_z\) represents \(F_z|_H\), with the Hermitian convention for
complex \(z\). Formula (2) can be sharper still because it retains the
signed pairing between the Fourier functional and the arithmetic
residual. Bounds on either factor in (4) alone need not capture that
cancellation.

## Conditional strip gate

Consider a growing sequence passing the finite real-zero gates, with
origin-normalized candidates \(w_j\) whose profiles converge locally
uniformly on \(|\operatorname{Im}z|<1/2\) to \(\Xi(z)/\Xi(0)\). If for
every compact subset \(K\) of that strip,

\[
 \sup_{z\in K}|F_{j,z}(0,T_j^{-1}r_{H,j})|\longrightarrow0,
                                                               \tag{5}
\]

then the ground profiles have the same limit and Hurwitz's theorem
implies RH. This is a sufficient condition, not a proof of (5). The
[prolate finite-Fourier diagonal](PROLATE_FOURIER_DIAGONAL_2026_09_23.md)
addresses the candidate's own limit along a fast path, but no uniform
bound on the constrained inverse-residual pairing is known. Equation
(5) isolates that missing estimate without a Rayleigh-below-second
gate. It also makes clear that a norm-only residual bound may be far
too expensive when \(T_j\) is ill-conditioned.
The existing [two-frequency certificate](PROLATE_PROFILE_CONSTRAINT_2026_09_23.md)
still shows substantial prolate-to-ground profile separation at these
small finite configurations. Bypassing the Rayleigh condition is an
algebraic improvement in the *transfer interface*, not evidence that
the prolate candidate already satisfies (5).

## Certified finite computation

`experiments/prime_spectral/ground_schur.py` forms \(T\) from the
unchanged certified cutoff-13 Weil matrices, certifies its positive
interval LDL pivots, solves (1) with Arb, checks that the first-row
residual contains zero, and independently compares its origin vector
with the previous boundary-constrained construction. The saved
[mode-4](ground_schur_13_4.json) and [mode-8](ground_schur_13_8.json)
outputs enclose the real profiles at 4 and 8 and the imaginary profile
at \(i\). The smallest ratio of an old coordinate interval width to
its Schur interval width exceeds \(2.57\times10^6\) at mode 4 and
\(6.87\times10^8\) at mode 8. These are enclosure improvements using
the same finite input, not new eigenvalue estimates or a convergence
result. An independent test checks \(P(i)=R(i)G(i)\).

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/ground_schur.py --certificate research/prime_spectral/certified_weil_13_4.json --output research/prime_spectral/ground_schur_13_4.json
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/ground_schur.py --certificate research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/ground_schur_13_8.json
```

The exact derivation is finite-dimensional spectral algebra. Interval
checks validate the implementation for two finite matrices; neither
they nor the conditional strip gate prove RH.
