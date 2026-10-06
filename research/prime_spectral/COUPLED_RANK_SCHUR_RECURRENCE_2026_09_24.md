# A coupled Schur recurrence for increasing Fourier rank

The [origin-constrained Weil resolvent](ORIGIN_SCHUR_RESOLVENT_2026_09_24.md)
gives an exact ground profile at one finite rank. At fixed prime support,
the even Fourier spaces are nested. Their rank increment has two
forcing terms that nearly cancel in the existing cutoff-13 example.
Keeping them under one constrained inverse is essential for a useful
all-rank estimate. The calculation below is finite; it does not prove
the required uniform cumulative budget or RH.

## Exact nested-rank identity

Fix a support cutoff and write the even Weil matrix at rank \(M>N\)
in coordinates \(0\), \(1,\ldots,N\), and \(N+1,\ldots,M\):

\[
 A_M=\begin{pmatrix}
 a&b^*&d^*\\ b&C&E\\d&E^*&F
 \end{pmatrix}.
\]

Its leading \((N+1)\)-dimensional block is exactly the rank-\(N\)
matrix, because each Weil entry depends on its two Fourier indices and
the common support, not on the mode cutoff. Assume both finite
simple-even and nonzero-origin gates. Let \(\lambda_N,\lambda_M\) be
the least even eigenvalues, and write the origin-normalized rank-\(N\)
ground vector as \(v_N=(1,h_N)\). Pad it by zero in the new modes.
The rank-\(M\) constrained block is

\[
 T_M=A_M[1{:}M,1{:}M]-\lambda_MI>0.
\]

The projected residual of the padded old ground vector has the
**coupled** form

\[
 r_{N\to M}=
 \begin{pmatrix}
   (\lambda_N-\lambda_M)h_N\\ d+E^*h_N
 \end{pmatrix}.                                             \tag{1}
\]

Indeed, the old ground equation gives \(b+Ch_N=\lambda_Nh_N\).
Applying the [origin-constrained identity](ORIGIN_SCHUR_RESOLVENT_2026_09_24.md)
in the larger space yields the exact recurrence

\[
 v_M-(v_N\oplus0)=(0,-T_M^{-1}r_{N\to M}),\qquad
 P_M(z)-P_N(z)=-F_{M,z}(0,T_M^{-1}r_{N\to M}).       \tag{2}
\]

The first component of (1) is the eigenvalue shift acting on the old
noncentral vector; the second is the old vector's coupling to new
modes. A bound on their separate inverse images loses their signed
cancellation. Equation (2) uses the sum **before** inversion.

For ranks \(N_0<N_1<\cdots\) at fixed support, telescoping (2) gives
the exact cumulative identity

\[
 P_{N_b}(z)-P_{N_a}(z)
 =-\sum_{k=a}^{b-1}F_{N_{k+1},z}
     (0,T_{N_{k+1}}^{-1}r_{N_k\to N_{k+1}}).       \tag{3}
\]

An effective tail bound on the *coupled* terms in (3), uniform over
the support cutoffs of interest and on compact subsets of the RH strip,
would settle the Fourier-rank part of the convergence problem. It
would still need an independent support-limit identification with Xi
and the finite real-zero gates along the path. No such tail bound is
proved here.

## A two-sided energy law from block elimination

The large cancellation in (2) is constrained by a scalar identity.
Set \(\lambda=\lambda_M\), \(R(t)=(C-tI)^{-1}\), and define the
new-mode Schur complement and effective coupling

\[
 S=F-\lambda I-E^*R(\lambda)E>0,\qquad
 q=d-E^*R(\lambda)b.
\]

Eliminating the old noncentral modes from \((A_M-\lambda I)v_M=0\)
gives \(h_{M,\mathrm{new}}=-S^{-1}q\) and the exact scalar equation

\[
 q^*S^{-1}q
 =g(\lambda_M),\qquad
 g(t)=a-t-b^*(C-tI)^{-1}b.                         \tag{4}
\]

The old ground equation gives \(g(\lambda_N)=0\). Throughout
\([\lambda_M,\lambda_N]\), the old constrained block is positive,
and differentiation yields

\[
 -g'(t)=1+\|R(t)b\|^2.
\]

Every spectral denominator in \(R(t)\) decreases as \(t\) increases,
so \(\|R(t)b\|^2\) is nondecreasing. Integrating gives the **two-sided
rank-energy law**

\[
 (\lambda_N-\lambda_M)
       \bigl(1+\|R(\lambda_M)b\|^2\bigr)
 \le q^*S^{-1}q
 \le(\lambda_N-\lambda_M)\bigl(1+\|h_N\|^2\bigr). \tag{5}
\]

Thus a bound on the origin-normalized ground-vector norms would turn
the telescoping least-eigenvalue decrease into a cumulative *coupling
energy* budget at each fixed support. It would not by itself bound the
Fourier-profile increment (2): the relevant Fourier dual resolvent can
amplify small-energy directions, and uniformity as support grows is
still missing. The exact pairing in (2), not separate bounds on its
two sources, remains the target for an all-rank profile budget.
More precisely, if all the finite matrices on a fixed-support rank
path are positive and \(\|v_{N_k}\|^2\le K\), then (5) telescopes to

\[
 \sum_{k=a}^{b-1}q_k^*S_k^{-1}q_k
 \le K(\lambda_{N_a}-\lambda_{N_b})
 \le K\lambda_{N_a}.                                \tag{6}
\]

There is an **unconditional scale-free version** that does not assume
any bound on the origin-normalized vector norms. Divide the upper
inequality in (5) by \(\|v_{N_k}\|^2=1+\|h_{N_k}\|^2\) before summing:

\[
 \sum_{k=a}^{b-1}
  \frac{q_k^*S_k^{-1}q_k}{\|v_{N_k}\|^2}
 \le\lambda_{N_a}-\lambda_{N_b}
 \le\lambda_{N_a}.                                \tag{7}
\]

The **full coupled residual** has an even cleaner exact energy
identity. Let \(x=v_N\oplus0\), \(y=v_M\), and \(d=x-y=(0,d_H)\).
Since \((A_M-\lambda_MI)y=0\) and the leading block of \(A_M\) is
\(A_N\),

\[
 d_H^*T_Md_H
 =x^*(A_M-\lambda_MI)x
 =(\lambda_N-\lambda_M)\|v_N\|^2.
\]

But \(r_{N\to M}=T_Md_H\), so equivalently

\[
 r_{N\to M}^*T_M^{-1}r_{N\to M}
   =(\lambda_N-\lambda_M)\|v_N\|^2.             \tag{8}
\]

Dividing (8) by \(\|v_N\|^2\) and summing gives **equality**, not
merely the upper bound (7): the normalized coupled-residual energies
telescope exactly to \(\lambda_{N_a}-\lambda_{N_b}\). This uses the
two forcing components together and requires no support-independent
origin-norm estimate. Equation (7) remains a separate bound on the
reduced *new-mode* coupling energy.

The decreasing nonnegative least eigenvalues have a limit, so the
normalized-energy tail in (7) vanishes at every fixed support along
any infinite rank path passing the finite gates. This is a genuine
all-rank *energy* budget. It is not an all-rank **profile** budget:
the Fourier functional may amplify a small normalized energy, and
uniformity as support grows still needs a bound on the right side or
a sharper coupled pairing estimate. The
[Parseval origin-norm obstruction](ORIGIN_NORM_TIGHTNESS_OBSTRUCTION_2026_09_24.md)
shows that a bound on \(\|v_{C,N}\|^2\) **independent of growing support**
is impossible along any path whose Fourier profiles converge locally
to normalized Xi. A uniform cumulative **profile** budget must absorb at
least this support-dependent norm growth or preserve further
cancellation in (2).

More precisely, if \(f_{M,z}\) represents the Fourier functional on
the noncentral modes, Cauchy-Schwarz in the \(T_M\)-energy gives

\[
 |P_M(z)-P_N(z)|^2
 \le(\lambda_N-\lambda_M)\|v_N\|^2
       f_{M,z}^*T_M^{-1}f_{M,z}.                  \tag{9}
\]

Thus the next analytic gate is a support-and-rank estimate on this
**dual Fourier resolvent**, or a direct bound on the signed pairing
in (2). The eigenvalue decrease alone cannot do it. For an abstract
control, take \(A_0=[1]\) and
\(A_1=\left(\begin{smallmatrix}1&-\varepsilon\\-\varepsilon&1\end{smallmatrix}\right)\)
with \(0<\varepsilon<1\). The least eigenvalue drops by
\(\varepsilon\), and (8) gives normalized energy \(\varepsilon\to0\),
yet the origin-normalized ground vector changes from \((1,0)\) to
\((1,1)\). In the even Fourier space of length \(2\pi\), its profile
change at real frequency \(1\) has magnitude \(1/\sqrt2\). This is
not a prime Weil matrix; it proves that a dual-resolvent hypothesis
cannot be omitted from a general transfer theorem.

## Certified mode-4 to mode-8 diagnostic

The saved [interval certificate](rank_schur_13_4_8.json) uses the
unchanged cutoff-13 Weil matrices and their least-even enclosures. It
certifies positivity of the rank-8 constrained block, checks interval
consistency with the exact nesting formula, and agrees with two
independently computed origin-normalized ground vectors. The table
shows readable midpoints; the last column is a **certified lower
bound** on the ratio of the two separate absolute contributions to
the coupled absolute change.

| Argument | Eigenvalue-shift contribution | New-mode contribution | Coupled profile change | Separate/coupled ratio, lower |
|:--|--:|--:|--:|--:|
| \(z=4\) | `-464.405640` | `+464.532584` | `+0.126944` | `>7317` |
| \(z=8\) | `-384.052626` | `+384.134403` | `+0.081777` | `>9393` |
| \(z=i\) | `+49.061364` | `-49.075922` | `-0.014558` | `>6741` |

The separate coefficient solutions have norms near 1087, while the
combined origin-vector change has norm near 0.270 (floating diagnostic).
Thus an all-rank estimate that takes absolute values of the two
sources before applying \(T_M^{-1}\) is more than three orders of
magnitude too costly at this one finite step. The cancellation is
algebraically enforced by the shared eigenvalue equation, but its
uniform size as rank and support grow is unknown.

The same interval certificate verifies (4) and the strict bracket (5).
Here \(\lambda_4-\lambda_8\) is near `9.67926178376e-15`, while the
effective coupling energy is near `2.30302630303e-14`; its lower and
upper bounds from (5) are near `2.30301318320e-14` and
`2.30303942308e-14`. These are readable approximations to the saved
outward rational enclosures, not an asymptotic estimate.
The old origin-normalized squared norm is near `2.37935441208`, so
the normalized coupling energy in (7) is near `9.67920664254e-15`,
strictly below the eigenvalue shift near `9.67926178376e-15`.
The coupled residual energy in (8) is enclosed near
`2.30303942308e-14`; its independent eigenvalue-shift expression
has an overlapping, much narrower interval.
The certificate also evaluates the dual Fourier energy in (9).
Even with the *exact* rank energy, its Cauchy bound is over `25.6694`
at \(z=4\), over `21.2300` at \(z=8\), and over `2.7118` at
\(z=i\), while the respective actual changes are about `0.126944`,
`0.081777`, and `0.014558` in magnitude. The certified ratios of the
Cauchy bound to the coupled change exceed `202`, `259`, and `186`.
Thus an all-rank proof using (9) would require substantially sharper
dual-resolvent control, or it must estimate the signed pairing (2)
directly. The telescoping energy identity alone does not close the
profile gate.

`experiments/prime_spectral/rank_schur_recurrence.py` evaluates both
sources and their sum with Arb. A separate test compares its coupled
profile change to the difference of the two saved Schur ground
profiles at all three arguments. Reproduce with:

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/rank_schur_recurrence.py --first research/prime_spectral/certified_weil_13_4.json --second research/prime_spectral/certified_weil_13_8.json --output research/prime_spectral/rank_schur_13_4_8.json
```

The recurrence is exact finite-dimensional algebra. The interval
certificate is bounded evidence about one rank increment, not a
sequence-wide theorem or an RH proof.
