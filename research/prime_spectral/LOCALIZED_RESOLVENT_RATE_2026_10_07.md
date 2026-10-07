# A sharp localized complementary-resolvent rate

7 October 2026. Continuation of the
[cluster prime-entry reduction](DEGENERATE_CLUSTER_PRIME_ENTRY_2026_10_07.md).
This supplies a quantitative replacement for its compactness-only factor
\(\omega_\delta\to0\). The analytic proof below is written mathematics;
the accompanying Lean module proves seven scalar consequences of named
analytic inputs. Neither is described as an RH proof or a cleared novelty
claim.

## 1. Statement and normalization

Work on a bounded physical interval \(I\), with zero extension to the
line and the unitary Fourier transform. Let \(B_I\) be the exterior
Dirichlet realization of the nonnegative multiplier

\[
 b(\xi)=\tfrac12\log(1+\xi^2).
\]

It is not the logarithm of the Dirichlet Laplacian.
Let \(A=B_I+E\), with \(E\) bounded self-adjoint, and let \(P\) be a
finite-rank reducing spectral projection for \(A\). Put \(Q=1-P\).
Suppose

\[
 Q(A-z)Q\ge\gamma Q,\quad \gamma>0,
 \qquad
 D=Q(A-z)Q+\gamma P=B_I+\widehat E,
 \qquad \|\widehat E\|\le\Lambda.                 \tag{1}
\]

The complementary inverse extended by zero is
\(R=Q[Q(A-z)Q]^{-1}Q\), so \(D^{-1}=R+\gamma^{-1}P\).
The equality defining \(D\) is an operator/form equality, not a
compression of \(B_I\) followed by a free inverse. The bounded lift
exists because \(AP\) is bounded for a finite spectral cluster.

Let \(M_\delta\) multiply by the union of the two endpoint layers,
each of physical width \(\delta\), and let
\(X=\log(1/\delta)\). Assume \(X\ge32\) and that the layers are
disjoint. Define

\[
 d_X=1+X-3\log X>0,\quad W=\Lambda+1,\quad
 C=W+W^2/\gamma.
\]

Then the actual complementary resolvent satisfies

\[
 \boxed{\quad
 \omega_\delta:=\|R^{1/2}M_\delta\|^2
 \le \frac{2(1+C)}{\pi X^3}
       +\frac1{d_X}+\frac{C}{d_X^2}.
 \quad}                                                   \tag{2}
\]

Also \(\omega_\delta\le1/\gamma\). If \(u_1,\ldots,u_k\) is an
orthonormal basis of \(P\), with \(\|u_i\|_\infty\le M\), then

\[
 \boxed{\quad
 \omega_\delta\ge
 \frac1{X+\tfrac12\log(1+\pi^2)+\Lambda}
       -\frac{8kM^2}{\pi^2\gamma}e^{-X}.
 \quad}                                                   \tag{3}
\]

For fixed bounds \(\Lambda,M,k,\gamma^{-1}\), these two inequalities
give the **sharp norm asymptotic**

\[
 \boxed{\omega_\delta\log(1/\delta)\longrightarrow1.} \tag{4}
\]

The same conclusion is uniform for varying intervals, operators,
shifts and clusters satisfying these uniform bounds. No convergence
of individual eigenvectors or traces is required for (2)–(4).
The coefficient one refers to the stated symbol and physical layer
width; changing the multiplier normalization changes it.

## 2. Free inverse moments: the restriction issue

Set \(T=B_I+1\). Its positive Dirichlet semigroup is dominated on
nonnegative data by the whole-line semigroup of \(B+1\). This is the
standard killed-process/Dirichlet-form domination for the nonnegative
Lévy kernel \(e^{-|x-y|}/(2|x-y|)\), used in the earlier
[boundary regularity argument](BOUNDARY_REGULARITY_PRIME_ACTIVATION_2026_10_07.md).
It is asserted here only for the comparison operator \(B_I\), never
for the Weil operator \(A\).

One can justify this comparison without a boundary-kernel formula.
On the whole line add the bounded killing potential
\(n1_{I^c}\) to \(B\). Each factor of its Trotter product is a
positive free-semigroup factor followed by multiplication by a
function between zero and one. The product on nonnegative data is
therefore dominated by the corresponding free-semigroup product.
Let \(n\to\infty\). Monotone convergence of the nonnegative closed
forms restricts their limit domain to functions zero outside \(I\),
which is precisely the exterior form domain already identified in
[the form-core note](WEIL_LOG_FORM_CORE_2026_10_07.md). The limiting
semigroup on that subspace is \(e^{-tB_I}\); positivity and domination
pass to the strong limit since the positive cone of \(L^2\) is closed.

For \(p=1,2\), the Laplace formula

\[
 T^{-p}=\frac1{\Gamma(p)}\int_0^\infty
                  t^{p-1}e^{-t}e^{-tB_I}\,dt
\]

therefore gives, for zero-extended \(f\),

\[
 \langle f,T^{-p}f\rangle
 \le\langle |f|,(B+1)^{-p}|f|\rangle.                 \tag{5}
\]

This uses positivity and **separate semigroup formulas for both
powers**. It does not square an operator-order inequality. Such a
squaring would be unjustified in general.

If \(f=M_\delta h\) and \(\|h\|_2\le1\), then \(\|f\|_2\le1\),
\(\|f\|_1^2\le2\delta\), and
\(\|\widehat{|f|}\|_\infty^2\le\delta/\pi\).
Split the Fourier integral at \(|\xi|=T_0\). For either power,

\[
 \langle f,T^{-p}f\rangle
 \le\frac{2\delta T_0}{\pi}
        +\frac1{(1+b(T_0))^p}.                       \tag{6}
\]

Take \(T_0=e^X/X^3\). Then
\(b(T_0)\ge\log T_0=X-3\log X\), yielding
\(2/(\pi X^3)+d_X^{-p}\). All frequency estimates are
in physical coordinates, so no dilation factor is missing.

## 3. The second resolvent identity

Write \(D=T+F\), where \(\|F\|\le W\). Since \(D\ge\gamma I\)
and \(T\ge I\), the bounded inverse identity is valid on all \(L^2(I)\):

\[
 D^{-1}=T^{-1}-T^{-1}FT^{-1}
                    +T^{-1}FD^{-1}FT^{-1}.           \tag{7}
\]

This is an exact noncommutative identity. For every \(f\),

\[
 \langle f,D^{-1}f\rangle
 \le\langle f,T^{-1}f\rangle
      +(W+W^2/\gamma)\langle f,T^{-2}f\rangle.        \tag{8}
\]

Indeed the linear term has absolute value at most
\(W\|T^{-1}f\|_2^2\); the final positive term is at most
\(W^2\|T^{-1}f\|_2^2/\gamma\).
Because \(0\le R\le D^{-1}\), (6) and (8) prove (2).
The relation
\(\|R^{1/2}M_\delta\|^2=\|M_\delta R M_\delta\|\)
uses positivity. It does not commute \(R\) and \(M_\delta\).

A direct energy split gives the additional, usually weaker bound

\[
 \omega_\delta\le
 \left(\frac{4}{\sqrt{\pi\gamma}\,X}
       +\sqrt{\frac{2(1+\Lambda/\gamma)}X}\right)^2.  \tag{9}
\]

To see this, for \(v=D^{-1/2}h\),
\(\|v\|_2^2\le1/\gamma\) and
\(q_B(v)\le1+\Lambda/\gamma\) for \(\|h\|\le1\).
The low/high frequency split of \(v\), followed by the triangle
inequality on the layers, bounds its restricted norm by
\(\sqrt{2\delta T_0/(\pi\gamma)}+
\sqrt{(1+\Lambda/\gamma)/b(T_0)}\).
Use \(T_0=e^{X/2}\), \(b(T_0)\ge X/2\), and
\(e^{-X/2}\le8/X^2\). Finally \(R\le D^{-1}\).
Unlike (2), (9) puts the inverse gap in its leading \(1/X\)
coefficient. The second identity separates that loss into lower order.

## 4. A matching lower bound

Choose the normalized sine supported in the left layer:

\[
 f_\delta(x)=\sqrt{2/\delta}\sin(\pi x/\delta),
 \quad 0<x<\delta,
\]

after translating the left endpoint to zero. Its zero extension is
in \(H^1(\mathbb R)\), hence in the logarithmic form domain.
Concavity of \(\log\), Plancherel, and
\(\|f_\delta'\|_2^2=\pi^2/\delta^2\) give

\[
 q_B(f_\delta)\le\tfrac12\log(1+\pi^2/\delta^2)
 \le X+\tfrac12\log(1+\pi^2).                       \tag{10}
\]

The spectral Cauchy–Schwarz/inverse Jensen inequality for \(D>0\)
gives \(\langle f_\delta,D^{-1}f_\delta\rangle
\ge1/q_D(f_\delta)\).
Moreover \(\|f_\delta\|_1^2=8\delta/\pi^2\), so

\[
 \|Pf_\delta\|_2^2
   =\sum_i|\langle u_i,f_\delta\rangle|^2
   \le 8kM^2\delta/\pi^2.
\]

Subtracting \(\gamma^{-1}P\) from \(D^{-1}\) proves (3).
Multiplication of (2) and (3) by \(X\) squeezes their bounds to one,
because \(d_X/X\to1\). Thus (4) is not merely a big-O upper bound.
The test is an actual form-domain trial for a resolvent quadratic
form; it is not substituted for a minimizing-state boundary profile.

## 5. Consequence for prime-entry Schur errors

Use the cluster notation of the linked note. Its lifted block operator
\(\overline A_\delta=A^0_\delta+Q_\delta V_\delta Q_\delta\)
is \(B_{I_\delta}\) plus a uniformly bounded self-adjoint operator.
On a fixed gap neighborhood, its complementary coercivity and its
finite-cluster eigenvalue bounds supply uniform constants in (1).
The uniform cluster \(L^\infty\) bound supplies (3). Consequently
the actual localized factor in that argument has

\[
 \omega_\delta=(1+o(1))/\log(1/\delta).
\]

Together with \(\|V_\delta P_\delta\|^2\le
2w^2K_V^2\delta V(\delta)^2\),
\(V(\delta)^2\sim1/\log(1/\delta)\), this strengthens the full
Schur remainder from \(o(\delta/\log(1/\delta))\) to

\[
 \|\Sigma_\delta(z)\|
       =O\!\left(\frac{\delta}{\log^2(1/\delta)}\right). \tag{11}
\]

An explicit upper coefficient follows by inserting (2); for example
the limsup of \(X^2\|\Sigma\|/\delta\) is at most
\(2w^2K_V^2\) with the stated uniform boundary envelope. This is an
upper estimate, not a claimed asymptotic equality for the Schur term.
The trace-matrix approximation error remains separate and can be
larger. This does not give a second-order expansion of full eigenvalues.
Existence of a moving-window gap neighborhood was proved qualitatively
in the cluster note; no numerical radius for it is produced here.

## 6. Actual fixed-threshold certificates

For \(q=2,3\), use the previously verified actual-operator enclosures
\(\lambda_1\le U\), \(\lambda_2\ge L_2\), with

| Threshold | \(U\) | \(L_2\) | \(\gamma=3(L_2-U)/4\) |
|---|---:|---:|---:|
| 2 | 0.00142 | 0.00999 | 0.0064275 |
| 3 | 0.000000103 | 0.000000109 | 0.0000000045 |

Set \(z=U+(L_2-U)/4\). Since the ground state is simple, its
projection \(P\) has rank one, and
\(D=A-z+(L_2-\lambda_1)P\ge\gamma I\).
The uniform bound \(\|E\|\le E_0=c+\kappa+m\) on
\(2/3\le |I|\le6/5\) gives \(\lambda_1\ge-E_0\), hence

\[
 \Lambda\le2E_0+L_2+z.
\]

The previously enclosed actual unit-state bound is \(M<3651\).
These are enough to enclose the actual fixed-threshold \(\omega_\delta\)
from both sides for every listed \(X\); no actual eigenvector samples
are needed. The script replays both full-complement second-eigenvalue
bounds and checks their source hashes. It checks the stored trial
upper enclosures and universal state bound, whose computations were
validated in the preceding verification packages; it does not repeat
those integrations. The current script is not an independent audit of
their analytic reduction.

Results are in
[localized_resolvents.json](verification_2026_10_07_localized_resolvent/localized_resolvents.json).
Each interval refers to the actual operator at \(|I|=\log q\), with
endpoint-layer width \(e^{-X}\). It is not a claim that a moving-window
gap is certified at those widths. These extremely small widths and
coarse constants are a validation of the rate, not a practical new
positive-window record or a nonzero actual endpoint trace certificate.

For example, the following are outward-weakened displayed enclosures
for the **scaled** norm \(X\omega_\delta\):

| \(X\) | Threshold 2 | Threshold 3 |
|---:|---:|---:|
| \(10^6\) | [0.99998, 1.04979] | [0.99998, 70920.04] |
| \(10^{16}\) | [0.9999999999, 1.0000000001] | [0.9999999999, 1.000007092] |

In particular the small gap at threshold 3 makes the finite-scale
upper estimate very conservative. The width at the last row is
\(e^{-10^{16}}\), not a practical continuation step.

## 7. Prior-art and proof status

Fourier concentration bounds, killed-semigroup domination, resolvent
identities, and spectral inverse Jensen inequalities are standard.
The distinction between exterior logarithmic operators and a spectral
logarithm, and their weak boundary behavior, already appears in
[Laptev–Weth, spectral properties of the logarithmic Laplacian](https://link.springer.com/article/10.1007/s13324-021-00527-y).
That operator has symbol \(\log|\xi|\), with a different low-frequency
behavior; its results are not silently used as theorems for our
\(\frac12\log(1+\xi^2)\) symbol. The application here is proved
directly by (5)–(10).

The primary-source check for this continuation searched logarithmic
operator small-set concentration, resolvent localization, Dirichlet
boundary eigenfunctions and related uncertainty estimates. It did
not establish priority for (4) or (11). A general high-frequency
localization principle could already subsume (4); no standalone
novelty claim is warranted from this search.

[WeilLocalizedResolvent.lean](../../Reinmann/WeilLocalizedResolvent.lean)
proves the scalar second-identity bound, combination of the TWO
inverse-moment bounds, coefficient positivity, projection-removal
bound and Schur-rate implication. The Fourier, domination, inverse
Jensen and actual-operator inputs are not Lean theorems. A sixth lemma
checks the action-error inequality used in the subsequent
[strong layer limit and leading Schur matrix](LAYER_RESOLVENT_SCHUR_COEFFICIENT_2026_10_07.md).
That continuation retains the exact cluster head and identifies its
next-scale Schur correction from the same two trace rows. A seventh
lemma transfers a named scalar coefficient-limit hypothesis through
the exact scalar Schur root equation, for real traces. This is a
concrete improvement to the proposed cluster argument and its
certificates; paper readiness and RH remain unresolved.
