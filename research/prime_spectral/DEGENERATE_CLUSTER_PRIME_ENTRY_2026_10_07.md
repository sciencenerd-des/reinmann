# Prime entry on a possibly degenerate ground eigenspace

Date: 7 October 2026. Status: proposed analytic theorem with a written
proof conditional on the previously stated Weil operator, uniform renewal
trace, and norm-resolvent inputs. These operator inputs and the application
below need mathematical review. Four accompanying Lean lemmas prove scalar
error implications with named hypotheses; they do not formalize this
operator theorem. No priority, new positivity endpoint, or RH claim.

This continues [the two-state convergence note](TRACE_ENCLOSURES_STATE_CONVERGENCE_2026_10_07.md).
Its simple-ground-state argument cannot select a common vector at a
multiple ground eigenvalue. The construction here retains the whole
ground cluster and accounts for its background splitting. It also isolates
why a naive fixed-gap second-order estimate does not prove the desired
prime-entry coefficient.

## 1. Statement with the background splitting retained

Let \(q=p^m\), \(w=\log p/\sqrt q\), \(L_\delta=\log q+\delta\).
On this interval let \(A_\delta^0\) omit just the newly entering \(q\)-term
and let \(A_\delta^1=A_\delta^0+V_\delta\), where
\(V_\delta=-w(T_{\log q}+T_{\log q}^*)\) denotes the supported translations.
All other prime powers and both pole terms are retained.

Transfer to the fixed interval \(J=(-1/2,1/2)\) by the unitary dilation.
Assume the common limiting operator \(A_*\) has lowest eigenvalue
\(\lambda_*\) of multiplicity \(k\) and next eigenvalue at least
\(\lambda_*+g\), \(g>0\). Compact resolvent guarantees such a finite \(k\)
and a positive gap to the next distinct eigenvalue. Simplicity within
this cluster is not assumed.

The previous note proves, as written analysis, norm-resolvent convergence
of both families to \(A_*\). Let \(P_\delta\) be the projection onto the
lowest \(k\) eigenvalues of \(A_\delta^0\); it converges in norm to \(P_*\).
Choose a fixed orthonormal basis of \(P_*L^2(J)\) and isometries
\(\mathcal J_\delta:\mathbb C^k\to P_\delta L^2(J)\) converging to its
inclusion. One canonical construction is the polar isometry of the map
\(P_\delta|_{P_*L^2(J)}\): its Gram matrix tends to the identity.
Define the actual background matrix

\[
 H_\delta=\mathcal J_\delta^*A_\delta^0\mathcal J_\delta.
 \tag{1}
\]

This finite matrix is not a numerical Galerkin approximation: its range
is the actual spectral subspace. It need not be explicitly computable.
Its eigenvalues are the lowest \(k\) eigenvalues of \(A_\delta^0\).

Let \(a_i=\tau_-(u_{*,i})\), \(b_i=\tau_+(u_{*,i})\) be the physical,
unit-normalized endpoint traces of the limiting basis states. Set

\[
 \mathcal B_{ij}=-w(\overline{a_i}b_j+\overline{b_i}a_j),\qquad
 s_\delta=W_\delta=\int_0^\delta V(t)V(\delta-t)\,dt
       \sim\frac{\delta}{\log(1/\delta)}.                \tag{2}
\]

Here \(V\) is the normalized renewal function, whereas \(V_\delta\) is
the newly active operator. With eigenvalues ordered increasingly, the
proposed conclusion is

\[
 \boxed{\quad
 \lambda_j(A_\delta^1)
   =\lambda_j(H_\delta+s_\delta\mathcal B)+o(s_\delta),
 \qquad 1\le j\le k.\quad}                             \tag{3}
\]

The remainder is uniform over this finite set of indices. The proof
does not replace \(H_\delta\) by \(\lambda_*I\) at the activation scale.
That replacement generally requires an additional, unavailable estimate.

## 2. Uniform traces on the moving cluster

The earlier semigroup argument bounds every unit eigenfunction whose
eigenvalue stays in a compact interval. A unit vector in the \(k\)-dimensional
cluster is a linear combination of these eigenfunctions with coefficient
sum at most \(\sqrt k\). Thus it has uniform \(L^\infty\) bounds. The same
argument applies to \(A_\delta^0u\), since the cluster eigenvalues are
uniformly bounded. The localized equation is

\[
 F_\delta=\chi[(A_\delta^0+c)u-Ku+S_\delta^0u]+[B,\chi]u.
\]

Consequently the bounded-forcing renewal argument applies uniformly to
all unit vectors in the cluster, including the canonical frame vectors
that need not individually be eigenvectors. There are constants
\(M_F,T,K_V\) such that, at both endpoints,

\[
 |\tau_\pm(u)|\le T,\qquad
 |u(t)/V(t)-\tau_-(u)|\le2M_FV(t),\qquad
 |u(t)|,\ |u(L_\delta-t)|\le K_VV(t).                  \tag{4}
\]

For trace convergence, each frame vector converges in \(L^2\), and
\[
 \|(A_\delta^0-\lambda_*)\mathcal J_\delta z\|_2
 \le\max_{1\le j\le k}|\lambda_j(A_\delta^0)-\lambda_*|\,\|z\|
 \longrightarrow0.
\]
The localized forcings therefore converge in \(L^2(H)\), with uniform
boundedness and exponential tails. The explicit three-region estimate
in the preceding note proves convergence of both endpoint trace rows.
This reasoning does not claim convergence of an arbitrarily selected
individual eigenvector inside a degenerate cluster.

For a unit cluster vector, expanding its endpoint overlap as in the
previous note gives, with \(h_\delta=2M_FV(\delta)\),

\[
 \left|\frac{\langle u,V_\delta u\rangle}{s_\delta}
      +2w\operatorname{Re}(\overline{\tau_-(u)}\tau_+(u))\right|
 \le2w[2Th_\delta+h_\delta^2].                         \tag{5}
\]

The operator norm of a Hermitian matrix is the supremum of the absolute
value of its unit-vector quadratic form. Convergence of the trace rows
and (5) prove

\[
 \left\|\mathcal J_\delta^*V_\delta\mathcal J_\delta/
                   s_\delta-\mathcal B\right\|
 \le \rho_\delta,\qquad \rho_\delta\longrightarrow0.   \tag{6}
\]

This is an operator bound on the entire cluster, obtained from a uniform
trace statement. An estimate for a single selected state would not
suffice.

## 3. The Schur correction is smaller than the activation scale

Write \(Q_\delta=1-P_\delta\). For small \(\delta<L_\delta/2\),
every vector \(V_\delta P_\delta f\) is supported in the two endpoint
layers \(E_\delta\), of physical width \(\delta\) each. Their dilation
to \(J\) has measure \(2\delta/L_\delta\to0\).
Using (4) on the two disjoint translated pieces,

\[
 \|V_\delta P_\delta\|^2
 \le2w^2K_V^2\delta V(\delta)^2
   =C_\delta s_\delta,\qquad
 C_\delta\longrightarrow2w^2K_V^2.                   \tag{7}
\]

A fixed inverse-gap bound by itself would give a Schur cost
\(O(s_\delta)\), not \(o(s_\delta)\). It cannot discard the correction
when identifying a leading coefficient.

Instead consider the full operator
\[
 \widetilde A_\delta=A_\delta^0+Q_\delta V_\delta Q_\delta.
\]
It is block diagonal for \(P_\delta\oplus Q_\delta\).
Its added perturbation is uniformly bounded and strongly tends to zero:
\(P_\delta\) converges in norm and \(V_\delta\) tends strongly to zero.
The same common-domain compact-resolvent argument as before yields
\(\widetilde A_\delta\to A_*\) in norm-resolvent sense.

It follows that the \(Q_\delta\) block has lower spectral bound
\(\lambda_*+g/2\), eventually. To justify this carefully,
norm-resolvent convergence gives exactly \(k\) eigenvalues in the
isolated low cluster and no spectrum below it, for small \(\delta\);
the \(P_\delta\) block already supplies these \(k\) eigenvalues.
Uniform semiboundedness excludes eigenvalues escaping below every
fixed energy. Thus no additional low eigenvalue can hide in \(Q_\delta\).

Set \(z_+=\lambda_*+g/4\), and extend its complementary inverse by zero:

\[
 R_\delta=Q_\delta
   [Q_\delta(\widetilde A_\delta-z_+)Q_\delta]^{-1}Q_\delta.
\]

This is nonnegative and compact. Norm-resolvent functional calculus
with a cutoff that vanishes on the low cluster gives

\[
 R_\delta\longrightarrow
 R_*=Q_*[Q_*(A_*-z_+)Q_*]^{-1}Q_*
 \quad\hbox{in operator norm}.                       \tag{8}
\]

The continuous cutoff is legitimate because the cluster and complement
are separated by a fixed gap; the reciprocal on the complement tends
to zero at infinity. Continuity of square roots gives
\(R_\delta^{1/2}\to R_*^{1/2}\) in norm.

Let \(M_\delta\) multiply by the indicator of the two layers in \(J\).
It tends strongly to zero and is self-adjoint. Compactness of
\(R_*^{1/2}\), by finite-rank approximation, therefore implies

\[
 \omega_\delta:=\|R_\delta^{1/2}M_\delta\|^2
\longrightarrow0.                                  \tag{9}
\]

In particular
\(\|R_*^{1/2}M_\delta\|=\|M_\delta R_*^{1/2}\|\to0\);
the self-adjoint layer multiplier is what permits the compact map to
be placed on the right of the strongly convergent factor.

For real \(z\in[\lambda_*-g/4,\lambda_*+g/4]\), the complementary
inverse at \(z\) is nonnegative and bounded above by that at \(z_+\).
The full Feshbach Schur correction

\[
 \Sigma_\delta(z)=P_\delta V_\delta Q_\delta
 [Q_\delta(A_\delta^1-z)Q_\delta]^{-1}
 Q_\delta V_\delta P_\delta
\]

has \(Q_\delta(A_\delta^1-z)Q_\delta
=Q_\delta(\widetilde A_\delta-z)Q_\delta\). Since
\(V_\delta P_\delta=M_\delta V_\delta P_\delta\), (7)–(9) give the
uniform estimate

\[
 \boxed{\quad0\le\Sigma_\delta(z)
       \le C_\delta\omega_\delta s_\delta P_\delta
       =o(s_\delta)P_\delta.\quad}                   \tag{10}
\]

The layer projection is applied before the complementary resolvent.
Projecting by \(Q_\delta\) first can destroy spatial localization;
the extended inverse in (8) is what makes the displayed argument valid.
Neither a small global operator norm for \(V_\delta\) nor a positive
Weil semigroup is assumed.

## 4. Eigenvalue counting closes the reduction

The Schur map here is classical; see
[Dusson–Sigal–Stamm](https://arxiv.org/abs/2105.02058).
Let \(G_\delta=H_\delta+
\mathcal J_\delta^*V_\delta\mathcal J_\delta\) and
\(\epsilon_\delta=C_\delta\omega_\delta\).
For \(z\) in the fixed gap interval, completing the complementary
square is an invertible triangular congruence of the form of
\(A_\delta^1-z\). It leaves a strictly positive complementary block
and the finite Schur matrix

\[
 G_\delta-zI-\mathcal J_\delta^*\Sigma_\delta(z)\mathcal J_\delta.
\]

The number of negative directions of the full form consequently equals
that of this matrix. Equation (10) bounds it between the counting
functions of \(G_\delta-zI\) and
\(G_\delta-(z+\epsilon_\delta s_\delta)I\).
Taking strict thresholds and then limits at the ordered eigenvalues gives

\[
 \lambda_j(G_\delta)-\epsilon_\delta s_\delta
 \le\lambda_j(A_\delta^1)\le\lambda_j(G_\delta),
 \qquad 1\le j\le k.                                 \tag{11}
\]

The upper bound also follows from min–max on \(P_\delta L^2(J)\).
All relevant eigenvalues lie inside the fixed gap interval eventually.
Weyl's finite Hermitian eigenvalue inequality and (6) then give the
explicit proposed error bound

\[
 \left|\lambda_j(A_\delta^1)
        -\lambda_j(H_\delta+s_\delta\mathcal B)\right|
 \le(\rho_\delta+C_\delta\omega_\delta)s_\delta.       \tag{12}
\]

Both coefficients on the right tend to zero. This proves (3)
under the stated analytic inputs. It neither assigns a numerical
neighborhood radius nor evaluates \(\omega_\delta\) or the actual traces.

## 5. Rank, parity, and what degeneracy does not permit

Let \(\mathcal Tz=(\sum_i a_i z_i,\sum_i b_i z_i)\).
With \(J_2=\begin{pmatrix}0&1\\1&0\end{pmatrix}\),

\[
 \mathcal B=-w\mathcal T^*J_2\mathcal T.              \tag{13}
\]

Thus its rank is at most two and it has at most one positive and one
negative eigenvalue. Its form vanishes on the joint kernel of the two
traces, a subspace of codimension at most two.
In a reflection-parity basis, \(b_i=a_i\) for even vectors and
\(b_i=-a_i\) for odd vectors. The cross-parity entries vanish, and

\[
 \mathcal B_{\rm even}=-2w\,a_{\rm even}^*a_{\rm even},
 \qquad
 \mathcal B_{\rm odd}=+2w\,a_{\rm odd}^*a_{\rm odd}.    \tag{14}
\]

The leading prime-entry form is therefore negative rank at most one
on the even cluster and positive rank at most one on the odd cluster.
These statements concern the leading form, not positivity of the
full operator.

For \(k=1\), (3) reduces to the previous common-coefficient formula.
For \(k>1\), Weyl's inequality gives the valid enclosure

\[
 \lambda_{\min}(\mathcal B)+o(1)
 \le\frac{\lambda_j(A_\delta^1)-\lambda_j(A_\delta^0)}{s_\delta}
 \le\lambda_{\max}(\mathcal B)+o(1).                  \tag{15}
\]

It does not generally give a single limit.
If additionally \((H_\delta-\lambda_*I)/s_\delta\to D\), then the
normalized full-cluster eigenvalues tend to those of \(D+\mathcal B\).
Without that additional hypothesis, the background splitting may
dominate the activation scale.
Also a rank-two perturbation can move all eigenvalues of a finite
matrix. It is false that all but two individual eigenvalues must
remain unchanged. The trace-free subspace assertion is the precise
statement justified by (13).

## 6. Readiness and the next certificate

The Schur method, compact-times-strong principle, and elementary
two-functional rank factorization are standard ingredients. The
proposed contribution is their combination with actual normalized
Weil endpoint traces to obtain (3),(10),(14), including a multiple
limiting ground eigenvalue. The prior-art review did not establish
priority for this combination; it remains a candidate, not an
advertised novel discovery.

The four scalar Lean lemmas in
[WeilClusterActivation.lean](../../Reinmann/WeilClusterActivation.lean)
separate the localized Schur cost from the boundary-matrix error and
prove the normalized limiting implications. The operator identities,
inertia correspondence, uniform trace inputs, and compactness
estimate (9) are not Lean theorems.

A useful next validation target is a computable upper bound for
\(\omega_\delta\), together with actual boundary-adapted profile/trace
enclosures. A \(1/g\) inverse bound alone will not do: it loses the
vanishing factor in (9). The existing prime-two and prime-three
certificates address \(k=1\); no multiple ground state is asserted to
occur there. No all-scale margin, zero-crossing exclusion, or RH
implication follows from this local reduction.

## 7. Quantitative continuation

The subsequent [localized-resolvent note](LOCALIZED_RESOLVENT_RATE_2026_10_07.md)
replaces the compactness-only factor by explicit upper and lower bounds.
A second resolvent identity, with the first TWO free inverse moments
separately dominated by killed-semigroup comparison, gives
\(\omega_\delta\log(1/\delta)\to1\) under the uniform complement-gap,
bounded-remainder and cluster-boundedness inputs. Its inverse-gap
constant occurs in a lower-order term. A localized sine and removal
of the finite cluster prove the matching lower bound.
Consequently the Schur error here is
\(O(\delta/\log^2(1/\delta))\), with explicit bounds once those inputs
are quantified. The fixed-threshold resolvent bounds at 2 and 3 are
evaluated; an explicit moving-window gap radius and tight actual
endpoint traces remain unresolved. This strengthens the analysis
without resolving the candidate theorem's priority.

The subsequent [rescaled-layer argument](LAYER_RESOLVENT_SCHUR_COEFFICIENT_2026_10_07.md)
identifies the leading Schur matrix itself as
\(w^2(a^*a+b^*b)\) at scale \(\delta/\log^2(1/\delta)\).
It yields a finer cluster eigenvalue reduction relative to the exact
head \(G_\delta\), while retaining all its background and trace errors.
