# Rescaled layer resolvents and the Schur coefficient

7 October 2026. A further proposed analytic consequence of the
[sharp localized-resolvent bounds](LOCALIZED_RESOLVENT_RATE_2026_10_07.md).
The inputs below are those of the existing actual-state trace and
cluster arguments. This note proves a written conditional operator
statement; it does not compute the actual endpoint traces, establish
novelty, or assert a second-order expansion of full eigenvalues.

## 1. Strong convergence after rescaling

Use physical coordinates \(I_\delta=(0,L_\delta)\). Let \(R_\delta(z)\)
be the complementary inverse of the lifted block operator from the
cluster note. Assume the uniform hypotheses of (1) in the linked
resolvent note: complement coercivity \(\gamma>0\), bounded lifted
remainder \(\Lambda\), and a rank-\(k\) cluster with orthonormal
states bounded by \(M\) in \(L^\infty\). These constants are uniform
in \(z\) in a fixed compact subinterval of the complement gap.

Let \(\mathscr H=L^2(0,1)\oplus L^2(0,1)\). The isometry
\(U_\delta:\mathscr H\to L^2(I_\delta)\) identifies its components
with the left and right layers:

\[
 (U_\delta h)(x)=
 \begin{cases}
 \delta^{-1/2}h_-(x/\delta),&0<x<\delta,\\
 \delta^{-1/2}h_+((L_\delta-x)/\delta),
                              &L_\delta-\delta<x<L_\delta,\\
 0,&\text{elsewhere}.
 \end{cases}
\]

With \(X=\log(1/\delta)\), define the positive operator

\[
 S_\delta(z)=XU_\delta^*R_\delta(z)U_\delta.
\]

Then

\[
 \boxed{S_\delta(z)\longrightarrow I_{\mathscr H}
             \quad\text{strongly, uniformly in }z.}        \tag{1}
\]

This is not convergence in operator norm: for every fixed \(\delta\),
\(S_\delta(z)\) is compact on the infinite-dimensional layer space,
so \(\|S_\delta(z)-I\|\ge1\). The strong limit suffices for finitely
many convergent prime-forcing profiles.

### Proof on a dense set

Take a fixed unit vector
\(h\in C_c^\infty(0,1)\oplus C_c^\infty(0,1)\).
Its two rescaled supports are disjoint. Plancherel and concavity of
\(\log\) give, exactly as for the localized sine,

\[
 q_B(U_\delta h)
 \le X+c_h,\qquad
 c_h=\tfrac12\log(1+\|h'\|_2^2).
\]

The inverse Jensen inequality for
\(D_\delta(z)=Q_\delta(\overline A_\delta-z)Q_\delta
+\gamma P_\delta\) yields a lower bound for its inverse quadratic
form. Since
\(\|U_\delta h\|_1^2
=\delta(\|h_-\|_1+\|h_+\|_1)^2\le2\delta\),
ground-cluster removal gives

\[
 \langle h,S_\delta(z)h\rangle
 \ge\frac{X}{X+c_h+\Lambda}
                   -\frac{2kM^2}{\gamma}Xe^{-X}
 =1-\eta_{h,X},                                   \tag{2}
\]

where \(\eta_{h,X}\to0\) uniformly in \(z\).
The upper norm bound in the preceding note gives
\(\|S_\delta(z)\|\le1+\epsilon_X\), with
\(\epsilon_X\to0\), \(\epsilon_X\ge0\). Eventually
\(\epsilon_X\le1\). Positivity gives
\(\|S h\|^2\le\|S\|\langle h,Sh\rangle\). Thus

\[
 \|S_\delta(z)h-h\|^2
 \le (1+\epsilon_X)\langle h,S_\delta(z)h\rangle
               -2\langle h,S_\delta(z)h\rangle+1
 \le\epsilon_X+\eta_{h,X}.                         \tag{3}
\]

This proves uniform strong convergence on the dense set. The uniform
operator-norm bound extends it to every fixed \(h\in\mathscr H\).
No uniform control over all high-frequency layer profiles is claimed.

## 2. The actual prime-forcing profiles converge

Let \(q\) be the newly entering prime power,
\(w=\Lambda(q)/\sqrt q\), \(L_\delta=\log q+\delta\), and
\(V_\delta=-w(T_{\log q}+T_{\log q}^*)\).
The letter \(V_\delta\) here denotes the prime perturbation;
\(V(t)\) without a subscript denotes the normalized renewal mass.
Let \(\mathcal J_\delta:\mathbb C^k\to P_\delta L^2(I_\delta)\)
be the convergent actual-cluster frame of the
[cluster note](DEGENERATE_CLUSTER_PRIME_ENTRY_2026_10_07.md).
Write \(u_{i,\delta}=\mathcal J_\delta e_i\), and assume the established
uniform renewal-trace estimate and trace convergence:

\[
 u_{i,\delta}(t)=V(t)(a_{i,\delta}+O(V(t))),\quad
 u_{i,\delta}(L_\delta-t)=V(t)(b_{i,\delta}+O(V(t))),
 \qquad a_{i,\delta}\to a_i,\ b_{i,\delta}\to b_i.    \tag{4}
\]

The error constants and traces are uniform in the finite cluster.
The prime maps the right endpoint layer into the left, and conversely.
Define the column operator

\[
 F_\delta=
 \frac{U_\delta^*V_\delta\mathcal J_\delta}
          {\sqrt\delta\,V(\delta)}:
          \mathbb C^k\longrightarrow\mathscr H.
\]

The normalized renewal function is slowly varying at zero:
\(V(\delta t)/V(\delta)\to1\) for each fixed \(t>0\).
For \(0<t\le1\), this ratio is at most one by monotonicity.
For each column, its left-layer profile is
\(-w u_{i,\delta}(L_\delta-\delta(1-t))/V(\delta)\),
and similarly on the right. Equation (4), dominated convergence and
the preceding ratio show

\[
 \boxed{F_\delta\longrightarrow F
          \text{ in operator norm},\qquad
 Fe_i=-w(b_i\mathbf1,a_i\mathbf1).}                \tag{5}
\]

Here \(\mathbf1\) is the unit constant in \(L^2(0,1)\).
Endpoints of the rescaled parameter interval have measure zero.
No ordinary endpoint value of a cosine/Galerkin trial is used.
Finite domain dimension upgrades columnwise \(L^2\) convergence
to operator-norm convergence.

## 3. A leading Schur matrix, not just an upper estimate

The actual complementary Schur matrix is

\[
 \mathcal J_\delta^*\Sigma_\delta(z)\mathcal J_\delta
 =\mathcal J_\delta^*V_\delta R_\delta(z)
                           V_\delta\mathcal J_\delta.
\]

The prime forcing is supported entirely in the two layers. Therefore
the following is an exact identity:

\[
 \mathcal J_\delta^*\Sigma_\delta(z)\mathcal J_\delta
 =\frac{\delta V(\delta)^2}{X}
                   F_\delta^*S_\delta(z)F_\delta.     \tag{6}
\]

Strong convergence in (1) is uniform on the finite-dimensional range
of \(F\); (5) and uniform boundedness of \(S_\delta\) imply
\(F_\delta^*S_\delta(z)F_\delta\to F^*F\) in matrix norm,
uniformly in \(z\). Since \(XV(\delta)^2\to1\), (6) proves

\[
 \boxed{
 \frac{X^2}{\delta}
 \mathcal J_\delta^*\Sigma_\delta(z)\mathcal J_\delta
 \longrightarrow\mathcal C,\qquad
 \mathcal C_{ij}=w^2(\overline{a_i}a_j+
                         \overline{b_i}b_j).
 }                                                       \tag{7}
\]

The limit is positive semidefinite of rank at most two. This identifies
the leading **Schur correction itself**, improving the coarse bound
\(\|\Sigma\|=O(\delta/X^2)\). It is conditional on (4) and the
uniform complement inputs, all explicit here and in the linked notes.
It need not be nonzero: trace nonvanishing remains unproved.

For a reflection-parity frame, \(b_i=a_i\) in the even sector and
\(b_i=-a_i\) in the odd sector. Cross-parity entries in \(\mathcal C\)
vanish, and each diagonal sector equals \(2w^2a^*a\), positive rank
at most one. In the full Schur matrix the correction is subtracted:

\[
 G_\delta-zI-\mathcal J_\delta^*\Sigma_\delta(z)\mathcal J_\delta.
\]

Thus its leading contribution lowers both parity blocks. The earlier
first-order boundary matrix is negative in the even block and positive
in the odd block; there is no contradiction between these two orders.
Retaining the actual cluster head \(G_\delta\) remains essential.

The uniformity in \(z\) also gives an eigenvalue refinement **relative
to that exact head**. Put \(h_\delta=\delta/X^2\). If
\(\|\mathcal J_\delta^*\Sigma_\delta(z)\mathcal J_\delta
-h_\delta\mathcal C\|\le\varepsilon_\delta h_\delta\) uniformly
in the gap interval, \(\varepsilon_\delta\to0\), the Feshbach inertia
identity bounds the eigenvalue counting function between those of
\(G_\delta-h_\delta\mathcal C\pm
\varepsilon_\delta h_\delta I\). Hence

\[
 \boxed{\lambda_j(A_\delta^1)
   =\lambda_j(G_\delta-h_\delta\mathcal C)+o(h_\delta),
              \qquad 1\le j\le k.}                 \tag{8}
\]

All relevant eigenvalues are in this interval eventually by the
existing cluster convergence. Counting with strict thresholds and
taking limits handles multiplicities. For \(k=1\), (8) is the
particularly concrete exact-Rayleigh prediction error

\[
 \boxed{\lambda_1(A_\delta^1)
 =\lambda_1(A_\delta^0)
   +\langle u_{0,\delta},V_\delta u_{0,\delta}\rangle
   -w^2(|a|^2+|b|^2)\frac{\delta}{X^2}
   +o(\delta/X^2).}                                 \tag{9}
\]

The two threshold gaps make the simple-cluster setting applicable
at \(q=2,3\), with the existing qualitative neighborhood argument.
For their even limiting states \(a=b\), the coefficient is
\(2w^2|a|^2\). Its numerical value and nonvanishing are not asserted.

## 4. What this does and does not advance

This supplies a normalized matrix coefficient for the full complementary
response to a new prime, using the actual endpoint traces rather than
a finite trial's endpoint behavior. It suggests a useful correction
to first-order perturbation models: the same two trace rows determine
both the first-order head matrix and the next-scale Schur matrix.

It does **not** give a second-order expansion of the actual eigenvalues
about their threshold values. The background cluster splitting and
the head trace-approximation error may be larger than \(\delta/X^2\).
Equations (8)–(9) retain the exact head, rather than replacing it by
its first-order trace approximation. For the scalar ground state,
converting (7) into a numerical coefficient
still requires actual trace enclosures. Neither a new positive window
nor an all-scale margin follows from (7).

The mechanism uses standard resolvent identities and strong convergence
on a fixed finite range. No exact matching Weil-Schur coefficient was
located in the targeted comparison so far, but priority for this
application is not established. It should be included in a focused
proof/prior-art review before any claim of a novel research paper.

The additional scalar lemmas in
[WeilLocalizedResolvent.lean](../../Reinmann/WeilLocalizedResolvent.lean)
check the signed inequality (3) and transfer a named real scalar
coefficient limit through the exact scalar Schur root equation to the
Rayleigh prediction error. The operator strong limit, actual
profile convergence, and matrix/eigenvalue refinements (7)–(9) remain written analytic
results, not Lean theorems.

## 5. Additional primary-source leads checked

The targeted search combined Weil/Schur/boundary/trace, prime
second-order perturbation, logarithmic shrinking resolvents and
geometric-stable small-interval asymptotics. In addition to the earlier
readiness review, the following primary sources were opened:

- [Šikić–Song–Vondraček, 2006, author PDF](https://rsong.web.illinois.edu/pages/geostb.pdf),
  Sections 3 and 5. Near-origin potential-kernel asymptotics and
  small-ball capacity/exit estimates are established prior art.
  Section 3 assumes \(d>\alpha\); its zero-potential theorem cannot
  simply be substituted for our one-dimensional \(\alpha=2\), positive
  shifted/complementary inverse. These results nevertheless reinforce
  that the general logarithmic localization scale is not a new idea.
- [TFPT, Prime Front, Sections 19–21](https://www.fixpoint-theory.com/prime-front).
  This author-maintained diary already discusses Schur dressing at
  prime-atom entry using finite probes and labels those explorations
  as sandbox work. No actual normalized renewal-trace Gram limit
  matching (7) was identified in those sections. Its code and claimed
  certificates were not audited; its broad prime/Schur program is
  prior disclosure, not an analytic input to our proof.
- [Connes–Consani–Moscovici, Zeta Spectral Triples](https://arxiv.org/abs/2511.22755),
  title, abstract and bibliographic record. This is a separate spectral
  realization/convergence program. Only its abstract was checked in
  this continuation; a full theorem-level comparison remains open.

No exact match located in this limited check is not evidence of
priority. These leads narrow the possible contribution to the precise
actual-Weil trace/Schur transfer, and add specific sources to the
remaining full comparison before a manuscript claim.
