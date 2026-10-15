# An operator-norm robustness obstruction at multiplicative C=3.2

This note gives D5 a precise, limited meaning. It concerns the full prime-defined Weil form on the additive window of length \(\log(16/5)\), with its written closed-form realization \(A=A_{16/5}\). It does not concern additive support length 3.2.

For a nonnegative self-adjoint operator \(A\), define its additive robustness radius by

\[
 r_*(A)=\sup\{r\ge0:\ A+E\ge0\text{ for every bounded self-adjoint }E
                      \text{ with }\|E\|\le r\}.
\]

**Proposition.** If a nonzero \(f\in D(q_A)\) satisfies

\[
 q_A(f)/\|f\|^2\le\varepsilon,
\]

then \(r_*(A)\le\varepsilon\). More concretely, for every \(\rho>\varepsilon\), the bounded rank-one self-adjoint perturbation

\[
 E=-\rho P_f,\qquad P_f v=f\langle f,v\rangle/\|f\|^2,
\]

has norm \(\rho\) and makes the form of (A+E) negative on \(f\).

**Proof.** \(P_f\) is an orthogonal rank-one projection, so \(E\) has the stated norm and symmetry. Bounded self-adjoint perturbations leave the form domain unchanged. Direct evaluation gives

\[
 (q_A(f)+\langle f,Ef\rangle)/\|f\|^2
 \le\varepsilon-\rho<0.
\]

Thus no radius larger than \(\varepsilon\) has the defining property. This is an elementary variational fact, not a new abstract obstruction theorem.

**Certified instance.** The explicit 17-coefficient even cosine trial in the C=16/5 row of [full_clusters.json](verification_2026_10_12_cluster/full_clusters.json) has

\[
 0<q_A(f)/\|f\|^2<8.112\times10^{-9}.
\]

Its coefficients are exact decimal rationals. The interval verification integrates the actual geometric form at the target support, with both in-window primes 2 and 3, the archimedean term and pole term. A numerical eigensolver selects the coefficients; only the subsequent Arb quotient supplies the bound. The test suite recomputes that quotient from the integration balls.

Consequently \(r_*(A)\le8.112\times10^{-9}\). In particular, the explicit perturbation \(E=-10^{-8}P_f\) makes the normalized form strictly less than \(-1.888\times10^{-9}\). No proof claiming positivity for **every** bounded self-adjoint perturbation of norm \(10^{-8}\) can hold for this operator.

The independently replayed full lower comparison at a containing window supplies \(A\ge\ell I\), with \(\ell>9\times10^{-13}\), under the same written comparison and form-identification dependencies. Thus the present certificates also give the coarse two-sided enclosure

\[
 9\times10^{-13}\le r_*(A)\le8.112\times10^{-9}.
\]

The lower endpoint follows immediately from \(q_A(v)+\langle v,Ev\rangle\ge(\ell-\|E\|)\|v\|^2\). The proposition alone needs no positivity assumption to construct its negative perturbation; positivity is used to interpret \(r_*\) and its lower endpoint.

This result limits norm-error methods that promise positivity uniformly over an unrestricted perturbation ball. It does not exclude exact identities, signed interval computations with much smaller errors, a structured arithmetic perturbation class, or a proof of RH. The cluster's external gap can be comfortably positive while this robustness radius remains small: those certify different properties.

The statement is a written proof with Arb arithmetic, not a Lean theorem about the Weil operator. Source, input and validation hashes are in the [verification manifest](verification_2026_10_12_cluster/manifest.json).
