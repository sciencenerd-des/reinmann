# The compact-support core for the logarithmic comparison form

Date: 7 October 2026. This is a written proof of a standard density
step needed in the Weil trace analysis, not a novelty claim or a Lean
formalization. It clarifies the Friedrichs realization used in
[the cluster argument](DEGENERATE_CLUSTER_PRIME_ENTRY_2026_10_07.md).
It does not prove the separate kernel identification or renewal theorem.

Let \(I=(-a,a)\), \(a>0\), and use the unitary Fourier transform on
\(L^2(\mathbb R)\). Put

\[
 b(\xi)=\tfrac12\log(1+\xi^2),\qquad
 \mathcal Q_I=\{u\in L^2(\mathbb R):u=0\ {\rm a.e.\ on}\ I^c,\
       \int_\mathbb R b(\xi)|\widehat u(\xi)|^2\,d\xi<\infty\}.
\]

Its Hilbert norm is
\(\|u\|_{\mathcal Q}^2=\int(1+b(\xi))|\widehat u(\xi)|^2d\xi\).
The form \(q_B(u)=\int b|\widehat u|^2\) restricted to this space
is nonnegative and closed: the whole-line weighted Fourier space is
complete, and the zero-support condition is closed in \(L^2\), hence
in the stronger form norm.

**Form-core lemma.** \(C_c^\infty(I)\) is dense in \(\mathcal Q_I\)
for this norm.

**Proof.** First shrink the support, then mollify.
For \(0<r<1\), define \(D_ru(x)=r^{-1/2}u(x/r)\).
Its Fourier transform is \(r^{1/2}\widehat u(r\xi)\), so

\[
 \|D_ru\|_{\mathcal Q}^2
 =\int_\mathbb R[1+b(\eta/r)]|\widehat u(\eta)|^2\,d\eta
 \le(1+|\log r|)\|u\|_{\mathcal Q}^2.                 \tag{1}
\]

The inequality follows from
\(|b(\eta/r)-b(\eta)|\le|\log r|\), by differentiating with
respect to \(\log r\).
Dilations are strongly continuous on the whole weighted Fourier
space at \(r=1\). Here are the density details: smooth compactly
supported functions of frequency are dense in
\(L^2((1+b(\xi))d\xi)\), by frequency truncation and ordinary smooth
approximation on compact sets where the weight is bounded above
and below. For these functions, dilation continuity follows from
dominated convergence on a common compact frequency interval.
Equation (1) extends it to all of the weighted space by a
three-term approximation argument.
Consequently \(D_ru\to u\) in form norm as \(r\uparrow1\).

The function \(D_ru\) is supported in \([-ra,ra]\), strictly inside
\(I\). Choose a nonnegative smooth mollifier \(\phi\), supported
in \([-1,1]\), with integral one, and put
\(u_{r,\epsilon}=\phi_\epsilon*D_ru\), where
\(0<\epsilon<(1-r)a\). This belongs to \(C_c^\infty(I)\).
Its Fourier multiplier relative to \(D_ru\) is
\(m(\epsilon\xi)=\int\phi(x)e^{-i\epsilon\xi x}dx\).
We have \(|m|\le1\) and \(m(\epsilon\xi)\to1\).
Dominated convergence with dominating function
\(4(1+b)|\widehat{D_ru}|^2\) proves
\(u_{r,\epsilon}\to D_ru\) in form norm for fixed \(r\).
Choose \(r_n\uparrow1\) and then sufficiently small \(\epsilon_n\)
to obtain the required sequence. \(\square\)

**Bounded-perturbation consequence.** Suppose the full geometric-side
Weil identity is verified on \(C_c^\infty(I)\) as

\[
 Q_W(u)=q_B(u)+\langle u,E_Iu\rangle,\qquad
 E_I=-cI+K_I-S_I,
\]

where \(E_I\) is bounded and self-adjoint on \(L^2(I)\).
Then its closure has precisely the form domain \(\mathcal Q_I\).
Indeed, for \(\alpha>\|E_I\|+1\),

\[
 q_B(u)+\|u\|^2
 \le Q_W(u)+\alpha\|u\|^2
 \le q_B(u)+(\alpha+\|E_I\|)\|u\|^2,
\]

so the two form norms are equivalent. The density lemma proves that
the closure of the test-space form is the stated bounded perturbation
on the entire domain. Its associated operator is
\(B_I+E_I\) with operator domain \(\mathfrak D(B_I)\), by the
bounded self-adjoint perturbation theorem and the form representation
identity. This identifies the Friedrichs realization once the
test-space kernel/form identity has independently been established.

Several distinctions matter:

- This proves a **form core**, not an operator core. Form density
  does not by itself prove convergence in an operator graph norm.
- The comparison operator is the exterior-Dirichlet restriction of
  the whole-line logarithmic multiplier. It is not the spectral
  logarithm of the interval Dirichlet Laplacian.
- Smooth or polynomial trial functions on the closed interval,
  extended by zero, can belong to the form domain despite jumps at
  the endpoints: their Fourier transforms are \(O(1/|\xi|)\).
  They need not possess an eigenfunction's normalized renewal trace.
- This density proof does not identify the full Weil kernel, compute
  traces, imply positivity, or address RH. It supplies one exact
  domain/closure dependency for those separate arguments.
