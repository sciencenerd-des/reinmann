# Boundary regularity as a candidate improvement to the Weil-window route

Date: 7 October 2026. Status: a proposed theorem with a written proof via
semigroup domination and published boundary regularity, checked algebra in
a separate Lean module, and a targeted prior-art review. The analytical
proof needs independent review and is not Lean-formalized. No new window,
RH proof, or established novelty claim. The proposal transfers optimal
logarithmic boundary regularity to actual Weil eigenfunctions and uses
**two minimizing states**, rather than a global perturbation norm, to
control a newly active prime power.

## What the literature check eliminated

| Proposed idea | Closest source checked | Decision |
|---|---|---|
| Schur continuation from a positive window | [Kuberwastaken, CONTINUATION, Sections 4–5](https://github.com/Kuberwastaken/riemann/blob/main/CONTINUATION.md) | Already proposed, with a margin-persistence obstruction. Do not claim novelty. |
| A new prime acts only on thin endpoint layers | Same source, Theorem 5.1 | Exact localization is already stated. Do not claim novelty. |
| Continuity or a first-failure zero mode | [Suzuki, Theorem 1.3 and discussion](https://arxiv.org/html/2606.09096v2) and Yoshida as cited there | Already known. Do not present this as a new RH reduction. |
| Smooth numerical passage through the first prime threshold | [Kim et al., R7 and Sections 5.2–5.4](https://arxiv.org/html/2607.24830) | Already observed numerically. That paper leaves analytic boundary behavior open and warns against fitting boundary exponents. |
| The inverse-square-root logarithmic boundary scale | [Hernández-Santamaría, López Ríos, Saldaña, Theorem 1.1](https://arxiv.org/html/2401.18033v2) | Established for bounded weak logarithmic-Laplacian solutions with bounded forcing. The exponent is not our discovery. |
| A logarithmic boundary Hardy inequality | [Dyda, Jarohs, Sk](https://arxiv.org/html/2411.11181v3), Section 5 | Established. This is different from an eigenfunction-specific pointwise bound. |
| A positive comparison semigroup for a logarithmic Schrödinger operator | [Feulefack, logarithmic Schrödinger operator](https://arxiv.org/html/2112.08783), Introduction | The positive Lévy generator and its variance-Gamma semigroup are classical. The candidate is their domination-based application to the sign-indefinite Weil perturbation. |

The candidate combination is narrower: a rigorous transfer to the full
pole-inclusive Weil operator, a quantitative prime-entry bound for its
minimizers, and a possible leading coefficient in terms of renormalized
endpoint values. The checked sources did not supply that complete theorem.
This is **not proof of novelty**. The checks include primary papers and an
author-maintained research repository; the latter is prior disclosure, not
independent peer review. Additional searches for this combination and for
Weil boundary regularity did not establish priority either way.

## 1. Boundedness without a positive Weil semigroup

Put `c=log(2*pi)` and let B be the whole-line operator with symbol
`b(t)=log(1+t^2)/2`. Its Lévy density is `exp(-|x|)/(2|x|)`.
Let B_I be its exterior-Dirichlet realization on `I=(-a,a)`, obtained by
restricting its quadratic form to zero-extended functions. This is NOT
the spectral logarithm of the ordinary Dirichlet Laplacian.

The actual Weil operator has the exact decomposition

\[
 A_a=B_I-cI+K-S. \tag{0a}
\]

Here S is the positive-in-order sum of the supported prime translations,
including their adjoints, with coefficients `w_q=Lambda(q)/sqrt(q)`.
The integral kernel of K is

\[
 k(x-y)=k_R(x-y)+2\cosh((x-y)/2),
 \quad
 k_R(x)=\frac{e^{-|x|}}{2|x|}
          -\frac{e^{|x|/2}}{e^{|x|}-e^{-|x|}},\qquad x\ne0.
\]

The continuous value of k_R at zero is `-3/4`. This follows by comparing
the exact geometric-side archimedean kernel with B's Lévy kernel. The
identity coefficient is `-c`: equivalently, the difference of the Fourier
symbols tends to `-log(2*pi)` at infinity. This is the full pole kernel;
its negative odd-sector rank-one term has not been removed.

There is an elementary global bound `|k_R(x)|<=5/4`. For `x>0`, write

\[
 -k_R(x)=e^{-x/2}\left[
 \frac1{1-e^{-2x}}-\frac1{2x}
       +\frac{1-e^{-x/2}}{2x}\right].
\]

The first difference in brackets is between 0 and 1, by the elementary
exponential inequalities. The last quotient is between 0 and 1/4.
Thus on I we may use

\[
 k_* = 5/4+2\cosh a,\quad
 \kappa=2ak_*,\quad k_{2,\infty}=\sqrt{2a}\,k_*,\quad
 m=2\sum_{q<e^{2a}}w_q.
\]

The absolute-kernel operator `|K|` has L2 norm at most kappa and maps
L2 to L-infinity with norm at most `k_(2,infinity)`. These bounds are
finite, explicit and independent of a spectral gap.

**Written semigroup proposition.** For every `t>1/2`,

\[
 \|e^{-tA_a}\|_{2\to\infty}
   \le e^{(c+m+\kappa)t}\,[C_t+t k_{2,\infty}],
 \quad
 C_t^2=\frac1{2\pi}\int_{\mathbb R}(1+\xi^2)^{-t}\,d\xi.
 \tag{0b}
\]

This is an eventual smoothing bound. No smoothing claim is made for all
small positive times, and no positivity preservation is asserted for the
Weil semigroup itself.

**Proof.** The whole-line semigroup of B has positive kernel, as follows
from the Gamma mixture of Gaussians

\[
 (1+\xi^2)^{-t/2}
   =\Gamma(t/2)^{-1}\int_0^\infty
                s^{t/2-1}e^{-s}e^{-s\xi^2}\,ds.
\]

Killing outside I gives `0<=P_t^I f<=P_t(Ef)` on nonnegative functions,
where E is zero extension. This is the ordinary domination of a killed
Lévy semigroup by its whole-line semigroup, or follows by positive
Trotter products with increasing exterior killing potentials.

First add S. Each term in its bounded-perturbation Dyson expansion is
positive. Replacing killed propagators and supported translations by
their whole-line versions only increases that term. The whole-line
translations commute with B. Hence

\[
 0\le T_t f:=e^{-t(B_I-S)}f
       \le P_t e^{tS_{\mathbb R}}Ef,
 \quad
 \|T_t\|_{\infty\to\infty}\le e^{mt},\quad
 \|T_t\|_{2\to\infty}\le e^{mt}C_t\ (t>1/2).
\]

Now let `U_t=exp[-t(B_I-S-|K|)]`. Since B_I is nonnegative and
`||S+|K|||_2<=m+kappa`, `||U_s||_2<=exp[(m+kappa)s]`.
Duhamel's identity, with the bounded kernel placed before the L-infinity
propagator, gives

\[
 U_t=T_t+\int_0^t T_{t-s}|K|U_s\,ds,
\]
\[
 \|U_t\|_{2\to\infty}
 \le e^{mt}C_t+
 k_{2,\infty}\int_0^t e^{m(t-s)}e^{(m+\kappa)s}\,ds
 \le e^{(m+\kappa)t}(C_t+t k_{2,\infty}).
\]

The signed-kernel Dyson expansion satisfies
`|exp[-t(B_I-S+K)]f|<=U_t|f|`. Restoring the constant c proves (0b).
All perturbations here are bounded on L2, and the kernel insertion maps
L2 to L-infinity immediately; no divergent small-time smoothing integral
is being used. ∎

For a normalized eigenfunction with eigenvalue `lambda<=M`, take `t=1`
and `C_1=1/sqrt(2)` to obtain

\[
 \boxed{\quad
 \|u\|_\infty\le
 e^{M+c+m+\kappa}\left[\frac1{\sqrt2}+\sqrt{2a}\,k_*\right].\quad}
 \tag{0c}
\]

The right side is huge but finite. Omitting a prime only decreases m, so
the same upper bound covers the single-prime-omitted operator. Also
`A_a>=-(c+m+kappa)I`, providing a lower bound on its eigenvalues. On a
compact support cell away from a=0, these bounds are uniform for all
eigenvalues below M. A common compactly supported unit trial function
provides such an M for the two ground-state families used below.

The standard semigroup tools are not claimed new. This argument is a
candidate application that supplies the boundedness gate without assuming
the unavailable positivity preservation of the full Weil semigroup.

## 1.1. Transfer to optimal endpoint decay

Use the Fourier convention of the committed window proof. The archimedean
symbol is

\[
 \Omega(t)=\operatorname{Re}\psi(1/4+it/2)-\log\pi.
\]

Define

\[
 r(t)=\Omega(t)-\log|t|+\log(2\pi).
\]

The classical digamma expansion gives `r(t)=O(t^-2)` at infinity. Near
zero it is `-log|t|+O(1)`. Thus `r` is integrable on the frequency line,
and its inverse Fourier transform `k` is bounded and continuous. On a
fixed finite interval `I=(-a,a)`, the remainder operator `R f=k*f`
(zero extension understood) maps L1(I) to bounded functions. In particular
it is a bounded operator on L2(I). The low-frequency singularity of
`log|t|` causes no form-domain problem on supported functions, since
`|F(t)|<=sqrt(2a)||f||2` and the logarithm is locally integrable.

Writing `L_Delta` for the exterior-Dirichlet logarithmic Laplacian with
symbol `2 log|t|`, the actual Weil operator therefore has the weak form

\[
 A_a=\tfrac12 L_\Delta-\log(2\pi)I+R+P-S,
 \quad
 S f=\sum_{q=p^k<e^{2a}}\frac{\log p}{\sqrt q}
            [f(\cdot-\log q)+f(\cdot+\log q)],
\]

where `P` is the full rank-two pole operator, with both signs retained.

**Written proposition.** If `u` is a bounded weak Weil eigenfunction on
I, with zero exterior values, then

\[
 |u(x)|\le K_a\,[\log(1/d(x,\partial I))]^{-1/2}
 \qquad(0<d(x,\partial I)<0.1).
 \tag{1}
\]

**Proof.** Its equation gives

\[
 L_\Delta u=2[(\lambda+\log(2\pi))u-Ru-Pu+Su].
\]

Every term on the right is bounded: this uses the assumed boundedness of
u, bounded convolution kernel for R, bounded pole kernel on I, and finitely
many translations in S. The logarithmic form domain agrees with that of
the exterior-Dirichlet logarithmic Laplacian up to bounded perturbations
on I. Apply the cited optimal boundary theorem to the real and imaginary
parts. Its continuity conclusion also gives the zero endpoint values. ∎

The boundedness gate is supplied by (0c), not just by membership in the
Weil operator domain. The boundary theorem's upper estimate can be written
`C_I (||u||infinity+||L_Delta u||infinity)` times the boundary weight:
its proof in Section 4 scales a fixed barrier linearly with the bounded
forcing and the bounded solution. To make this uniform on
`0<a_min<=a<=a_max`, rescale `v(y)=u(ay)` onto the fixed interval (-1,1).
The scaling identity is
`L_Delta v(y)=(L_Delta u)(ay)+2 log(a) v(y)`. The normalized eigenfunctions,
their eigenvalues and their forcing are uniformly bounded by (0c), the
lower spectral bound and the finite shift/kernel bounds. The fixed-interval
barrier estimate therefore supplies one uniform endpoint constant after
reducing the layer width if necessary. For sufficiently small physical
distance d, `log(a/d)>=log(1/d)/2` uniformly on this compact cell.

This gives the uniform upper-bound input used in (7) as written analysis.
It does **not** give existence or continuity of a nonzero limit of
`u(a-t)*sqrt(log(1/t))`. The stronger trace input in (5) remains open.

## 2. An explicit overlap kernel with two-sided bounds

For `0<delta<1`, put `H=log(1/delta)>0` and

\[
 J(H)=\int_0^1
 \frac{dv}{\sqrt{(H-\log v)(H-\log(1-v))}}.
\]

**Written lemma.**

\[
 \boxed{\quad \frac1{H+1}\le J(H)\le\frac1H.\quad} \tag{2}
\]

**Proof.** Set `A=H-log v`, `B=H-log(1-v)`. Both are at least H, which
proves the upper bound. Also
`integral sqrt(AB) <= integral (A+B)/2 = H+1`, using
`integral_0^1 -log v dv = integral_0^1 -log(1-v) dv = 1`.
Cauchy–Schwarz applied to `(AB)^(1/4)` and `(AB)^(-1/4)` gives
`1 <= (integral sqrt(AB))*J(H)`, proving the lower bound. All these
integrals are finite; their endpoint logarithms are integrable. ∎

Consequently `0<=1-H J(H)<=1/(H+1)`. In particular the model convergence
is logarithmically slow; a good power-law fit over a finite mesh is not a
reliable way to infer the true boundary behavior.

## 3. Quantitative correlation at the support edge

For a supported function on `[-a,a]`, write the genuine autocorrelation as

\[
 g(2a-\delta)=\int_0^\delta
       \overline{u(-a+\delta-t)}u(a-t)\,dt. \tag{3}
\]

If both endpoint bounds in (1) hold with constants `K_-`, `K_+` on a
layer of width delta below 0.1, (2) immediately gives

\[
 \boxed{\quad |g(2a-\delta)|
    \le K_-K_+\,\delta J(H)
    \le K_-K_+\frac{\delta}{\log(1/\delta)}.\quad} \tag{4}
\]

There is a precise leading coefficient under a **stronger** trace input.
Suppose on `0<t<delta`

\[
 |u(a-t)\sqrt{\log(1/t)}-b_+|\le\eta,
 \quad
 |u(-a+t)\sqrt{\log(1/t)}-b_-|\le\eta.
\]

Put `c=conjugate(b_-)*b_+` and
`E=eta(|b_-|+|b_+|)+eta^2`. Substitute in (3), expand the product before
taking absolute values, and apply (2). This proves

\[
 \left|\frac{H}{\delta}g(2a-\delta)-c\right|
 \le E+\frac{|c|}{H+1}. \tag{5}
\]

Thus actual endpoint trace limits imply

\[
 g(2a-\delta)=\overline{b_-}b_+
                 \frac{\delta}{\log(1/\delta)}
               +o\!\left(\frac{\delta}{\log(1/\delta)}\right).
\]

Equation (4) needs only an upper boundary estimate. Equation (5) requires
trace limits; the cited PDE theorem does not provide those limits. For a
family of eigenfunctions on varying supports, the endpoint estimates or
trace errors must be uniform on the shrinking layers. Pointwise limits
at each fixed support do not establish that uniform statement.

## 4. Turn the state estimate into a spectral estimate without a gap divisor

Fix a prime power q and let `2a=log q+delta`, with delta positive and small
enough that no other prime-power threshold intervenes. On this SAME
interval, compare the full form with the form in which only q is omitted:

\[
 Q_\delta=Q^0_\delta+V_q,
 \qquad V_q(u)=-2w_q\operatorname{Re}g_u(\log q),
 \quad w_q=\Lambda(q)/\sqrt q.
\]

Let normalized actual minimizers of these two forms be `u_delta` and
`u0_delta`, with minimum values `lambda_delta` and `lambda0_delta`.
The variational principle gives the exact bracket

\[
 \lambda^0_\delta+V_q(u_\delta)
       \le\lambda_\delta
       \le\lambda^0_\delta+V_q(u^0_\delta). \tag{6}
\]

By (0c), the transfer proposition, and the fixed-interval rescaling, BOTH
ground-state families satisfy (1) with an endpoint-product bound K
independent of small delta. Equations (4) and (6) consequently give the
following proposed theorem with its written proof:

\[
 \boxed{\quad |\lambda_\delta-\lambda^0_\delta|
       \le 2w_q K\frac{\delta}{\log(1/\delta)}=o(\delta).\quad} \tag{7}
\]

No assumption that either minimum is positive, no spectral simplicity,
and no division by a small spectral gap is used in (6)–(7). The uniform
boundary estimate is obtained through an extremely large finite constant;
this is not yet a practical numerical margin. Under common uniform trace limits, (5)
likewise squeezes a common leading coefficient through (6). For real
even states the coefficient of the new prime term is `-2w_q b^2`; for
real odd states it is `+2w_q b^2`.

This comparison isolates the new q term at the same support. It is not
the total change of the minimum as a changes. In particular, (7) does not
prove differentiability of the full support-dependent ground eigenvalue,
positivity past the threshold, or a global continuation theorem.

## 5. Why a global norm bound cannot replace these hypotheses

For every positive delta with disjoint endpoint layers, take a unit bump
h in the left layer and its translate `T_(2a-delta) h` in the right layer.
The unit vector `u=(h+T h)/sqrt(2)` has
`g_u(2a-delta)=1/2`, independent of delta. Thus the new prime perturbation
does not become small in operator norm on L2 as the layer shrinks.
Logarithmic form energy of concentrating bumps grows; these are not a
uniformly bounded family of actual low eigenfunctions. This distinction
is exactly why (7) evaluates TWO minimizing states instead of all unit
vectors. Evaluating only an approximate trial state supplies an upper
bound, not the lower side of (6).

The finite-Fourier rank-one derivative kick in this repository evaluates
nonzero endpoint values of finite trigonometric polynomials. Proposition
1 instead forces zero ordinary endpoint values for bounded continuum
eigenfunctions. The order of the rank limit and the thin-layer limit
therefore needs care. Form convergence alone does not control point
evaluation. It cannot justify interchanging these limits or extracting
the renormalized trace from finite endpoint coordinates.

## 6. Concrete next theorem and decision gates

1. Independently review the exact decomposition (0a), killed-semigroup
   domination, and the signed-kernel Dyson argument. Their written proof
   above closes the L-infinity gate without a positivity or gap premise.
   Formalizing these analytic facts is substantive work; the Lean module
   below currently proves only the finite algebra that uses them.
2. Extract usable explicit constants from the fixed-interval boundary
   barrier proof. Existence of a uniform constant suffices for the
   qualitative theorem (7); the rough exponential bound (0c) is likely too
   expensive for immediate certified window enlargement. Check the full
   novel-application claim against Weil-operator regularity literature.
3. Only then pursue trace limits and their continuity under support
   changes, to obtain a coefficient rather than an upper bound. Positivity
   of the full Weil semigroup cannot be assumed; the existing repository
   gives an explicit cross-form obstruction at larger supports.
4. Use the boundary model to enrich a finite retained space while keeping
   the original polynomial space inside it. Then the existing moment-based
   complement bound remains valid. Replacing all polynomial directions by
   weighted polynomials would lose those moment cancellations and requires
   a new complement proof. All matrix, quadrature and coupling estimates
   must be recomputed for any enrichment.

After independent review, this proposed theorem would provide rigorous
prime-threshold control and resolve part of the finite-to-continuum
boundary question, subject to further novelty adjudication. It still
would not exclude a zero eigenvalue arising between thresholds,
control the cumulative prime budget as support tends to infinity, identify
the ground-profile limit with Xi, or supply a cofinal family of positive
windows. Those remain RH-relevant obligations. Smooth prime entry alone
cannot settle them.

## 7. Formalization boundary

[WeilBoundaryActivation.lean](../../Reinmann/WeilBoundaryActivation.lean)
contains eight proved statements: general variational bracketing, transfer of a shared state-level
coefficient error, the absolute version, the elementary reciprocal-root
kernel inequalities, the normalized-kernel error implication, and
positivity of the scale `delta/log(1/delta)`, together with the geometric
exponential error and the `5/4` comparison-kernel allowance.

The semigroup smoothing and analytic transfer propositions, integral bounds, overlap asymptotics,
and the application to actual Weil eigenstates above are written
mathematics. They are not claimed to be Lean-formalized. In particular the
module does not turn an endpoint-decay hypothesis into an axiom about zeta.
Standard variational inequalities and Cauchy–Schwarz are not claimed novel.
The candidate contribution is the complete application after its missing
formalization and independent proof review, and after its priority is checked.

The separate [kernel normalization check](../../experiments/prime_spectral/check_boundary_activation_kernel.py)
uses Arb adaptive complex integration with the singularity at zero
explicitly removed. The transforms at `t=0,1/2,2,7` contain the exact
digamma-symbol differences, including the constant `log(2*pi)`. A global
tail bound `5 exp(-128/2)` accounts for the omitted spatial integral.
These four checks catch a sign, factor or identity-offset error; they do
not replace the written exact identity or prove the semigroup argument.

Replay:

```sh
lake build Reinmann.WeilBoundaryActivation Reinmann.WeilBoundaryActivationAudit
lake env lean Reinmann/WeilBoundaryActivationAudit.lean
uv run --with python-flint==0.8.0 --python 3.12 python experiments/prime_spectral/check_boundary_activation_kernel.py --output research/prime_spectral/boundary_activation_kernel_check_2026_10_07.json
```

This work is in separate new files. Existing dirty research and the
previously committed window certificates are not edited by this proposal.
