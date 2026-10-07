# Renewal endpoint traces for the full Weil operator

Date: 7 October 2026. Status: proposed analytic theorem with a written
proof, requiring independent review. The Green formula and renewal
theory used below are established prior art. Their application here is
not an established novelty claim. No new positive window or RH proof.

This continues [the boundary-activation note](BOUNDARY_REGULARITY_PRIME_ACTIVATION_2026_10_07.md).
That note left the existence of renormalized endpoint limits open. The
argument below proposes to supply those limits, including a uniform
error for bounded families of eigenfunctions. A common leading
coefficient for two moving minimizing states still requires convergence
of their endpoint products; fixed-interval trace existence alone does
not imply that convergence.

## 1. The comparison process and the exact normalization

Use the exterior-Dirichlet restriction of the whole-line symbol

\[
 B(\xi)=\tfrac12\log(1+\xi^2),\qquad
 \nu(z)=\frac{e^{-|z|}}{2|z|}.
\]

Let H=(0,infinity), and let V be the ascending ladder-height renewal
function, with the symmetric Wiener–Hopf normalization

\[
 \kappa(\lambda)=\exp\left\{\frac1\pi\int_0^\infty
 \frac{\lambda\log B(\xi)}{\lambda^2+\xi^2}\,d\xi\right\},
 \qquad \int_{[0,\infty)}e^{-\lambda y}\,dV(y)=\kappa(\lambda)^{-1}.
 \tag{1}
\]

Write v=V'. The renewal density is completely monotone, hence positive,
continuous and decreasing on (0,infinity); V(0)=0. The exact half-line
Green formula is

\[
 G_H(x,y)=\int_0^{x\wedge y}v(x-s)v(y-s)\,ds. \tag{2}
\]

These are classical fluctuation-theory inputs, not new lemmas of this
project. See [Grzywny–Ryznar, Proposition 3.2 and Lemma 4.3](https://arxiv.org/pdf/1107.0745).
Their exponent is log(1+xi^2); ours is half of it. Consequently our V is
sqrt(2) times theirs, and our Green kernel is twice theirs. Omitting
this factor changes the proposed prime coefficient.

## 2. A trace lemma for signed bounded forcing

Suppose F belongs to L-infinity(H) intersect L1(H), real or complex,
and M=||F||_infinity. Define

\[
 H_F(s)=\int_0^\infty v(t)F(s+t)\,dt,
 \qquad \tau(F)=H_F(0).
\]

These integrals are absolutely convergent: the portion t<1 is bounded
by M V(1), and the remaining portion by v(1)||F||_1. The latter bound
also holds uniformly for every s>=0.

Monotonicity of v gives the particularly useful estimate

\[
 |H_F(s)-H_F(0)|\le 2M V(s). \tag{3}
\]

Indeed, after shifting the first integral, its difference from H_F(0)
is bounded by

\[
 M\int_0^s v(y)\,dy
 +M\int_s^\infty [v(y-s)-v(y)]\,dy.
\]

The integrand in the second term is nonnegative. Its integral up to T
is V(T-s)-V(T)+V(s)<=V(s). Monotone convergence gives (3), without
assuming F continuous or nonnegative. Applying the same argument to
F(s0+.) proves continuity of H_F at every s0>=0.

Fubini's theorem and (2) now give

\[
 (G_HF)(x)=\int_0^x v(x-s)H_F(s)\,ds,
 \qquad
 \left|\frac{(G_HF)(x)}{V(x)}-\tau(F)\right|
       \le 2M V(x). \tag{4}
\]

Absolute Fubini is justified by first using |F|: its inner H function
is bounded by M V(1)+v(1)||F||1, and the outer integral has mass V(x).
Thus (4) proves existence of a finite endpoint trace for Green
potentials, with a quantitative error. It uses neither a boundary
Harnack theorem nor positivity of the solution.

## 3. Localizing an actual Weil eigenfunction

On I=(0,L), after translating the centered interval, the full operator
in the previous note is

\[
 A_I=B_I-cI+K-S,\qquad c=\log(2\pi).
\]

Keep the full pole kernel in K and all active prime translations in S.
If A_I u=lambda u and u is bounded, then

\[
 B_Iu=g=(\lambda+c)u-Ku+Su\in L^\infty(I). \tag{5}
\]

Boundedness of u is provided by the written semigroup-domination
argument in the previous note. In particular, this step does not
assume a positive Weil semigroup or a positive lowest eigenvalue.

Choose a bounded smooth real cutoff chi, equal to 1 for x<=r and to
0 for x>=2r, with 0<=chi<=1 and 2r<L. Extend u by zero to the line,
and put w=chi u. On H, in the weak sense,

\[
 B_Hw=F=\chi g+[B,\chi]u,
 \quad [B,\chi]u(x)=\int_\mathbb R
        [\chi(x)-\chi(y)]u(y)\nu(x-y)\,dy. \tag{6}
\]

There is no principal-value issue in the commutator: Lipschitz
regularity cancels the singularity. In fact

\[
 \|[B,\chi]u\|_\infty
 \le \operatorname{Lip}(\chi)\|u\|_\infty
             \int_\mathbb R |z|\nu(z)\,dz
 =\operatorname{Lip}(\chi)\|u\|_\infty. \tag{7}
\]

The same absolute-kernel bound is a Schur L2 bound. Multiplication by
chi preserves the form domain, by expanding differences of chi u and
using the finite integral of min(1,z^2)nu(z). Equation (6) follows
first against smooth compactly supported test functions and then by
form-density. Its L2 right-hand side puts w in D(B_H).

For x>=2r+1, chi(x)=0 and

\[
 |F(x)|\le \|u\|_\infty r e^{2r}e^{-x}.
\]

On the remaining bounded interval F is bounded by (7) and (5).
Hence F belongs to L-infinity intersect L1 intersect L2 on H, with

\[
 M_F\le\|g\|_\infty+\operatorname{Lip}(\chi)\|u\|_\infty. \tag{8}
\]

It remains to justify w=G_HF, rather than insert an unproved inverse at
spectral parameter zero. B_H is nonnegative and has zero kernel: its
form is the integral of B(xi)|w-hat(xi)|^2, and B(xi)>0 except at a
set of measure zero. For epsilon>0 the spectral theorem gives

\[
 (B_H+\varepsilon)^{-1}F
   =w-\varepsilon(B_H+\varepsilon)^{-1}w\longrightarrow w
       \quad\hbox{in }L^2.
\]

The positive killed comparison semigroup gives resolvent kernels
G_H^epsilon<=G_H. Their integrals against F converge pointwise to
G_HF, by domination with G_H|F|, already proved finite above.
An L2-convergent subsequence identifies w=G_HF almost everywhere.
The convolution expression in (4) is continuous in x>0 and provides
the continuous representative, agreeing with the PDE representative
used in the earlier note. This supplies the required zero-resolvent
argument even though B_H has no spectral gap.

Combining (4)–(8), because chi=1 near zero, yields

\[
 \boxed{\quad \tau_-(u)=\lim_{x\downarrow0}\frac{u(x)}{V(x)}
          =\int_0^\infty v(y)F(y)\,dy,\qquad
 \left|\frac{u(x)}{V(x)}-\tau_-(u)\right|\le 2M_F V(x).
          \quad} \tag{9}
\]

Reflection supplies the right trace tau_plus. Different permissible
cutoffs give the same trace, since the left side is intrinsic.
The proof works for sign-changing and complex eigenfunctions.

For L in a compact subinterval of (0,infinity), and normalized
eigenfunctions with eigenvalues bounded above, the previous note
bounds eigenvalues below and u uniformly in L-infinity. It also bounds
K and S uniformly, including when one prime term is omitted. Fix r
below one quarter of the shortest length. Equations (8)–(9) then
give uniform trace errors and uniformly bounded traces. None of these
constants divide by an eigenvalue or a spectral gap.

## 4. Why V has the precise logarithmic coefficient one

The exact normalization is derivable directly from (1); a comparability
statement V(x) comparable to 1/sqrt(log(1/x)) is insufficient here.
Set lambda=exp(T). With xi=lambda exp(z), (1) becomes

\[
 \log\kappa(e^T)=\frac1\pi\int_\mathbb R
 \frac{\log[\tfrac12\log(1+e^{2(T+z)})]}{2\cosh z}\,dz.
\]

The measure dz/(2*pi*cosh z) has mass 1/2. Subtract (log T)/2.
For z>=-T/2 the integrand's logarithmic difference tends to zero
pointwise and is bounded by a constant plus log(2+|z|), using

\[
 t\le\tfrac12\log(1+e^{2t})\le t+\tfrac12\log2
       \quad(t\ge0).
\]

Dominated convergence applies on that region. On z<-T/2, use the
bound |log[log(1+e^{2t})/2]|<=C+2|t| for t<=0, and a linear
bound for t>=0. The omitted tail is O((T+1)e^{-T/2}). Thus

\[
 \kappa(\lambda)\sim\sqrt{\log\lambda}. \tag{10}
\]

For completeness, a short Laplace argument replaces a Tauberian
black box. Put J(lambda)=1/kappa(lambda). For any fixed h>0,

\[
 V(x)\le e^h J(h/x),\qquad
 V(x)\ge J(h/x)-e^{-h/2}J(h/(2x)). \tag{11}
\]

The first follows by integrating e^{-hy/x} over y<=x; the second
splits the Laplace–Stieltjes integral at x and bounds its tail by
e^{-h/2} times the integral at h/(2x). By (10), both J(h/x)/J(1/x)
and J(h/(2x))/J(1/x) tend to one. Let h decrease to zero in the
upper bound and increase to infinity in the lower bound. Consequently

\[
 V(x)\sqrt{\log(1/x)}\longrightarrow1. \tag{12}
\]

This proves the logarithmic normalization, and in particular slow
variation of V at zero. Combining (9) and (12) establishes the
existence of u(x)sqrt(log(1/x)) limits. No rate for (12) is asserted.

## 5. Endpoint overlap and the remaining two-state condition

For 2a=log(q)+delta and a centered eigenfunction u, let

\[
 g_u(\log q)=\int_0^\delta
       \overline{u(-a+\delta-t)}u(a-t)\,dt,
 \quad W(\delta)=\int_0^\delta V(\delta-t)V(t)\,dt.
\]

Equation (9), with eta_delta=2 M_F V(delta) using a common bound
for both endpoints, gives

\[
 \left|g_u(\log q)-\overline{\tau_-(u)}\tau_+(u)W(\delta)\right|
 \le [\eta_\delta(|\tau_-|+|\tau_+|)+\eta_\delta^2]W(\delta).
 \tag{13}
\]

This holds uniformly for the compact families just described, even
when u and a vary with delta. Monotonicity gives
W(delta)<=delta V(delta)^2. For fixed epsilon in (0,1/2), restricting
the integral to [epsilon delta,(1-epsilon)delta] gives the lower bound
(1-2epsilon)delta V(epsilon delta)^2. Slow variation and then
epsilon decreasing to zero prove

\[
 W(\delta)\sim\frac{\delta}{\log(1/\delta)}. \tag{14}
\]

For each delta compare the full and q-omitted forms on the SAME
interval, with minimizing states u1_delta and u0_delta and eigenvalues
lambda1_delta and lambda0_delta. With wq=Lambda(q)/sqrt(q), the
previously checked variational bracket and (13) imply a bracket for
(lambda1_delta-lambda0_delta)/W(delta) between

\[
 -2w_q\operatorname{Re}(\overline{\tau_-(u1_\delta)}\tau_+(u1_\delta))
 \quad\hbox{and}\quad
 -2w_q\operatorname{Re}(\overline{\tau_-(u0_\delta)}\tau_+(u0_\delta)),
 \tag{15}
\]

with errors tending uniformly to zero. If BOTH endpoint products
converge to the same real part c0, then

\[
 \lambda1_\delta-\lambda0_\delta
 =-2w_q c_0\frac{\delta}{\log(1/\delta)}
       +o\!\left(\frac{\delta}{\log(1/\delta)}\right). \tag{16}
\]

The common-product premise is explicit. At a multiple lowest
eigenvalue, two moving minimizers can select different vectors;
trace existence by itself does not remove this issue. Nor does (16)
compute the TOTAL eigenvalue change from changing the interval.

There is a useful sufficient condition that replaces trace convergence
with ordinary L2 convergence. Suppose lengths stay in a compact cell,
the two zero-extended, endpoint-aligned minimizing states converge in
L2 to the same state, and their eigenvalues converge to the same value.
The uniform bounds already proved give a common M_F and common
exponential tail for their cutoff forcings. For a fixed cutoff, the
commutator in (6) is bounded on L2. The localized K term is also bounded
on L2, and the previously active translations are fixed bounded
operators. The newly active translation contributes only on a layer of
length delta, so its L2 norm on these bounded states is O(sqrt(delta)).
Thus both cutoff forcings converge to the same F in L2(H).

Their traces then converge to tau(F). To see this, split the integral
of v(y)(F_n-F)(y) into (0,epsilon), (epsilon,R), and (R,infinity).
The first part is bounded uniformly by 2 M_F V(epsilon); the middle
part tends to zero by Cauchy–Schwarz since v is bounded there; the
last part tends uniformly to zero by the common exponential tail and
boundedness of v away from zero. This proves trace continuity under
these precise assumptions. One must still establish common L2
convergence of the actual minimizing states. Simplicity plus suitable
compact spectral convergence is a possible way to do that; it has not
been supplied by the Lean lemmas or assumed at a degenerate threshold.

## 6. Prior art, proof status, and the next useful target

The renewal function, its complete monotonicity, Wiener–Hopf formula
and half-line Green factorization are from the cited 2011 paper and
its fluctuation-theory references. The simple signed-potential trace
lemma (3)–(4) should be presumed standard until a dedicated check
establishes otherwise. [The logarithmic-Laplacian boundary paper](https://arxiv.org/html/2401.18033v2)
supplies the earlier optimal upper scale; it is not being credited
with a trace limit it does not state. [Kim et al.](https://arxiv.org/html/2607.24830)
study numerical boundary behavior for the Weil operator. Searches on
7 October for Weil eigenfunctions with renewal endpoint traces did
not locate the transfer (6)–(16). An unsuccessful search does not
establish novelty. None of these papers is being cited as proving RH.

A tempting further shortcut through a logarithmic-Laplacian Pohozaev
identity must be excluded: [Arora–Giacomoni–Vaishnavi, arXiv:2411.15985v2](https://arxiv.org/abs/2411.15985v2)
was withdrawn on 26 April 2025 because of an error in the proof of that
identity. Its indexed first-version text is not evidence of an available
theorem. We do not use it, or assert a Hadamard formula or total support
derivative from the endpoint trace established in this proposal.

The companion Lean module proves a genuine weighted integral error
lemma and its trace-limit consequence, and names the representation
inputs. It does not formalize (1)–(2), the cutoff operator identity,
spectral resolvent argument, Wiener–Hopf asymptotic, or the full Weil
transfer. The analytic proof here remains proposed and independently
unreviewed. The previous Arb kernel checks concern only the earlier
comparison-kernel normalization, not this trace theorem.

The next substantive target is a usable error certificate for endpoint
traces, with explicit renewal enclosures and forcing constants, followed
by a basis enriched with the two boundary profiles while retaining the
polynomial moment-cancellation subspace. For a single coefficient in
(16), prove continuity of endpoint products for the relevant minimizing
states, including possible degeneracy. No argument above rules out a
zero eigenvalue between prime thresholds, controls an all-scale prime
budget, or supplies cofinal positive windows. Those remain essential
obstructions to an RH proof.
