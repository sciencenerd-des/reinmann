# A form-core route from finite real-zero transforms to the true ground state

Date: 11 October 2026. Status: written argument, not Lean formalization or a novelty claim. This supplies a precise alternative to assuming an operator core solely to pass to a fixed-support Fourier limit. It does not prove the growing-support Xi limit.

## Statement

Let q be a closed lower-bounded real quadratic form on H=L2(0,L), with associated self-adjoint operator A. Suppose A has a simple isolated lowest eigenvalue λ0 and real unit ground vector u, invariant under reflection x↦L−x. Let λ1>λ0 bound the rest of the spectrum. Assume:

1. The spaces E_N spanned by exp(2πinx/L), −N≤n≤N, are contained in the form domain; their increasing union is a form core.
2. q commutes with conjugation and reflection.
3. Whenever a restriction to E_N has a simple even minimum, its minimizing trigonometric polynomial, extended by zero outside (0,L), has a Fourier transform with only real zeros.

Then the Fourier transform of u has only real zeros. No operator-core claim is needed for this statement.

Assumption 3 is supplied by [Connes–van Suijlekom, Theorem 5.6](https://arxiv.org/html/2511.23257) if the finite real symmetric matrix has off-diagonal entries (b_i−b_j)/(i−j), with b_−i=−b_i and even diagonal. Subtracting its minimum eigenvalue changes only the diagonal, preserving that structure. A different finite matrix model must establish its own version of assumption 3.

## Proof

Write λ_N=min{q(v):v∈E_N, ||v||=1}. Form-core density gives unit approximants to u in the form norm. They show λ_N↓λ0. This uses continuity of q in a shifted form norm, not convergence in the graph norm of A.

For sufficiently large N, λ_N<λ1. There is at most one eigenvalue of q restricted to E_N below λ1, counted with multiplicity. Indeed, if a two-dimensional subspace had energy below λ1, it would contain a nonzero vector orthogonal to u, contradicting the full complementary bound q(v)≥λ1||v||² there. Hence λ_N is simple.

Choose a real unit minimizer v_N. Reflection preserves its one-dimensional eigenspace, so v_N is either even or odd. The odd case makes v_N orthogonal to the even vector u and again forces λ_N≥λ1. Therefore v_N is even.

Orient v_N so c_N=⟨v_N,u⟩≥0, and write v_N=c_Nu+w_N, w_N⊥u. The ground eigenvector equation holds against every form-domain vector. It gives

\[
 \lambda_N=q(v_N)
 \ge\lambda_0c_N^2+\lambda_1\|w_N\|^2,
 \qquad c_N^2+\|w_N\|^2=1.
\]

Thus

\[
 \|w_N\|^2\le\frac{\lambda_N-\lambda_0}{\lambda_1-\lambda_0},
 \qquad
 \|v_N-u\|^2=2(1-c_N)\le2\|w_N\|^2\to0.
\]

Center the coordinate by x↦x−L/2. Translation multiplies the Fourier transform by a nonvanishing exponential and does not change zeros. Cauchy–Schwarz gives, for |Im z|≤Y,

\[
 |\widehat v_N(z)-\widehat u(z)|
 \le\left(\int_{-L/2}^{L/2} e^{2Yx}\,dx\right)^{1/2}
       \|v_N-u\|_2
 =\sqrt{L}\,W(L,Y)\|v_N-u\|_2,
\]

where W(L,Y)=sqrt(sinh(LY)/(LY)), with W(L,0)=1. The transforms converge locally uniformly on the complex plane. Each approximating transform has only real zeros by assumption 3. The limit is not identically zero because the Fourier transform is injective on compactly supported L2 functions and ||u||=1. Hurwitz on each open half-plane now excludes nonreal zeros of the limit. ∎

## Application boundary for the Weil work

The existing [fixed-support form-core note](FIXED_SUPPORT_FORM_CORE_2026_09_23.md) supplies the relevant density argument after identifying the logarithmic closed form. The [full-window comparison proof](WINDOW_POSITIVITY_PROOF_2026_10_07.md) and the new [ground-state enclosure](FULL_GROUND_FOURIER_2026_10_11.md) provide numerical inputs to a simple-even ground-state argument at two thresholds, using the full complement.

For the real-zero conclusion, identify the exact full Fourier restrictions with the structured matrices, as follows. The Legendre comparison matrices used to bound eigenvalues are not those Fourier restrictions and must not be substituted for them.

## Exact Fourier matrix identification

Use the normalized complex Fourier basis e_n(x)=L^-1/2 exp(2πinx/L) on (0,L). The geometric matrix formula implemented by `certified_weil.entry` uses, for m≠n,

\[
 c_{mn}(r)=-\frac{2r}{L}\cos\frac{\pi(m+n)r}{L}
            \operatorname{sinc}\frac{\pi(m-n)r}{L}
 =-\frac{\sin(2\pi mr/L)-\sin(2\pi nr/L)}{\pi(m-n)}.
\]

The equality is the sine-difference identity, with sinc continued at zero. Let

\[
 K(r)=2\cosh(r/2)-\frac{e^{r/2}}{2\sinh r},\qquad
 \omega_n=2\pi n/L,
\]

and define the real sequence

\[
 b_n=-\frac1\pi\int_0^L K(r)\sin(\omega_n r)\,dr
     +\frac1\pi\sum_{p^k<e^L}\frac{\log p}{\sqrt{p^k}}
                        \sin(\omega_n\log(p^k)).
\]

The integral is convergent: K(r)=−1/(2r)+O(1) at zero and sin(ω_nr)=O(r). The prime sum is finite, b_0=0, and b_−n=−b_n.

For an off-diagonal entry, c_mn(0)=0, so the archimedean diagonal subtraction is absent. The geometric Weil identity is exactly

\[
 A_{mn}=\int_0^L K(r)c_{mn}(r)\,dr
       -\sum_{p^k<e^L}\frac{\log p}{\sqrt{p^k}}
                         c_{mn}(\log(p^k))
       =\frac{b_m-b_n}{m-n}.
\]

For diagonal entries the correlation is 2(1−r/L)cos(ω_nr), with the usual regularization at zero. It is invariant under n↦−n, so A_−n,−n=A_nn. The diagonal scalar shift by a finite minimum eigenvalue preserves that property. All entries are real and symmetric. A prime exactly at e^L contributes zero at the support endpoint and may be omitted, consistently with the code.

This identifies the required matrix pattern **for every finite rank**, using the exact geometric form formula rather than sampled numerical identities. The analytic dependency is the geometric Weil form identity and its closed realization already used in the window proof. The sine-difference step is independently checked symbolically in `verification_2026_10_11_fourier_ground_state/sine_difference_identity.json`; that check is not a formalization of the analytic functional.

Consequently the local simple-even ground states at C=2 and C=3 have Fourier transforms with only real zeros, under the same written form-realization and comparison arguments. This is a local application of established finite real-zero mathematics, not a new RH theorem or novelty claim.

This argument therefore clarifies how a **form-core** theorem can suffice for the limit step. It does not silently infer essential self-adjointness on trigonometric polynomials from form density, and it does not formalize the operator identities in Lean. The next global obstruction is still a quantitative comparison with an Xi-producing arithmetic candidate as L grows.
