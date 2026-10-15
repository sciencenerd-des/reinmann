# Fixed-support enclosures for actual Weil ground-state Fourier transforms

Date: 11 October 2026. This continues the [frontier review](../frontier_audit_2026_10_11/FRONTIER_REVIEW.md) in the separate `codex/xi-eigenvector-reduction` worktree. It implements an actual numerical instance of the repository's existing form-level Fourier transfer. The underlying spectral estimates are standard; no novelty or RH claim is made.

## Result and trust boundary

Using freshly assembled comparison matrices, both parity sectors, and analytic bounds on the entire infinite polynomial complement, the arithmetic certificates give the following weakened public bounds. Let u_q be the real unit ground state at support length L=log(q), oriented toward the exact nine-mode cosine trial g_q from the earlier threshold work. Fourier integrals use the centered coordinate x−L/2.

| Quantity | q=2 | q=3 |
|---|---:|---:|
| Full ground eigenvalue lower bound | >0.00124999 | >3.99999·10^-8 |
| Full second eigenvalue lower bound | >0.05699999 | >4.11999·10^-6 |
| ‖u_q−g_q‖₂ | <0.05509 | <0.12407 |
| L^-1/2 ∫u_q | >0.83604 | >0.64162 |
| Raw Fourier error on abs(Im z)≤0.4 | <0.04616 | <0.13214 |
| Error after normalizing each Fourier transform at z=0, same strip | <0.14072 | <0.45309 |

The JSON retains exact rational outward endpoints. These are uniform bounds over the entire horizontal strip at each fixed support, not just sampled z values. They compare trials to the full-operator ground state through written analysis; they do not identify that ground state with the prolate/arithmetic candidate whose limit is Xi.

The trust boundary is **written infinite-dimensional operator/form analysis plus Arb-enclosed finite arithmetic**. The operator realization, compactness, form min-max principle, and spectral decomposition are not formalized by the new scalar Lean module. The finite integrals, parity inertia checks, prime content, quadrature bounds, infinite-complement allowance, and source hashes are explicit numerical dependencies.

The subsequent [orthogonality-aware transfer](ORTHOGONAL_FOURIER_TRANSFER_2026_10_11.md) strengthens the normalized profile errors to <0.05310 and <0.17867 on the same strip, and the protected means to >0.86479 and >0.68014. It uses the same state-distance and full spectral inputs. The table above preserves the initial transfer for comparison.

## Why the new calculation works despite the old residual failure

The [assembled trials](ASSEMBLED_TRIAL_FULL_RESIDUAL_2026_10_07.md) fail a sufficient endpoint-trace transfer test. Their large full residual bounds prevent tight use of the residual-to-gap estimate. The present construction instead uses the original cosine polynomial as a **form-domain** trial; no endpoint renewal repair is needed for this observable.

For a full lower-bounded operator, suppose ell≤λ0, b≤λ1, and a unit form-domain trial f has Rayleigh quotient μ<b. Write f=cu+w, where u is a unit ground vector, c≥0, and w⊥u. With t=||w||²,

\[
 \mu\ge\ell(1-t)+bt,\qquad
 t\le q:=\frac{\mu-\ell}{b-\ell}<1.
\]

The phase distance obeys the sharper bound

\[
 \|f-u\|\le d(q):=\sqrt{2(1-\sqrt{1-q})}
 =\sqrt{\frac{2q}{1+\sqrt{1-q}}}.
\]

The second expression avoids cancellation in interval arithmetic. Unlike the earlier finite transfer routine, this bound needs only a ground lower bound and a full second-level lower bound, rather than an interval upper bound for the ground eigenvalue in its denominator. A negative ell is permitted; positivity of the ground eigenvalue is not a prerequisite.

## Whole-operator spectral inputs

Fresh rational comparison half-widths are

\[
 a_2=346574/10^6>\log(2)/2,\qquad
 a_3=549307/10^6>\log(3)/2.
\]

The final comparison has frequency cutoff 128. It uses 160 Legendre modes at q=2 and 320 at q=3, with Gauss order 80, generated at 384 bits. The initial cutoff-64 calculation used 80 modes / order 64 at q=2 and 160 modes / order 80 at q=3. Their prime content includes all prime powers active in the comparison interval. Restricting back to the threshold interval makes the newly activated endpoint shift vanish almost everywhere; form min-max gives the threshold eigenvalue lower bounds.

Let G be the exact retained comparison block, β the high-frequency comparison level, E_Q the quadrature operator error, B the full cross-block allowance, and D the full omitted-block deviation. The written reduction yields

\[
 A_{\rm comparison}\ge (G\oplus\beta)-(B+D)I.
\]

Shifted interval LDL on both parity matrices certifies:

| Threshold | Finite ground shift ell_f | Finite second shift b_f | Combined eigenvalues below b_f+E_Q |
|---|---:|---:|---:|
| 2 | 0.00125 | 0.057 | exactly one |
| 3 | 4·10^-8 | 0.00000412 | exactly one |

No eigenvalue is below ell_f+E_Q, and β>b_f. Hence the whole-operator bounds are ell=ell_f−B−D and b=b_f−B−D. Both complement terms are recomputed and checked; setting them to zero is rejected. These are not eigenvalues of the retained cosine matrix.

Widening the comparison frequency band, with the same actual nine-mode trials, reduces the ground-distance bound from 0.07561 to 0.05509 at q=2 and from 0.15050 to 0.12407 at q=3. The original and refined certificates are both retained. This is a measured improvement in full-operator enclosures, not evidence of an all-support rate.

The actual cosine Rayleigh integrals are separately recomputed in Arb, with exact decimal rational coefficients and exact L2 normalization. They enclose 0.00141902476895669 and 1.02560145378248·10^-7. Each is strictly below its full second bound. Compact resolvent supplies eigenvalues with multiplicity; this strict separation proves simplicity. Since the trial is even, an odd ground state would force its Rayleigh quotient above the full second level. Thus the ground state is even. This uses the full form, not a finite parity assumption.

## Fourier error and normalization

For centered support of length L define

\[
 \mathcal F_z(f)=L^{-1/2}\int_{-L/2}^{L/2}f(x)e^{-izx}\,dx,
 \quad W(L,Y)=\sqrt{\frac{\sinh(LY)}{LY}},\quad W(L,0)=1.
\]

Cauchy–Schwarz gives |F_z(f−u)|≤W(L,Y)||f−u|| for every |Im z|≤Y. For the raw integral multiply by sqrt(L). This fixes the normalization distinction between the existing `strip_functional_norm` function and an unnormalized Fourier integral.

If c0=F_0(g)>0 and d<c0, then F_0(u)≥c0−d>0. Therefore the origin-normalized profiles satisfy

\[
 \left|\frac{\mathcal F_z(u)}{\mathcal F_0(u)}
       -\frac{\mathcal F_z(g)}{\mathcal F_0(g)}\right|
 \le W(L,Y)\frac{d}{c_0-d}\left(1+\frac1{c_0}\right).
\]

This follows by subtracting the quotients, bounding each functional difference by Wd (and the mean difference by d), and using |F_z(g)|≤W. It does not evaluate the endpoint of either function. A protected Fourier value at zero must not be called a protected endpoint trace.

## Relation to the real-zero theorem

The new [form-core transfer note](FORM_CORE_REAL_ZERO_TRANSFER_2026_10_11.md) proves the fixed-support limit step from form-core density and a suitable finite real-zero theorem. It also derives the required structured Fourier matrix identity at arbitrary finite rank directly from the geometric correlation formula. This clarifies why an operator-core theorem is stronger than needed for that particular step. The geometric form identity and its closed realization remain written analytic dependencies. Legendre lower-comparison matrices are used for spectral bounds, not for the finite real-zero theorem.

The new bounds do not provide the support-uniform energy/gap ratio or the arithmetic Xi identification needed to turn this into an RH argument.

## Reproduction

Use Python 3.12 with `python-flint==0.8.0` and `mpmath`, for example through `uv run --with python-flint==0.8.0 --with mpmath --python 3.12`.

1. Replay `window_positivity_exp_1p2.json` with `verify_window_positivity.py`, writing `verification_2026_10_11_fourier_ground_state/baseline_replay.json`.
2. Generate the two fresh comparisons using `compact_window_certificate.py`, with the half-width, count, order and finite shifts recorded in their JSON. The original generation uses finite lower 10^-6 at q=2 and 10^-12 at q=3; the stronger shifts above are checked by the new script.
3. Replay each fresh comparison with `verify_window_positivity.py`. Each verifier recomputes four entries by adaptive complex-ball integration and checks the geometric constant-function normalization. This shares FLINT/Arb and analytic input with the generator; it is not an independent implementation of the whole proof.
4. Run `experiments/prime_spectral/full_ground_fourier.py --band 64` and `--band 128`. They validate the baseline and comparison replay records, check both parity blocks and all complement constants, and recompute the actual cosine Rayleigh integrals. The latter also writes the final `full_ground_fourier.json`.
5. Run `python -m unittest discover -s experiments/prime_spectral -p 'test_full_ground_fourier.py' -v` in the same environment.

Artifacts are in [the verification directory](verification_2026_10_11_fourier_ground_state/). `manifest.json` records completed checks and hashes. Existing manuscript files and the independently running Green integration were not edited for this work.

## Next research gate

The local baseline is now concrete. The next useful experiment should improve the form-energy excess relative to the **whole** complementary gap, then track this ratio and the protected mean across increasing support. A larger retained cosine space alone is insufficient: the complement and its arithmetic errors must improve with it. The target is a support-dependent bound whose product with W(L,Y), and any origin-normalization amplification, tends to zero for each Y<1/2. No such global rate is established here.

### A quantitative acceptance test for support growth

For an explicitly specified unit arithmetic candidate k_L, compute its genuine full-form energy μ_L, a full ground lower bound ell_L, a full second lower bound b_L, and its positive normalized mean c_L=L^-1/2∫k_L. Put

\[
 r_L=\frac{\mu_L-\ell_L}{b_L-\ell_L},\qquad
 d_L=\sqrt{2(1-\sqrt{1-r_L})}.
\]

Require 0≤r_L<1 and d_L<c_L. The observable acceptance quantity is

\[
 H_L(Y)=W(L,Y)\frac{d_L}{c_L-d_L}
                    \left(1+\frac1{c_L}\right).
\]

A sufficient research target is H_L(Y)→0 for every fixed Y<1/2, together with a separately established locally uniform Xi limit for the origin-normalized transform of this same candidate. Approximating each ground state by an arbitrary fitted Ritz vector does not establish that arithmetic identification.

There is a simpler, stronger sufficient condition. Since 0<c_L≤1 and d_L≤sqrt(2r_L),

\[
 \frac{W(L,Y)^2r_L}{c_L^4}\longrightarrow0
\]

implies d_L/c_L→0 and H_L(Y)→0. Once d_L≤c_L/2, the explicit estimate is H_L(Y)≤4sqrt(2)W(L,Y)sqrt(r_L)/c_L². For fixed Y>0, W²=sinh(LY)/(LY), so this sufficient condition asks for r_L=o(L c_L^4 exp(−LY)). This exponential requirement is a limitation of the L2-to-strip estimate; it is not asserted necessary for RH or for a more direct Fourier comparison. A useful next study should determine whether the candidate energy/gap ratio can meet it, or whether arithmetic cancellation permits a sharper observable estimate.

### Why frequency refinement is a mathematically sound local direction

There is a qualitative explanation for refining both the frequency cutoff and the retained rank. Fix support and the arithmetic symbol Ψ. Choose an increasing envelope β(T)→∞ with Ψ(t)≥β(T) for |t|≥T. The current logarithmic envelope has this property. Let R_T be the bounded lower comparison whose frequency multiplier is Ψ on |t|≤T and β(T) outside, retaining the exact pole operator. Then R_T increases in form order to A: on a newly added band Ψ≥the old envelope, and beyond that band the envelope increases.

Strong resolvent convergence alone would not supply eigenvalue convergence. Here the fixed support gives an extra compactness argument. Choose M with Ψ+M≥0, and let P be the bounded pole operator. A unit state with R_T energy ≤E satisfies, for T≥R sufficiently large,

\[
 \frac1{2\pi}\int_{|t|\ge R}|\widehat f(t)|^2dt
 \le\frac{E+M+\|P\|}{\beta(R)+M}.
\]

Indeed the shifted multiplier is nonnegative everywhere and at least β(R)+M in that tail. This tends to zero uniformly over such states. Fixed spatial support plus uniform Fourier tightness makes these states precompact in L2. For any fixed S, R_S is bounded, so its quadratic form is continuous under strong convergence; taking the supremum over S identifies the limit with the full form. Applying this argument to orthonormal frames for the first k eigenvalues and using min-max proves λ_k(R_T)↑λ_k(A). Low eigenvalues of R_T exist below its essential level β(T) for all sufficiently large T, by finite-dimensional trial upper bounds for A.

At each fixed T, R_T−β(T)I is compact: its bounded-band kernel and pole terms are compact on a finite interval. Polynomial compression therefore converges in operator norm for this compact part. The analytic B,D bounds tend to zero with sufficiently large retained rank, while quadrature and arithmetic errors can be reduced separately. Combined with the existing upper Ritz approximation, this explains how arbitrarily accurate fixed-support enclosures are possible in principle under the stated analytic identities. It supplies neither a complexity bound nor automatic termination of the present hard-coded certificate search.

The research frontier is the **uniform dependence on support** in these statements. Pole norms, prime weights, the required frequency cutoff, the ground gap and the normalization can all deteriorate. The two computed improvements do not establish a rate that survives that deterioration.
