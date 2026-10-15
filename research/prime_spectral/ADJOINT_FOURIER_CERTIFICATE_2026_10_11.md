# Actual full-operator adjoint corrections for Fourier profiles

Date: 11 October 2026. Status: written operator/domain analysis and Arb arithmetic, not a Lean operator proof or novelty claim. This implements the proposed dual test from the [orthogonality-aware transfer](ORTHOGONAL_FOURIER_TRANSFER_2026_10_11.md). All work is in `codex/xi-eigenvector-reduction`.

## Result and scope

Let u_C be the genuine real even unit Weil ground state at support length L=log C, and g_C the same exact nine-mode cosine trial used in the [previous full-ground certificate](FULL_GROUND_FOURIER_2026_10_11.md). The new certificates bound the difference between their Fourier transforms after normalizing at the origin.

| Region or point | C=2 | C=3 |
|---|---:|---:|
| Previous bound on the entire strip abs(Im z)≤0.4 | <0.05310 | <0.17867 |
| **New bound on abs(Re z)≤1, abs(Im z)≤0.4** | **<0.00551** | **<0.08754** |
| New point bound at z=0.4i | <0.000663 | <0.01205 |
| New point bound at z=1+0.4i | <0.00475 | <0.08603 |

The first row also bounds the compact rectangle, so the comparison there is valid. The new adjoint argument does not yet cover every real frequency. The certificates use eight endpoint-zero correction modes, residual coefficients through mode 64, and an analytic bound on **every** remaining cosine mode. All odd residual coefficients vanish by reflection symmetry.

These are comparisons with a local cosine reference. That reference has no established increasing-support Xi limit and is not the canonical prolate candidate of Connes–Consani–Moscovici. No arithmetic Xi identification or RH proof follows.

The trust boundary remains the written closed Weil realization, self-adjointness, Fourier matrix identity and spectral bounds, followed by Arb-enclosed finite arithmetic. The associated operator and discrete-spectrum framework is described in [Connes–Consani–Moscovici, §3](https://arxiv.org/html/2511.22755v1). The domain and residual arguments below are written mathematical steps, not additional Lean theorems.

## The adjoint inequality actually used

Write F_z(f)=L^-1/2∫f(x)exp(−iz(x−L/2))dx and p(z)=F_z(g)/F_0(g). In the even subspace use the kernel cos(z(x−L/2)). Let k_z represent F_z−p(z)F_0, with the compatible Riesz conjugation convention. If

\[
 Au=\lambda_0u,\quad \|u\|=1,\quad F_0(u)\ge M>0,
 \quad |\lambda_0-\nu|\le\delta,
\]

then any h in D(A) satisfying ||(A−ν)h−k_z||≤ε and ||h||≤H gives

\[
 \left|\frac{F_z(u)}{F_0(u)}-p(z)\right|
 \le\frac{\varepsilon+\delta H}{M}.
\]

This follows by moving A to u in the inner product and applying Cauchy–Schwarz. For the coefficient implementation u and the operator matrix are real; complex-linear extension gives the same identity without changing any norm.

The full ground lower bound ell and exact-trial Rayleigh upper bound μ give λ0∈[ell,μ]. Set ν=(ell+μ)/2 and δ=(μ−ell)/2. The earlier orthogonal angle calculation supplies M>0. Thus the numerator has no spectral-gap denominator, although the current certificate for M still uses a full second-level bound. This distinction matters when considering larger supports.

## Corrections belong to the operator domain

In the normalized even basis e_0=L^-1/2 and e_n=sqrt(2/L)cos(2πnx/L), choose exact decimal complex coefficients d_1,…,d_N and set

\[
 h=\sum_{n=0}^N h_ne_n,\qquad h_n=d_n\ (n\ge1),
 \qquad h_0=-\sqrt2\sum_{n=1}^Nd_n.
\]

Then h(0)=h(L)=0 exactly. This condition is imposed on the correction only, not on the ground state or reference trial.

Its zero extension is in H1(R): the smooth interior derivative is square-integrable and there is no boundary delta in the weak derivative. The Fourier multiplier of the archimedean Weil part grows at most logarithmically; fixed-support prime terms and pole terms are bounded. Therefore its full multiplier applied to h is in L2, since (1+log(1+|t|))² is bounded by a constant times 1+t². Pairing this L2 representative with all form-domain vectors identifies h as an element of the domain of the associated operator. This proves the required domain statement directly for these corrections; it does not infer an operator core from a form core.

## Actual Fourier matrix and a bound for its entire tail

The [exact divided-difference identity](FORM_CORE_REAL_ZERO_TRANSFER_2026_10_11.md) gives a real sequence b_n with b_−n=−b_n and, for positive m≠n,

\[
 A^{\rm even}_{mn}=\frac{2(mb_m-nb_n)}{m^2-n^2},\qquad
 A^{\rm even}_{m0}=\frac{\sqrt2 b_m}{m}.
\]

The finite diagonal entries are separately integrated. The sequence itself is recomputed as b_n=n*A_{n0} in the complex Fourier basis, using adaptive ball integration. Independent tests compare the divided-difference matrix with direct geometric entry integrals and compare b_n with a separate sine-integral expression.

A uniform bound is needed for all b_m, not only the computed prefix. With K(r)=2cosh(r/2)−exp(r/2)/(2sinh r), write K=−1/(2r)+R. For 0<r≤L,

\[
 |R(r)|\le R_*:=2\cosh(L/2)+e^{L/2}/4+L\cosh L/12.
\]

This follows from sinh r≥r, exp(r/2)−1≤r exp(L/2)/2 and sinh r−r≤r³ cosh L/6. The singular sine integral obeys |Si(t)|≤3 for t≥0: use |sin t|≤t below 1 and integrate sin t/t by parts above 1. Consequently

\[
 |b_m|\le B_*:=\frac{3/2+LR_*+
              \sum_{q=p^k<C}\log(p)/\sqrt q}{\pi}.
\]

The endpoint prime q=C has zero correlation and can be omitted. All active prime powers are included in this bound.

For m>N the endpoint-zero identity cancels the leading b_m/m term exactly:

\[
 (Ah)_m=b_m\sum_{n=1}^N\frac{2n^2h_n}{m(m^2-n^2)}
             -\sum_{n=1}^N\frac{2nb_nh_n}{m^2-n^2}.
\]

For a prefix cutoff P>N put ρ=1−(N/(P+1))². Define

\[
 C_3=\frac{2B_*}{\rho}\sum n^2|h_n|,
 \qquad C_2=\frac2\rho\sum n|b_nh_n|.
\]

Then |(Ah)_m|≤C_3/m³+C_2/m² for all m>P. Put a=Lz/2. The target coefficients at positive modes are

\[
 (k_z)_m=\frac{\sqrt2 a\sin a}{a^2-\pi^2m^2}.
\]

They obey |(k_z)_m|≤K_2/m², where K_2=sqrt(2)|a sin a|/[π²(1−|a|²/(π²(P+1)²))], whenever the denominator is positive. Integral bounds for the inverse-power series give the complete tail estimate

\[
 \|((A-\nu)h-k_z)_{m>P}\|_2
 \le\frac{C_3}{\sqrt{5P^5}}
        +\frac{C_2+K_2}{\sqrt{3P^3}}=:T.
\]

If S is the squared norm of the independently enclosed residual coefficients through P, then ε≤sqrt(S+T²). No discarded residual modes are set to zero. Parseval applies to the complete even cosine basis; the odd part is zero.

## Selection and complete complex-cell coverage

Floating least squares selects a correction from the endpoint-zero basis and penalizes δ²||h||². This is only a selector, not a proof or an optimization claim. Its coefficients are rounded to exact decimal rationals, after which Arb computes the actual rectangular matrix residual, full tail, norm and δH term.

For the compact rectangle use 16 real cells and 8 imaginary cells in its positive quadrant. The same fixed correction is used throughout each cell. Arb evaluates the full target and tail on that complex rectangle. Real evenness and conjugation cover the other three quadrants. Thus each cutoff uses 128 complete cells, not 128 sampled points.

Stable analytic cancellation is essential. For m≥1 use the rational Fourier-coordinate formula above whenever its denominator excludes zero; use the entire sinc formula at removable resonances. Compute the constant target coefficient directly as

\[
 (k_z)_0=-\sum_{n\ge1}\frac{g_n}{g_0}F_z(e_n),
\]

instead of subtracting two interval evaluations sharing the same constant Fourier term. This preserves cancellation across a cell. Interval norms are bounded using nonnegative modulus endpoints before square roots, including cells crossing zero.

## Validation and reproduction

Eleven tests pass. They cover direct matrix-entry comparisons, independent sine and physical Fourier integrals, endpoint-zero corrections and independently integrated norms, all admissible tail-sequence values, removable resonances, exact zero frequency, corrupted numerical payloads, invalid inputs, and replay of every saved rectangle correction. Matrix payload and source hashes are checked. All original spectral inputs remain unchanged.

```sh
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python experiments/prime_spectral/adjoint_fourier_certificate.py --cover-cells 16 8
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_adjoint_fourier_certificate.py -v
```

The [verification directory](verification_2026_10_11_adjoint_fourier/) retains the exact corrections, full matrix inputs, every cell's residual and tail, and outward rational bounds.

## Next research gate

The adjoint method is now an actual local operator experiment. Its next meaningful test is the **canonical arithmetic/prolate Fourier profile** rather than the present cosine reference. The dual criterion only needs that profile p(z), not a candidate Rayleigh quotient below the second eigenvalue. It therefore tests a different obligation from the [earlier failed prolate residual/gap gate](PROLATE_RESIDUAL_GAP_AUDIT_2026_09_26.md).

That advantage is conditional on obtaining a certified candidate profile, a protected actual ground mean, and correction residuals whose ε+δH stays useful as support and complex regions grow. Large correction norms, eigenvalue uncertainty and omitted-mode tails remain explicit possible obstructions. Neither a growing-support rate nor the comparison with an Xi-producing candidate has been established here.
