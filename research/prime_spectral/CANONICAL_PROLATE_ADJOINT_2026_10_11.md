# Full Weil adjoints against the canonical prolate profile

Date: 11 October 2026. Status: written operator/prolate analysis and Arb certificates in `codex/xi-eigenvector-reduction`. No novelty claim, growing-support theorem or RH proof.

## Result

Let u_C be the real even unit ground state of the actual semilocal Weil operator, whose simplicity, parity, full spectral bounds and protected mean at C=2 and C=3 are supplied by the [full-ground certificate](FULL_GROUND_FOURIER_2026_10_11.md). Let p_C be the origin-normalized Fourier transform of the **unprojected** arithmetic/prolate candidate defined below. The new certificate gives

\[
 \sup_{|\Re z|\le1,\ |\Im z|\le2/5}
 \left|\frac{\widehat u_C(z)}{\widehat u_C(0)}-p_C(z)\right|
 < B_C.
\]

| Correction modes / residual prefix | C=2 | C=3 |
|---|---:|---:|
| 8 / 64 | 0.00563 | 0.08697 |
| **16 / 128** | **0.00381** | **0.07196** |

Both rows retain every remaining residual mode analytically. Each row uses 256 complete complex cells per cutoff, covering both signs of the imaginary coordinate. These are bounds on the stated rectangle, not the entire strip or a frequency grid. The prolate eigenvector error is transferred through the complete arithmetic map before normalization; no finite Fourier projection replaces the candidate.

The preceding [local-cosine adjoint certificate](ADJOINT_FOURIER_CERTIFICATE_2026_10_11.md) did not identify an Xi-producing reference. This continuation makes that comparison at two fixed cutoffs. The canonical family is the zero-integral two-prolate-mode candidate in [Connes–Consani–Moscovici, §7, equations (7.5)–(7.9)](https://arxiv.org/html/2511.22755v1). Their Lemma 7.3 gives its suitably normalized transform an increasing-support Xi limit; their §8 leaves the comparison with Weil ground states open. Our finite certificates do not close that asymptotic step.

## The exact candidate, including its odd part

Put C=lambda² and L=log C. On [-1,1], let psi_0 and psi_4 be unit real even prolate eigenfunctions for

\[
 -\partial_s((1-s^2)\partial_s)+(2\pi C)^2s^2.
\]

Orient their constant normalized-Legendre coefficients a_0,a_4 positively, and set H=psi_4-(a_4/a_0)psi_0, extended by zero. Since only the constant Legendre coefficient contributes to the integral, integral H=0. On -L/2≤t≤L/2 define

\[
 K_C(t)=e^{t/2}\sum_{1\le n<C} H(ne^t/\sqrt C),\qquad
 p_C(z)=\frac{\int K_C(t)e^{-izt}\,dt}{\int K_C(t)\,dt}.
\]

The term n=C only contributes at an endpoint and has zero integral. Rescaling s=x/lambda supplies the physical prolate modes; their common scalar normalization cancels in p_C. The angular parameter is 2*pi*C, rather than 2*pi*sqrt(C).

Zero integral does not imply that a compactly supported prolate combination is exactly Fourier invariant. Accordingly K_C need not be even. The [previous two-constraint audit](PROLATE_TWO_CONSTRAINT_DEFECT_2026_09_23.md) explains the compressed-Fourier defect. We retain it here. At the real frequency z=1 the certificate proves

\[
 -\Im p_2(1)>0.00054020,\qquad
 \Im p_3(1)>0.000000475782.
\]

Because the true real even ground state's transform is real there, these are also strict lower bounds on its normalized profile difference from the canonical candidate at that frequency. Exact equality at finite support is false. This does not obstruct asymptotic convergence. For the real candidate, p_C(-conj z)=conj p_C(z). This symmetry reflects the real coordinate only; it does not justify omitting negative imaginary frequencies. The cell cover uses 16 nonnegative real intervals and 16 imaginary intervals across [-0.4,0.4], then reflects the real coordinate.

## Infinite prolate eigenfunction errors and normalization

The first four even Jacobi eigenvalues are isolated by Arb Sturm bisection and an infinite-tail Schur estimate, using 40 even Legendre terms and tail cut 500. Decimal trial modes are selected by mpmath and certified by their full infinite-Jacobi residual, including the omitted-coordinate coupling. Their oriented unit L2 errors obey

| Cutoff | Mode 0 | Mode 4 |
|---|---:|---:|
| 2 | <1.12e-58 | <1.07e-55 |
| 3 | <4.99e-47 | <8.32e-44 |

These are certified upper bounds, not floating eigensolver accuracy claims. Every stored eigenvector and spectral-bound field is replayed before use; input and generator hashes are checked.

Write v_0,v_4 for normalized decimal trials, eta_0,eta_4 for their errors, and z_0 for a lower bound on the constant coefficient of v_0. If z_0>eta_0 and f_0 bounds the absolute constant coefficient of v_4, then

\[
 r_*=(f_0+\eta_4)/(z_0-\eta_0),\quad
 e_r=\eta_4/(z_0-\eta_0)+f_0\eta_0/[z_0(z_0-\eta_0)],
\]

\[
 \|H-H_{\rm trial}\|_2
 \le\eta_4+r_*\eta_0+e_r=:e_H.
\]

For the full arithmetic map, changing variables s=n*exp(t)/sqrt(C) in each summand gives

\[
 \|K_H-K_{\rm trial}\|_2
 \le C^{1/4}\left(\sum_{n=1}^{C-1}n^{-1/2}\right)e_H=:e_K.
\]

For |Im z|≤Y its unnormalized Fourier error is at most sqrt(L)*exp(YL/2)*e_K. The origin is enclosed using the real error sqrt(L)*e_K and is protected above 0.49530 at C=2 and 0.58404 at C=3. Thus both exact normalized profiles are well defined. The eigenfunction input error is much smaller than the final Weil comparison error.

## Complete Fourier integrals and interval cancellation

Expand the normalized decimal input as H_trial(s)=sum q_k*s^(2k), with exact rational Legendre polynomial algebra. Substituting x=t+L/2 gives the closed antiderivative

\[
 \widehat K_{\rm trial}(z)=
 C^{-1/4}e^{izL/2}\sum_{n=1}^{C-1}\sum_kq_k
 \frac{\sqrt{C/n}\,e^{-iz\log(C/n)}-(n/C)^{2k}}
      {2k+1/2-iz}.
\]

This formula has no denominator zero on the open half strip. It integrates each summand on its entire support, so all arithmetic threshold jumps are retained.

On complex cells a direct subtraction of interval evaluations loses useful cancellation. Instead compute real moments M_j=integral t^j*K_trial(t) dt for j=0,...,19. For beta=2k+1/2, D=log(C/n), l=-L/2 and r=D+l, the weighted moments obey

\[
 I_0=(e^{\beta D}-1)/\beta,\qquad
 I_j=[e^{\beta D}r^j-l^j-jI_{j-1}]/\beta.
\]

After multiplying each monomial's prefactor and summing, these give M_j. The full Taylor remainder at order J=20 is bounded by

\[
 \sqrt L\,\|K_{\rm trial}\|_2\,
 e^R R^J/J!,\qquad R=|z|L/2.
\]

The trial norm is bounded through the same full arithmetic map, using the actual Legendre combination norm. For the constant target coordinate compute the difference moments directly:

\[
 (k_z)_0=\operatorname{sinc}(Lz/2)-p_C(z).
\]

The normalized constant kernel has moments U_j=0 for odd j and U_j=(L/2)^j/(j+1) for even j. Evaluate the degree-19 polynomial with coefficients (U_j-M_j/M_0)/j! in powers (-iz)^j, setting the shared constant to zero exactly. Retain both Taylor remainders. The exact-candidate correction to the trial quotient is bounded by

\[
 \frac{e_z+|p_{\rm trial}(z)|e_0}{M_0-e_0},
 \quad e_0=\sqrt L e_K,\quad e_z=e_0 e^{|\Im z|L/2}.
\]

This includes the full odd profile. Stable moment subtraction reduces interval dependency; it does not discard an error term.

## Actual Weil adjoints and remaining frontier

Use the [actual endpoint-zero correction domain, matrix identity and infinite residual tail](ADJOINT_FOURIER_CERTIFICATE_2026_10_11.md). Only the constant target coefficient changes when replacing the cosine reference by p_C; every positive-mode target remains F_z(e_n), because F_0(e_n)=0. If a correction h satisfies full residual epsilon, norm H, eigenvalue uncertainty delta and protected ground mean M, then

\[
 |\widehat u_C(z)/\widehat u_C(0)-p_C(z)|
 \le(\epsilon+\delta H)/M.
\]

The matrix and residual prefix are evaluated in Arb; all omitted modes retain the analytic inverse-power bound. Floating least squares only chooses exact decimal correction coefficients. The complete residual, domain restriction, correction norm, eigenvalue uncertainty term and protected ground mean remain in every cell certificate. The eight-mode and sixteen-mode certificates are separate verified choices, not claims of optimal correction.

For the eight-mode C=3 point z=1+0.4i, the full residual upper bound is approximately 0.05833, the tail contribution approximately 0.03493, and delta*H approximately 0.000002624. These scales explain why tighter prolate eigenvectors or only a sharper eigenvalue interval cannot substantially improve this bound. Increasing the correction dimension does improve it, but no rate in growing C has been established.

The next research obligation is to construct h_(C,z) across growing supports and prove

\[
 \sup_{z\in K}(\epsilon_{C,z}+\delta_C\|h_{C,z}\|)/M_C\longrightarrow0
\]

for compact K in the half strip, while proving the full simple-even ground-state gate on that path. Combine that estimate with the canonical Xi limit and the real-zero ground-state transfer only after both are justified. Repeating fixed-cutoff computations does not supply this support-dependent estimate. A weighted adjoint construction that exploits arithmetic/prolate cancellation in the residual is the substantive target; the present inverse-power tail bounds are a reproducible starting point.

## Validation and replay

Eleven tests pass: six independent complex Fourier integrals using Legendre recurrence and support splitting, six independent physical moment integrals, large-frequency Taylor remainder checks, exact origin/protected normalization, nonzero odd profiles and the correct symmetry, interval-cell containment, full replay of 1,024 complex cells and sixteen point corrections, source/dependency hashes, six additional direct geometric matrix integrals, corrupted-vector rejection and invalid-input checks. The earlier actual-adjoint tests separately validate the full tail majorant and correction-domain algebra.

```sh
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python experiments/prime_spectral/canonical_prolate_adjoint.py --cover-cells 16 8
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python experiments/prime_spectral/canonical_prolate_adjoint.py --modes 16 --prefix 128 --cover-cells 16 8
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_canonical_prolate_adjoint.py -v
```

All new records, input certificates and hashes are in [verification_2026_10_11_prolate_adjoint](verification_2026_10_11_prolate_adjoint/manifest.json). Jacobi inputs use `certified_prolate_jacobi.py --cutoff C --terms 40 --tail-cut 500`, followed by `certified_prolate_vectors.py`; their generators and parameters are recorded. Matrix integration uses 384 bits and the profile/correction arithmetic uses 1,024 bits. The trust boundary includes the written infinite-dimensional prolate and Weil realizations, full spectral/domain identities and tail arguments. No new Lean operator formalization is claimed.
