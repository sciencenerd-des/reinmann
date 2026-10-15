# Free-boundary and ground-angle adjoint certificates

Date: 12 October 2026. Worktree: `codex/xi-eigenvector-reduction`. Status: written Weil operator-domain and full-tail arguments, Arb arithmetic, and separately checked abstract Hilbert-space lemmas. No increasing-support theorem, novelty claim or RH proof.

## Result

For the actual simple even Weil ground states at C=2 and C=3, the origin-normalized Fourier comparison with the **unprojected canonical arithmetic/prolate candidate** now satisfies the following complete rectangle bounds:

| Positive cosine index / residual prefix | C=2 | C=3 |
|---|---:|---:|
| Previous endpoint-zero correction, 16 / 128 | <0.00381 | <0.07196 |
| New free-boundary, coherent-tail, ground-angle correction, 16 / 128 | **<0.000948** | <0.007722 |
| New free-boundary, coherent-tail, ground-angle correction, 32 / 256 | <0.000952 | **<0.006274** |

The region is abs(Re z)≤1, abs(Im z)≤0.4. Each new correction size uses 256 complete complex cells per cutoff, with both signs of Im z covered explicitly. The extra constant coefficient is free, so N positive indices give N+1 correction parameters. Every boundary contribution, omitted residual mode, exact-prolate eigenfunction error and eigenvalue uncertainty is retained.

The previous row comes from the [canonical prolate certificate](CANONICAL_PROLATE_ADJOINT_2026_10_11.md). The earlier actual-adjoint argument supplies the [full matrix identity and basic duality](ADJOINT_FOURIER_CERTIFICATE_2026_10_11.md); its endpoint-zero restriction was sufficient for the domain argument, rather than a necessary operator boundary condition. The finite-support candidate still has a nonzero odd part. These bounds do not identify it exactly with a ground state.

At z=1+0.4i the 32 / 256 bounds are <0.000808 for C=2 and <0.005883 for C=3. The C=2 whole-rectangle bound is slightly tighter with 16 indices. No monotonicity or optimality in correction dimension is claimed.

## 1. Finite cosine corrections need not vanish at the endpoints

Let f be smooth on [0,L], with arbitrary finite endpoint values, extended by zero to the real line. Its distributional derivative is a finite measure: it consists of the interior derivative and the two boundary jumps. Integration by parts gives

\[
 |\widehat f(t)|\le\operatorname{Var}(f)/|t|\quad(t\ne0),
 \qquad |\widehat f(t)|\le\|f\|_1.
\]

The archimedean Weil multiplier has at most logarithmic growth. Consequently its product with the Fourier transform of this extension lies in L2, since

\[
 \int_1^\infty\log^2(1+t)t^{-2}\,dt<\infty.
\]

Compressing that L2 multiplier image to [0,L], and adding the bounded prime and pole operators, gives an L2 representative for q(f,v) against every vector v in the closed form domain. The representation theorem therefore puts f in the domain of the associated Weil operator. In particular **every finite cosine correction used here is admissible**, including those with nonzero endpoints. This is a direct domain argument; it does not infer an operator core from a form core.

The underlying closed-form realization, bounded prime/pole terms and logarithmic multiplier are described in [Connes–Consani–Moscovici, §3, especially Theorem 3.6](https://arxiv.org/html/2511.22755v1). Their bounded-variation observation also explains the Fourier decay of piecewise smooth tests; the L2 multiplier argument above supplies the additional operator-domain step used here.

This argument concerns known finite corrections only. It does not make endpoint evaluation continuous on a logarithmic graph norm, estimate a ground-state trace, or invalidate the earlier endpoint-trace obstruction.

## 2. A sharper all-mode bound on the matrix sequence

Use the actual even matrix sequence b_m from the preceding certificate. Put L=log C, omega=2*pi*m/L and

\[
 R(r)=2\cosh(r/2)-\frac{e^{r/2}}{2\sinh r}+\frac1{2r},\qquad R(0)=7/4.
\]

The geometric form gives the exact identity

\[
 b_m=\frac{\operatorname{Si}(2\pi m)}{2\pi}
 -\frac1\pi\int_0^L R(r)\sin(\omega r)\,dr
 +\sum_{q=p^k<C}\frac{\log p}{\pi\sqrt q}\sin(\omega\log q).
\]

To bound R' without subtracting singular terms, define

\[
 E(r)=\tfrac12\int_0^1e^{tr/2}\,dt,
 \quad S(r)=\tfrac12\int_0^1(1-t)^2\cosh(tr)\,dt,
 \quad T(r)=\int_0^1\cosh(tr)\,dt.
\]

Then R=2*cosh(r/2)-(E-r*S)/(2*T). For 0≤r≤L,

\[
 T\ge1,\quad |T'|\le\sinh L/2,\quad
 E\le e^{L/2}/2,\quad E'\le e^{L/2}/8,
 \quad S\le\cosh L/6,\quad |S'|\le\sinh L/24.
\]

The product/quotient rule therefore gives

\[
 |R'|\le D_R:=\sinh(L/2)
 +\tfrac12(e^{L/2}/8+\cosh L/6+L\sinh L/24)
 +(e^{L/2}/2+L\cosh L/6)\sinh L/4.
\]

Integration by parts uses cos(omega*L)=1 and bounds the regular sine integral by 2*L*D_R/omega. Also abs(Si(x)-pi/2)≤2/x. It follows, for every positive integer m, that

\[
 \left|b_m-\frac14-
   \sum_{q=p^k<C}\frac{\log p}{\pi\sqrt q}\sin(\omega\log q)\right|
 \le\frac{D_C}{m},\qquad
 D_C=(1/2+L^2D_R)/\pi^2.
\]

For all m>P this supplies

\[
 |b_m|\le B_C(P):=\frac14+
       \sum_{q=p^k<C}\frac{\log p}{\pi\sqrt q}+\frac{D_C}{P+1}.
\]

This written estimate and its implementation allow any integer C≥2. The **ground-state and adjoint certificates remain restricted to C=2 and C=3**. Independent sine-integral tests check the estimate at C=2,3,5. Those checks supplement the analytic argument, rather than proving the all-mode statement by sampling.

## 3. Full residual tails retain signed moments and the boundary term

Take h=sum_(n=0)^N h_n e_n with arbitrary exact decimal complex coefficients. Write

\[
 E_h=h_0+\sqrt2\sum_{n=1}^Nh_n,
 \quad T_j=\sum_{n=1}^N n^jb_nh_n,
 \quad S_j=\sum_{n=1}^N n^jh_n.
\]

The common endpoint value is E_h/sqrt(L). For m>N, the actual matrix identity becomes

\[
 (Ah)_m=\frac{\sqrt2E_h b_m}{m}
 +b_m\sum_{n=1}^N\frac{2n^2h_n}{m(m^2-n^2)}
 -\sum_{n=1}^N\frac{2nb_nh_n}{m^2-n^2}.
\]

Put a=L*z/2, u=(a/pi)^2 and K=sqrt(2)*a*sin(a)/pi². The positive-mode target is -K/[m²(1-u/m²)]. After J geometric terms the residual is

\[
 ((A-\nu)h-k_z)_m
 =\frac{\sqrt2E_h b_m}{m}
 +\sum_{j=0}^{J-1}\frac{-2T_{2j+1}+Ku^j}{m^{2j+2}}
 +b_m\sum_{j=0}^{J-1}\frac{2S_{2j+2}}{m^{2j+3}}
 +\mathcal R_m.
\]

The signed combinations -2*T_(2j+1)+K*u^j and S_(2j+2) are enclosed **before** taking absolute values. This preserves cancellation between correction modes and the Fourier target. Set rho=1-(N/(P+1))², eta=1-abs(u)/(P+1)², both positive, and B=B_C(P). The complete remainder obeys

\[
 |\mathcal R_m|\le
 \left[\frac2\rho\sum n^{2J+1}|b_nh_n|
       +\frac{|K||u|^J}{\eta}\right]m^{-(2J+2)}
 +\frac{2B}{\rho}\sum n^{2J+2}|h_n|m^{-(2J+3)}.
\]

For p>1/2 define W_p(P)=1/sqrt((2p-1)*P^(2p-1)). Minkowski's inequality and the integral comparison for the full infinite series give a residual-tail bound

\[
 \sqrt2|E_h|B W_1(P)
 +\sum_{j=0}^{J-1}|-2T_{2j+1}+Ku^j|W_{2j+2}(P)
 +2B\sum_{j=0}^{J-1}|S_{2j+2}|W_{2j+3}(P)
\]

plus the two displayed remainder coefficients times their corresponding W powers. The implementation uses J=2. Its boundary term decays only as P^(-1/2) and is always included. An endpoint-zero identity is no longer imposed or silently assumed.

Least squares includes these boundary and moment expressions as selection penalties. This selection is untrusted and is not an optimization certificate. Arb independently checks the resulting exact decimal h, the complete prefix, full tail, norm and spectral uncertainty.

## 4. Ground-angle duality reduces the relevant residual component

Let u and g be unit vectors, with u the actual ground state and g the certified nine-mode trial. Write u=c*g+w, w orthogonal to g, and assume ||w||²≤r<1, supplied here by the previously certified **full** form-energy/gap bound. For any vector v,

\[
 |\langle u,v\rangle|
 \le |\langle g,v\rangle|
       +\sqrt r\,\|v-\langle g,v\rangle g\|.
\]

This follows from abs(c)≤1, orthogonality and Cauchy–Schwarz. If V bounds ||v|| and q_-≤abs(<g,v>)≤q_+, then

\[
 B_u(v):=\min\{V,\ q_++\sqrt r\sqrt{V^2-q_-^2}\}
\]

bounds abs(<u,v>). The first branch is ordinary Cauchy–Schwarz. Only a mathematically nonnegative squared norm is clamped against outward interval rounding.

For the **full** adjoint residual R_z=(A-nu)h-k_z, self-adjointness at the selected domain vectors gives

\[
 \langle u,k_z\rangle=(\lambda_0-\nu)\langle u,h\rangle
                         -\langle u,R_z\rangle.
\]

With abs(lambda_0-nu)≤delta and F_0(u)≥M>0, the improved profile error is

\[
 \left|\widehat u(z)/\widehat u(0)-p_C(z)\right|
 \le [B_u(R_z)+\delta B_u(h)]/M.
\]

The norm of R_z still includes the entire omitted tail. Because g has nine modes, its pairing with R_z is computed exactly from retained coordinates; no omitted component of that pairing is discarded. The correction dimension and residual prefix contain every trial coordinate.

At C=3, z=1+0.4i, the 32 / 256 ordinary Cauchy bound is approximately 0.04545. Keeping the certified trial pairing and angle lowers it to approximately 0.0058821. For the whole rectangle the ordinary bound is below 0.04853, compared with the refined 0.006274. Thus the ground-angle estimate supplies most of the improvement at C=3; freeing the boundary and refining the tail alone do not explain the final gain.

## 5. Shared Fourier moments must be cancelled before cell evaluation

Summing g_n times independently enclosed residual coordinates loses cancellation across a complex cell. Instead evaluate

\[
 \langle g,R_z\rangle
 =\sum_nh_n\left(\sum_i g_i A_{in}-\nu g_n\right)
   -\big(F_z(g)-g_0p_C(z)\big).
\]

The first parenthesized expression is frequency independent for a fixed cell correction. The Fourier difference is evaluated through its combined moments. If B_j are the centered normalized Fourier moments of g and M_j the full arithmetic trial moments from the canonical profile certificate, use B_j-g_0*M_j/M_0 **before** interval evaluation. The shared constant vanishes exactly. The arithmetic candidate's odd moments remain in the expression.

Cosine moments are obtained independently from I_0=0 and

\[
 I_j=[(L/2)^j-(-L/2)^j-jI_{j-1}]/(i\omega_n),
 \qquad\omega_n=2\pi n/L.
\]

Their real parts, scaled by sqrt(2)/L, give the positive-mode moments; odd cosine moments vanish. The degree-19 polynomial retains the full order-20 exponential remainder for both functions and the exact-prolate eigenfunction quotient error. This rearrangement preserves cancellation without relying on floating eigenvectors or a finite projection of the canonical candidate.

## 6. Formal and numerical validation

[Reinmann/WeilAdjointPairing.lean](../../Reinmann/WeilAdjointPairing.lean) proves six abstract complex Hilbert-space lemmas: the orthogonal decomposition bound, its unit-trial form, the orthogonal-remainder squared-norm identity, intersection with ordinary Cauchy–Schwarz, the local adjoint residual identity, and the resulting pairing bound. The targeted Lake build passes. The separate six-theorem axiom audit has not completed; no completed audit is claimed. The numerical angle, actual Weil action/domain, sequence asymptotics and tail integrals remain written or computer-assisted dependencies, rather than formal Lean instances. The module is independently built; it is not added to the root imports or presented as an all-repository fresh build.

Eleven new tests cover:

- Four independent regular-kernel integral identities and nine independent sequence sine integrals at C=2,3,5.
- Six adversarial tail checks (two cutoffs and three expansion orders), retaining both extremes of every admissible omitted b_m for 400 test modes; the analytic remainder bounds the infinite tail.
- A nonzero constant correction with its explicit nonzero boundary tail.
- The ground-pairing bound in independent finite complex geometries.
- Eight stable trial/target pairing comparisons and four actual omitted-row decompositions beyond mode 256.
- Six additional direct geometric matrix comparisons up to mode 256.
- Full replay of 1,024 complete complex cells and sixteen point corrections, current source/dependency hashes and invalid inputs.

The eleven canonical-profile tests and eleven earlier actual-adjoint tests also pass, for 33 Python tests in total. Matrix integration uses 384 bits; profile and correction verification use 1,024 bits. [Verification manifest](verification_2026_10_11_boundary_moment/manifest.json) records the source, numerical-input, log and artifact hashes. The directory name records the batch's starting date; this report and final validation are dated 12 October.

## 7. The remaining research frontier

One part of the growing-support tail can already be bounded explicitly. For every integer C≥2, L=log C, the elementary inequalities sinh(L/2)≤sqrt(C)/2, cosh L≤C and sinh L≤C/2 give

\[
 D_R\le C^2(17/24+L/32),\qquad D_C\le C^2(1+L)^3.
\]

Also log p≤L and the integral comparison for sum q^(-1/2) give

\[
 \sum_{q=p^k<C}\frac{\log p}{\pi\sqrt q}
 \le\frac{2\sqrt C\,L}{\pi}.
\]

Choose an integer residual prefix P≥C²*(1+log C)³, enlarged as needed to lie beyond the correction modes. Then D_C/(P+1)≤1 and the **entire boundary part** of the residual tail obeys

\[
 T_{\rm boundary}
 \le\frac{\sqrt2 |E_h|}{\sqrt P}
       \left(\frac54+\frac{2\sqrt C L}{\pi}\right)
 \le\frac{3|E_h|}{\sqrt C\sqrt{1+\log C}}.
\]

For the last inequality use sqrt(2)*(5/4+2/pi)<3, C≥1 and L≥0. Thus, after division by the protected mean, this boundary contribution tends to zero whenever abs(E_h)/M=o(sqrt(C)*sqrt(1+log C)). In the angle-weighted complementary-residual criterion below an additional sqrt(r_C) factor is available. This is an explicit **all-integer-support boundary-tail estimate**, not a construction of h_C, a bound on its endpoint, or control of the complete bulk residual. The quadratic prefix requirement is sufficient and is not claimed optimal. No prime number theorem or unproved prime cancellation is used.

The bounds are still fixed-support results. The all-support question is now more precise than demanding a small unweighted adjoint norm. It would suffice to prove, along a growing-support path and uniformly on each compact frequency set,

\[
 \frac{|\langle g_C,R_{C,z}\rangle|}{M_C}\to0,\qquad
 \frac{\sqrt{r_C}\,\|Q_{g_C}R_{C,z}\|}{M_C}\to0,\qquad
 \frac{\delta_C B_{u_C}(h_{C,z})}{M_C}\to0.
\]

The residual itself need not tend to zero if its ground-sensitive part does. This is a sufficient criterion derived from the proved inequality, **not an established asymptotic estimate**. The full simple-even ground-state gate, protected means and angle bounds must also be established on that path.

The explicit boundary/moment expansion identifies what the remaining full tail costs: B_C(P)*abs(E_h)/sqrt(P), signed arithmetic/Fourier moments, and higher inverse-power remainders. A useful next analytic construction should control those combinations together with the trial pairing, rather than only increasing a finite matrix dimension or tightening an already negligible prolate eigenvector error. The arithmetic oscillations in b_m must remain visible when support grows. The matrix integration helper and full spectral inputs have not yet been generalized beyond the two certified cutoffs.

Only after this estimate is established can the canonical candidate's published Xi limit be transferred to true Weil ground states and combined with the real-zero transfer. No such support-dependent estimate is claimed here.

## Reproduction

```sh
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python experiments/prime_spectral/boundary_moment_adjoint.py --cover-cells 16 8
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python experiments/prime_spectral/boundary_moment_adjoint.py --modes 32 --prefix 256 --cover-cells 16 8
uv run --with python-flint==0.8.0 --with mpmath --with numpy --python 3.12 python -m unittest discover -s experiments/prime_spectral -p test_boundary_moment_adjoint.py -v
lake build Reinmann.WeilAdjointPairing
lake env lean research/prime_spectral/verification_2026_10_11_boundary_moment/axiom_audit.lean
```
