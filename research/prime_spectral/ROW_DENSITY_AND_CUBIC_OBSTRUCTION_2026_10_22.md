# Row-density extraction and the obstruction to a cubic substitution

22 October 2026. This is an exponent and coefficient-identity audit, not a new
mean-square estimate, zero-free region, or Lean theorem. The source is OpenAI's
**unrefereed alternate 11/12 manuscript**, frozen at
[1581d4c, paper2.tex](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex).
The separate 7/8 manuscript/replay is not being re-proved or parameterized here.
The original [extraction note](QUASI_RH_EXTRACTION_BARRIER_2026_10_20.md)
remains the k=6 reconstruction.

The general optimization is correct. Three qualifications change the proposed
next step: the h>1 range gives 5/6, not 3/4, for k=3; k=1 has a whole ray of
minimizers; and cubic theta already occurs in the sextic proof. Replacing the
row character by a cubic character breaks its coefficient conversion and its
quadratic large-sieve reduction. This rejects the unchanged substitution, not
all possible cubic or arithmetic arguments.

## 1. Exact conditional extraction and optimization

Let K=Q(sqrt(-3)), O_K=Z[omega], omega=exp(2 pi i/3). Write mu_K for the ideal
Mobius function, and fix a finite excluded set S, a finite-order Hecke character
nu, and W in C_c^infinity((0,infinity)). All n below are nonzero integral ideals
prime to S. For residue-symbol evaluations use their primary generators.
These are not the ordinary Xi coefficients mu_n or the Jensen coefficients
n! mu_n. D is an ideal-norm sum scale; H is a row-norm cutoff.

Suppose an explicitly defined family has

    A_u(D) = sum_n mu_K(n) nu(n) rho_n(u) W(N(n)/D),
    sum_{0<N(u)<=H} |A_u(D)|^2 << D^(1+epsilon) H.             (MS)

Suppose also that, for prime ideals p of norm about Y=H^(1/k),

    rho_n(p^k) = 1_{p does not divide n},
    A_{p^k}(D) = M_nu(D) + O(D/Y),
    M_nu(D) = A_1(D).

The number of these distinct rows is J asymptotic to Y/log Y. Nonnegativity
of the family squares and |x+y|^2 <= 2|x|^2+2|y|^2 imply

    |M_nu(D)|^2 <= (2/J) sum_p |A_{p^k}(D)|^2 + O(D^2/Y^2)
                << D^(1+epsilon) H^(1-1/k) + D^2 H^(-2/k).   (E)

The logarithm is absorbed into D^epsilon for fixed positive h and k when
H=D^h. Constants may depend on the fixed data, h, k and epsilon; there is no
claim of uniformity as k grows or as h approaches a boundary. For the actual
sextic family (MS) is Proposition `thm:ms`, equation `eq:ms`, in the source;
(E) is `eq:prime-extract` at k=6. The general k statement is conditional on
its family and these hypotheses; neither is supplied for arbitrary k.

After taking square roots, set

    A(h) = 1/2 + (k-1)h/(2k),
    B(h) = 1-h/k,
    sigma_k(h) = max(A(h), B(h)).

For every real k>=1 and every h,

    [2/(k+1)] A(h) + [(k-1)/(k+1)] B(h) = k/(k+1).

Both weights are nonnegative and sum to one. Thus sigma_k(h)>=k/(k+1).
The two lines meet at h=k/(k+1), attaining that bound. For k>1, A increases
strictly and B decreases strictly, so this is the unique minimizer. For k=1,
A=1/2 is constant: **every h>=1/2 minimizes**, and 1/2 is only the smallest
minimizing h. No negative or nonasymptotic family length is needed for this
calculation.

| k | Smallest minimizing h | Unrestricted minimum of sigma | Infimum for h>1 |
|---|---|---|---|
| 1 | 1/2 | 1/2 | 1/2 |
| 2 | 2/3 | 2/3 | 3/4 |
| 3 | 3/4 | 3/4 | 5/6 |
| 4 | 4/5 | 4/5 | 7/8 |
| 6 | 6/7 | 6/7 | 11/12 |

Indeed, at h=1, A=1-1/(2k) and B=1-1/k. For k>1, A dominates and increases
on h>=1. The manuscript proves only H=D^(1+vartheta), 0<vartheta<=1/10, and
lets vartheta decrease to zero within the exponent loss. A cubic analogue
in **that same range** would yield 5/6+epsilon; 3/4+epsilon would additionally
need H=D^(3/4), or a suitable limiting short-family range. The 7/8 at k=4
in the last column is not an identification of the separate 7/8 proof with a
quartic variant. The algebra supplies no quartic family over this field.

These minima optimize an assumed **upper bound**. They are not lower bounds
on actual Mobius sums, impossibility theorems for arithmetic, or a proof that
another extraction cannot do better.

## 2. Where the sixth powers enter, before the estimates

In the actual family, rho_n(u)=chi_n(u)=(u/n)_6. The row identity is

    chi_n(p^6) = 1_{p does not divide n},
    chi_n(p^3) = (p/n)_2.

The second is a quadratic twist of the column variable, varying with p, not
the untwisted M_nu(D). Fixed-character bounds with constants depending on nu
do not remove a new conductor depending on p.

There is a small exact counterexample to using cubes in this family. Take
column prime n=-2-3omega (norm 7) and row prime p=1-3omega (norm 13). Both are
primary, prime to 6 and coprime to each other. Modulo n, omega=4 and p=3 in F_7.
The quadratic residue of 3 is -1, so chi_n(p^3)=-1 while chi_n(p^6)=1.
The verifier computes these character values with modular integers, without
floating-point complex arithmetic.

Changing the family to rho_n=chi_n^2 does make p^3 a principal row. That is a
change of the original arithmetic problem, not a denser subset of the existing
family. It must pass the next two tests.

## 3. First obstruction: Poisson produces different theta coefficients

Use the source's normalized Gauss sums gamma_j(n), alpha(n)=n/|n|, and its
fixed-ray factor G(n). Lemma `lem:arithmetic`, equations `eq:gj`, `eq:convert2`,
and Appendix `app:gauss-identities` give, for squarefree n away from S,

    gamma_2(n)^3 = mu_K(n) alpha(n),
    gamma_2(n) gamma_{-2}(n) = 1,
    mu_K(n) gamma_{-1}(n)
      = chi_n(-1) G(n)^(-1) conjugate(alpha(n)) gamma_2(n).    (S6)

Sextic Poisson supplies gamma_{-1}; (S6) converts the original Mobius factor
into the **single cubic Gauss coefficient** used by Kubota's theta function.
The theta series is therefore already cubic in the original proof.

Cubic Poisson instead supplies gamma_{-2}. The same exact identities give

    mu_K(n) gamma_{-2}(n)
      = conjugate(alpha(n)) gamma_2(n)^2.                   (C3)

Equivalently, the same source identity gamma_1 gamma_2=mu_K alpha G gives

    mu_K(n) gamma_{-2}(n)
      = conjugate(alpha(n)) G(n)^(-1) gamma_1(n).             (C6)

Thus Mobius is absorbed, but into a **sextic Gauss coefficient** rather than
the single cubic-theta coefficient. A square of a cubic Gauss coefficient is
another description of that change. Relative to the coefficient in (S6), the
residual factor is gamma_2(n), not the source's fixed-ray factor. In particular gamma_2(n)^3=mu_K(n)alpha(n)
is not finite-valued on all these n; it cannot simply be absorbed into a
fixed finite-order ray character. For a split primary prime p with p and
conjugate(p) nonassociate, alpha(p) is not a root of unity: otherwise
alpha(p)^2=p/conjugate(p) would be a root of unity in K, contradicting its
nonzero prime-ideal valuations. The norm-7 example already has this property.

A conjugate choice of cubic character gives the analogous squared-conjugate
Gauss coefficient. Multiplying theta functions does not solve this identity:
Fourier coefficients of a product are convolutions, not pointwise squares.
No ordinary-squarefree-index automorphic realization with the required
summation formula and mean-square costs for (C3)/(C6) is established here.
This does not say that sextic Gauss sums have no metaplectic interpretation. The four exact finite-field Jacobi checks at norms
7,13,19,31 confirm the normalization J(chi_3,chi_3)=-p used in these formulas;
they do not prove every global theta identity.

## 4. Second obstruction: the quadratic large sieve is lost

Even if the coefficient problem in (C3) were separately solved, the existing
reflection argument cannot be kept verbatim. Equation `eq:theta-local-factors`
in the source gives, for its ordinary theta coefficient and generic j,

    B_{p,j}(x) = chi_p(x)^(-j-2),        j not in {0,4}.

Thus j=1 becomes chi_p^3 (quadratic), whereas j=2 becomes chi_p^2 (cubic).
The latter is not in the family covered by
[Goldmakher–Louvel, Theorem 1.1 and Corollary 1.2](https://arxiv.org/abs/1112.1642).
This is a diagnostic of the proposed unchanged use of that reflection formula,
not a newly derived reflection theorem for the squared coefficients in (C3).

The quadratic sieve factor is M+L. The available generic higher-order sieve
in [Blomer–Goldmakher–Louvel, Theorem 1.3](https://arxiv.org/abs/1112.1650)
adds (ML)^(2/3), up to epsilon losses. At M=L=X that term is X^(4/3), not O(X).
Replacing one sieve by the other therefore does not preserve the same
balanced-scale bound. This comparison is not a derivation of a complete new
cubic-family bound: the coefficient identity, squarefree restrictions, weights
and cube-divisor transfers would all need to be supplied first.

There is also an independent range restriction. The source's final
`eq:initial-positive-gap` has, schematically, dual rows Hcal~D^2/H, columns
X~D and Hcal/X~D/H. Its recursive argument needs a positive power gap
Hcal/Sigma << D^(-vartheta). For H=D^(3/4), the basic ratio instead grows
like D^(1/4). Changing the extraction exponent does not prove this missing
short-range recursive estimate.

The comparison with the literature must retain conditionality:
[Dunn–Radziwill, arXiv:2109.07463v3](https://arxiv.org/html/2109.07463v3),
§5, Lemma 5.4 and Proposition 5.3 give the theta/cube-completion tools;
Theorem 1.4 and Remark 1.1 state that their sharpness lower bounds for the
cubic large sieve are **GRH-conditional**, while the quoted upper bounds are
unconditional. Neither a GRH-dependent dispersion estimate nor its conditional
sharpness may be imported as an unconditional proof of RH. Dunn's
[2025 cusp-form paper](https://arxiv.org/html/2403.13151v4), Theorem 1.5 and
Proposition 1.6, concerns different bilinear/linear sums; it does not supply
(C3) or the required short-family Mobius estimate.

Conclusion of the source audit: the same proof does **not** give a cubic-row
3/4 theorem. Sixth-power extraction is the principal-row identity of this
particular sextic construction. This does not prove that sixth powers are
unavoidable in every metaplectic approach.

### Relevant sextic prior art and the narrower next question

[Broeker–Hoffstein, Fourier coefficients of sextic theta series,
arXiv:1312.0568v1](https://arxiv.org/html/1312.0568v1), introduction and §5,
is directly relevant to (C6). It discusses the sixth-cover coefficient
relations, including a normalized Gauss-sum formula at **fourth-power prime
indices**, with local normalization qualifications, and partly conjectural
coefficients at other indices. That is not an identity identifying gamma_1(n)
with ordinary squarefree-index coefficients and the same cutoff X. A proposed
use of fourth-power indices must account for their different norm scale,
missing-index completion and local factors. No same-cost passage is justified
by merely naming the sextic theta function.

A concrete specialist question is therefore whether the clean representative
coefficient family

    sum_{N(h)<=Hcal} |sum_{n squarefree} conjugate(alpha(n)) G(n)^(-1)
        gamma_1(n) xi(n) chi_n(h)^2 U(N(n)/X)|^2

has a metaplectic treatment with the required constants and exclusions. This
is a **model for an open intermediate obligation**, not an assertion that it
alone supplies every common-divisor/auxiliary family in the original proof.
Even a result for Hcal<=X would not give the optimal cubic extraction range:
H=D^(3/4) leads to Hcal=D^(5/4)>X at X=D.

The recent [Xu–Sang preprint, arXiv:2610.17675v2](https://arxiv.org/html/2610.17675v2),
§§1–2, explicitly distinguishes arbitrary-coefficient sextic operator norms
from moments of specified prime coefficients. Its matching lower-bound claim
uses moment inputs from OpenAI's manuscript; it is not independently replayed
or proved here. Its structured prime bound is not the above Mobius-derived
coefficient family and does not furnish the short-family estimate. In
particular a worst-case large-sieve norm, whether sharp conditionally or
otherwise, is not a lower bound for our particular Mobius vector. This audit
cannot turn those norm statements into a general arithmetic impossibility
claim.

## 5. RH endpoint and its exact DH distinction

For nu=1 and every W, a bound M_1(D)<<D^(1/2+epsilon) gives nonvanishing of
zeta_K in Re(s)>1/2 by the same Mellin argument used in §3 of the source:
choose W with Mellin transform nonzero at a putative zero. Together with the
functional equation this is RH for zeta_K. The reverse implication is the
standard Mobius/Perron consequence of RH for this fixed Dedekind zeta; no new
proof of that classical equivalence is claimed. Omitting finitely many Euler
factors changes no zero in Re(s)>0. Since

    zeta_K(s) = zeta(s) L(s,chi_{-3}),

and the second factor has no pole cancelling a nontrivial zero of zeta, RH for
zeta_K implies RH for zeta. This is stronger than merely RH for zeta; it also
controls the quadratic Dirichlet factor.

However, the extraction algebra does **not** force H=D^(1/2) at k=1: it is
only the smallest h attaining 1/2. Any H=D^h with h>=1/2 has the same exponent.
Furthermore, a literal character-valued order-one residue family is principal.
It no longer has the nontrivial character variation used by the Poisson/theta
argument. Its desired coefficient-specific mean square already demands the
missing Mobius cancellation. Therefore “prove a shorter large sieve” is not,
on its own, a construction of an RH strategy. A genuinely new family/identity
and an estimate for its actual Mobius coefficients would have to be specified.

It is also too strong to say that a DH cancellation analogue cannot be stated.
Write H_DH(s)=sum a_n/n^s, a_1=1, with the actual period

    (a_0,a_1,a_2,a_3,a_4) = (0,1,kappa,-kappa,-1),

and let b be its ordinary **Dirichlet inverse**, a*b=delta_1. These coefficients
can be put into a smoothed sum, or lifted as b(N(n)) to ideal indices. They
are not multiplicative. An exact witness, even away from primes 2,3,5, is

    b_7 = -kappa,        b_13 = kappa,
    b_91 = -1-2 kappa^2,
    b_91-b_7 b_13 = -1-kappa^2 < 0.

This is not a missing implementation: the verifier performs polynomial
Dirichlet inversion through index 91 and checks the convolution exactly.
It rules out identifying these coefficients with an ideal-Mobius/Hecke Euler
product. No fixed finite deletion repairs the global problem: primes in the
classes 7 and 13 modulo 15, outside any fixed excluded set, give the same
calculation. No minimal cancellation scale or first PF failure is inferred.

A square-root smoothed reciprocal-DH bound for every W would contradict its
classically known zeros with Re(s)>1, via the Mellin argument. The retained
Titchmarsh §10.25 reference in the register is literature evidence, not a
newly located finite-D witness. A replacement DH metaplectic family remains
uninstantiated; no transfer of theta reflection is asserted.

Thus this entry has a **named and algebraically checked structural separator**:
ideal Mobius/Hecke coefficients and the exact Gauss-to-theta identity. Its
RH-level mean-square estimate, admissible prime-density family, and a method
proving that estimate remain open. The register's flag for an active RH
strategy with a proved separating inequality stays false.

## 6. Reproduction and disposition

Run, from the repository root:

    python3 experiments/prime_spectral/verify_row_density_extraction.py

The immutable `verification_2026_10_22_row_density/exact_checks.json` records
exact rational exponent checks for k=1,...,100, exact local Jacobi/character
checks and the exact DH reciprocal defect. The universal optimization proof is
in §1; finite checks are not misrepresented as a universal or Lean proof.
The source URLs, downloaded-source SHA256 and equation labels are retained in
that directory. The specialist review draft accompanies this note.

Do not build a cubic-family analytic pipeline from the unchanged substitution.
Reopen that direction only with a justified coefficient realization for (C3)/(C6), the
corresponding reflection/sieve estimates, and an explicit valid parameter
range. These are concrete arithmetic obligations, not a forecast. Finite-window
Weil work may continue only as finite calibration; further PF boxes and stopped
Jensen/Toeplitz scans are not restarted by this note. No publication or external
contact is made in this round.
