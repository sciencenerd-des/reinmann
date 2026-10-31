# Directions B–E: bounded trials and outcomes (1 November 2026)

**B:** the localized H(4/5) hypothesis can be priced in the refined
numerator system with a rational conditional certificate at **0.874825**.
This is below B_flat, but above the older conditional pointwise certificate
0.874793. It is not an improved best conditional result, an arithmetic
estimate, or an optimized boundary.

**C:** Xu–Sang's structured-prime theorem does not supply that inverse
moment as stated. Its support and scale restrictions fail for the target
Mobius vector; an additional coefficient-sensitive transport is missing.

**D:** the Hadamard motivation for upgrading Lean is already satisfied by
the attributed PNT+ backport. Its actual folded-Xi theorem builds and has
only standard Lean axioms on 4.30. The external 7/8 theorem remains a
separate-toolchain input. No blanket toolchain upgrade was performed.

**E:** a targeted library search did not locate the full finite
Caratheodory–Fejer kernel theorem. The nontrivial missing component is a
finite Toeplitz moment representation (or the equivalent quotient/unitary
construction), not a scalar coefficient check. No CF theorem is claimed
formalized in this round.

The DH register was updated before these trials. No arithmetic route is
activated, no stopped scan is restarted, and no publication, outreach,
novelty or RH claim accompanies them.

## B. A band-only refined certificate

The hypothesis is the original ideal-Mobius mean square, with original
Eisenstein ideal norms, ray/sextic twists, zero extensions, excluded
primes, smooth seminorms and height costs:

\[
\sum_{q_u\asymp U}|M_u(U^r)|^2
\ll U^{1/5+4r/5+\epsilon}(1+T_1)^A,
\qquad 1099/1000\le r\le119/100.
\]

Outside that band retain the old amplification exponent 5/6. The saving
against the old long moment is still `(D/U)^(1/30)`. No replacement DH
family is implemented. The preceding 7/8 bound supplies kappa=3/4; the
conditional conclusion does not license itself.

Choose the exact rational parameters

\[
\kappa=3/4,\quad b=17/200,\quad\ell=5021/30000,\quad
B=34993/40000=0.874825.
\]

With c=1/(3*kappa), use the refined count polynomials

\[
D_c=3-(1+2c)x,\quad P_c=(2-2cx)(1-x),\quad
J_\alpha=(\alpha-\delta)D_c+\delta P_c,
\]

\[
R_\alpha=1-\delta+
\frac{(\alpha-\delta)\delta P_c}{2J_\alpha},\qquad
t_\alpha=1+\frac{\delta P_c}{2J_\alpha}.
\]

The old count suffices outside the sufficient class box

\[
21/50\le\delta\le51/100,\qquad21/50\le x\le1/2.
\]

This moves the old box's delta interval from [1/3,47/100] to
[21/50,51/100]; the needed r band stays unchanged. No box or band is
claimed minimal. Exact derivative/positive-polynomial certificates cover
the two delta sides; a shifted positive discriminant covers x<=21/50.

### Enforce the length band instead of extrapolating the improved moment

Inside the box set alpha=4/5 and choose
`t=min(t_alpha,119/100)`. Exact tensor Bernstein coefficients verify
t_alpha>1099/1000 throughout the box. For r below the band the old long
bound increases up to its value at r_lo; within the band the new bound
increases up to t. The original short moments give R_short(t). Therefore
the count is bounded by the envelope

\[
\max\{R_{4/5},\ R_{\rm short}(119/100),\
1-5/6+(5/6-\delta)(1099/1000)\}.
\]

This follows by considering t_alpha<=r_hi and t_alpha>r_hi separately:
in the first case the new long and short branches balance; in the second
the capped short branch dominates the new long branch. The old count
remains separately available. The cutoff cap is genuinely used: t_alpha
at delta=51/100,x=1/2 exceeds 1.19. Using R_alpha alone there would silently
assume the improved moment beyond its registered band.

Insert this envelope into the refined endpoint

\[
E=C_0+\delta/2+\delta x\{\ell+c(h/4-l_y/2)\}
 -(3h/4)(1-R),\qquad C_0=-1/4+b/6+5\ell/4.
\]

The R_4/5 branch has a positive completed-square discriminant. The capped
short and old-long branches have strictly positive tensor Bernstein
certificates for their negative endpoints on the full box. The maximum
envelope is thus controlled uniformly, rather than by a sampled grid.
An independent affine-cell detector check tests that envelope separately.

All printed fixed-geometry auxiliary conditions are retained and strictly
checked: direct support/Gram bound, principal region, prime supply, plain
numerator gate, small-delta bound, detector floor, small rows, and positive
row-extension reserves. In particular ell/h>21/100. The full direct
majorant equals B; a positive row extension and retained margin absorb
the sufficiently small losses in this scalar ledger.

The receipt is
`verification_2026_11_01_other_directions/refined_localized_certificate.json`.
It does not reprove the analytic assembly with the hypothetical moment.

### What this certificate does and does not improve

It improves the refined **baseline** B_flat by more than 0.000061647039964.
However the old pointwise conditional certificate gives the smaller bound
0.874793 under the same global length-band moment hypothesis. That remains
the better existing conditional payoff in this repo.

The old geometry cannot simply be declared admissible in the printed
refined system: its ell/h-21/100 is `-113543/48396300`, and its reserve
against the coarse small-delta threshold -1/250 is
`-405562241237/116151120000000`. These are failures of that sufficient
admissibility package, not disproofs of sharper row estimates or the
arithmetic hypothesis. Replacing coarse gates or mixing numerator choices
would require a further explicit assembly audit. We do not chase an
optimized conditional decimal here or suggest this conservative certificate
as a new publishable result.

## C. Why the structured-prime theorem does not supply H_band

Versioned primary source:
[Xu–Sang 2610.17675v2](https://arxiv.org/html/2610.17675v2), Sections 6–7.
The source archive SHA-256 is
`7f7f2cbad8ed6c15e485b00053c5e4bac55adddf784dfa81b90ca6de58dde24c`.
The archive's TeX file is `sieve_100.tex`; source anchors and its hash are
recorded in `coefficient_and_gate_audit.json`.

Section 6 explicitly imports the original inverse moment
`E(r)=max{1,(1+5r)/6}`. It combines it with the plain fourth moment and
buffered detector to obtain density, then uses logarithmic-derivative
contours for prime sums. The output is a theorem about structured prime
coefficients, not a new inverse moment.

The Section 7.3 extension is broader than prime-only support: it includes
bounded convolutions of independently weighted large primes. But it
requires a fixed bound k<=k0 on the number of factors, every factor norm
at least Y^c for fixed c>0, logarithmically controlled smooth weights, and
row norm and column-product norm both comparable with Y. It gives a raw
second-moment bound

\[
Y^{\kappa_6+\epsilon}+Y^{13/6-c+\epsilon},\qquad
\kappa_6=(37-10\sqrt6)/6\simeq2.084183762.
\]

The desired inverse polynomial has unrestricted squarefree-composite
support at column length D=U^r while rows have norm U. A fixed allowed
prime ideal p0 outside finite S can divide squarefree products p0*q at
arbitrarily large D; their Mobius coefficients are nonzero, while p0 is
eventually smaller than D^c for every fixed c>0. Thus the full vector is
not in the rough-convolution class. A support decomposition would need
controlled sums of components and cross terms, plus an unbalanced
conductor/length estimate and the original height uniformity. None is
provided by this theorem as stated.

Even an illustrative, **unproved** balanced-to-unbalanced substitution
Y=D would not directly give the requested exponent: normalizing the raw
prime term by D gives `r*(kappa6-1)`. This exceeds `1/5+4r/5` by more
than 6683/60000 across the requested band. The simple rational comparison
uses sqrt(6)<49/20, hence kappa6-9/5>17/60. This compares supplied upper
bounds; it is not a lower bound on the actual Mobius moment or a
disproof of H_band.

**Decision:** the published estimate does not supply the localized gain
as stated. Its adaptation would require a new coefficient-sensitive
argument, not a change of normalization or a direct theorem substitution.
That arithmetic step remains unproved and has no DH instantiation.

## D. The existing Lean backport already supplies Hadamard

Live inspection finds the attributed backport under
`Reinmann/PNTPlus`, with upstream commit and adaptation hashes in
`UPSTREAM.json`. The upstream 4.35 sources were ported to the current
Lean/Mathlib 4.30 checkout. `Reinmann.XiHadamardProduct` imports its
Hadamard theorem and is itself imported by `Reinmann.lean`.

The targeted build completed successfully (3637 Lake jobs, with existing
style warnings). A separate Lean 4.30 probe checks the imported xi
Hadamard theorem and the actual `foldedXi_product`; axiom prints for the
folded product and order bound contain only `propext`, `Classical.choice`,
and `Quot.sound`. The first probe used an incorrect namespace for the
upstream theorem; its diagnostic is retained, and the corrected probe
passes. This was a probe-name correction, not a proof repair.

The earlier README sentence saying this backport remained outside the root
import was stale and is corrected. The literature review's suggestion
that an upgrade is required to obtain the Hadamard factorization is also
corrected. Toolchain and dependency pins are unchanged. No fresh full-root
or CI build is claimed.

The external 7/8 proof remains different: `QuasiRHInputs.lean` explicitly
carries it as a named proposition; it does not import the external theorem.
Installed toolchains are 4.27.0, 4.30.0 and 4.34.1; 4.35 is not installed.
Unifying the external 7/8 development with this checkout would still need
an isolated dependency migration or port and its own complete checks.
The Hadamard motivation alone does not justify that migration now.

## E. A precise remaining formalization task

Primary reference:
[Connes–van Suijlekom 2511.23257, Section 2](https://arxiv.org/html/2511.23257).
Target a Hermitian PSD Toeplitz matrix T of size n+1 and rank n, and a
**nonzero** kernel vector v. With p_v(z)=sum_(j=0)^n v_j*z^j, show every
zero has modulus 1. The nonzero-vector condition must be explicit in a
formal statement.

A targeted search found PSD/Hermitian matrix and polynomial tools, but no
ready finite CF theorem, Toeplitz atomic moment representation, or matching
kernel-root theorem in this Mathlib checkout. This is a search result, not
a proof that no differently named library result exists.

One possible route is to prove a finite atomic representation with n
distinct unit-circle nodes and positive weights. In the convention
`T_ij=sum_r w_r*conj(z_r)^i*z_r^j`, the kernel relation then gives
`sum_r w_r*|p_v(z_r)|^2=0`. Positivity forces n distinct roots; the
degree bound forces all roots onto those nodes. The substantial missing
theorem is obtaining that representation from the PSD Toeplitz/rank
hypotheses (or proving the equivalent finite quotient/unitary construction).
Assuming this representation and formalizing only its immediate root
consequence would not complete the proposed CF contribution.

No new Lean CF module or placeholder theorem is added. The full task
remains open as shared formal infrastructure that also applies to DH;
it has no newly identified RH discriminator.

## Reproduce and scope

```sh
python3 experiments/prime_spectral/liu_refined_localized.py
python3 -m unittest discover -s experiments/prime_spectral -p 'test_liu*.py' -v
python3 experiments/prime_spectral/check_dh_research_gate.py
lake build Reinmann.XiHadamardProduct
lake env lean research/prime_spectral/verification_2026_11_01_other_directions/HadamardProbe.lean
python3 research/prime_spectral/verification_2026_11_01_other_directions/validate.py
```

All checks are local and bind the actual dirty working tree and HEAD.
Earlier verification files are checked unchanged; the previous threshold
packet and its predecessors replay against their historical source inputs.
No immutable manifest, existing model of a stopped scan, release, or
publication is changed. Nothing is committed.
