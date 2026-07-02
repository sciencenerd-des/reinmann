# Current RH Frontier Review

**Date:** 2026-06-30
**Status:** research review and next theorem target; not a proof of RH.

## Bottom line

The Riemann Hypothesis remains unsolved.  The honest local status is:

1. The repo has strong Lean-checked reduction infrastructure.
2. The same-height fiber papers isolate an RH-equivalent obstruction, but do not
   make that obstruction easier.
3. The direct Hankel/moment route was correctly demoted: it asks for the wrong
   curvature.
4. The strongest current direction is the corrected Toeplitz/Pólya-frequency
   route for the signed coefficients of Riemann's xi function.
5. We are not "close" in the sense of having only a routine lemma left.  We are
   close only in the architectural sense: the proof-search target is now narrow,
   sign-correct, and falsifiable.

The right next mathematical problem is:

> Prove all order-`k` Toeplitz minors of the signed xi coefficient sequence are
> nonnegative, starting with a serious attack on the first genuinely open
> order-3 family.

Equivalently, prove that the signed xi coefficients form a Pólya-frequency
sequence without assuming RH.

## External standing

The Clay Mathematics Institute still lists RH as **Unsolved** and states it as
the claim that all non-obvious zeros of the zeta function have real part `1/2`:
https://www.claymath.org/millennium/riemann-hypothesis/

The best relevant published terrain for this repo is:

- Jensen route: Griffin-Ono-Rolen-Zagier prove asymptotic Jensen hyperbolicity
  and hyperbolicity through degree 8, but not the all-degree/all-offset theorem:
  https://arxiv.org/abs/1902.07321
- de Bruijn-Newman dynamics: Rodgers-Tao prove the Newman constant is
  nonnegative; RH would require the opposite inequality `Lambda <= 0`:
  https://arxiv.org/abs/1801.05914
- computation: Platt-Trudgian rigorously verify RH up to height `3 * 10^12`,
  which is evidence but not a proof:
  https://arxiv.org/abs/2004.09765

## Audit of accumulated local papers

### `paper/rh_reduction_paper.tex`

This is the strongest paper in the folder.  It says the right thing: no RH proof,
only machine-checked conditional reductions.  Its central value is the correction
from the wrong completed-zeta target to Riemann's `xi`, and the tightness result:
assuming the classical bridges, the Toeplitz/PF positivity condition is
equivalent to RH.

Verdict: keep and sharpen.  This is the publishable spine if the framing remains
strictly "verified reductions and frontier localization."

### `paper/rh_same_height_fiber_framework.tex`

This is a valid reduction-style paper: an off-critical zero forces a reflected
same-height partner, so RH is equivalent to same-height fiber uniqueness under
the required symmetry setup.  But that uniqueness principle is RH-strength.  It
does not currently import an independent analytic handle.

Verdict: keep as formal architecture, not as the primary proof route.

### `paper/hef_companion_paper.tex`

The Hyperbolic Entropic Flow idea is directionally related to de Bruijn-Newman
and Jensen deformation, but the draft overstates the current mathematics.  The
global monotonicity of the entropy functional is the whole missing theorem, not
a consequence of the definitions.  GUE/Dyson stiffness is statistical evidence
and heuristic structure; it is not a deterministic proof input unless converted
into a rigorous inequality.

Verdict: demote to speculative theory notes until the monotonicity theorem is
made precise, local, and testable.

## Audit of active Lean routes

### Correct foundation

`Reinmann/JensenProgram.lean` now defines `Xi` from Riemann's `xi`, not from the
wrong `completedRiemannZeta0` slice.  The key checked target is:

```lean
Xi_eq_zero_iff_riemannZeta :
  Xi t = 0 ↔ riemannZeta (1 / 2 + (t : Complex) * Complex.I) = 0
```

That correction is essential.  Without it, Jensen, Toeplitz, and moment claims
would target the wrong function.

### Superseded route

`Reinmann/XiTotalPositivity.lean` documents the old Hankel path and its
obstruction.  Hankel positivity is a moment/Stieltjes condition and forces
log-convexity.  The xi Laguerre-Polya product wants the opposite curvature:
Toeplitz/PF log-concavity.

Verdict: retain as a warning and source of determinant lemmas, not as the lead
program.

### Correct route

`Reinmann/XiToeplitzPositivity.lean` is now the lead route.  It defines
`XiToeplitzTotalPositive`, proves the `1x1` and `2x2` consequences, connects the
`2x2` minor to the Turan inequality, and exposes the first real frontier at
order `3` and above.

`Reinmann/XiMomentKernel.lean` now specializes the complete kernel ladder to this
first frontier rung:

```lean
xiToeplitzOrder3Positive_iff_moment_of_kernelRep :
  XiToeplitzOrder3Positive ↔ MomentToeplitzOrder3Positive M
```

under Pólya's moment representation.  This moves the next proof attempt from a
bare coefficient inequality to an explicit factorial-weighted moment determinant
for the xi Fourier kernel.  The same file also proves
`momentToeplitzOrder3_eq`, an explicit algebraic expansion of that determinant
in terms of the weighted moments `M n / (2n)!`.  It also names the central-scale
normalization and adjacent-ratio expression used by the numerical probe.

The exact proof-search spine is:

```text
signed xi coefficients are PF
  -> Edrei-ASW / Laguerre-Polya bridge
  -> scaled finite real-rooted approximants
  -> Jensen hyperbolicity
  -> RH
```

The bridges are classical or named external inputs.  The nonclassical payload is
proving the PF hypothesis for the concrete xi coefficients.

## How close are we, truthfully?

Not close to a proof.  The all-order PF condition is essentially RH-strength for
this sequence.  Proving it directly would be a major theorem.

But the repo has made real progress in a different sense: it has converted a
large vague search space into a small list of precise theorem targets, and the
best one is now sign-correct.  The viable next step is not "prove RH"; it is:

1. prove or disprove the order-3 Toeplitz minor family;
2. identify a kernel-level total-positivity theorem that implies all orders;
3. formalize each successful finite rung in Lean;
4. only then return to the global RH implication.

## The next theorem to attack

Let `mu n = (-1)^n * XiCoeff n`.  The order-3 contiguous Toeplitz determinant is

```text
det [
  mu(n+2)  mu(n+1)  mu(n)
  mu(n+3)  mu(n+2)  mu(n+1)
  mu(n+4)  mu(n+3)  mu(n+2)
]
```

The immediate target is:

```lean
def XiToeplitzOrder3Positive : Prop :=
  ∀ n : Nat, 0 ≤ XiToeplitzMinor3 n
```

This is the first rung not covered by the classical Turan/order-2 story.  If we
can prove it from the explicit Pólya kernel, we get a genuinely new foothold.  If
we cannot, the failure mode will still teach us whether the PF route needs a
different normalization or a stronger kernel theorem.

## Concrete next work package

1. Use the newly added `XiToeplitzOrder3Positive` as the named intermediate
   target for the first non-Turan rung.
2. Build a symbolic expansion of the order-3 determinant in terms of the
   factorial-weighted moments of Pólya's kernel.
3. Use `research/ORDER3_TOEPLITZ_FRONTIER_LOG.md` as the current numerical
   baseline: offsets `n = 0..116` are positive, and the smallest normalized
   margin occurs at the last tested offset.  The tail data currently points to
   a possible cubic-scale lower bound `D_n >= c / (n+1)^3`.
4. Search for a known total-positivity theorem applying to kernels of the form
   `cosh(u * sqrt(z))` integrated against the xi Fourier kernel.
5. If a plausible theorem is found, encode its exact hypothesis as a Lean
   contract before attempting prose proof.

The cross-field incorporation pass is now tracked in
`research/CROSS_FIELD_INCORPORATION_2026_07_02.md`.  Its conclusion is that
combinatorial total positivity / Lorentzian-polynomial methods are the most
direct outside tools for the order-3 target; elliptic-curve/Weil, Euclidean
convexity, and hyperbolic geometry become actionable only if they supply one of
the registered `CrossFieldOrder3Witness` contracts.

## Working rule

Every future note should label claims as one of:

- **Lean-verified**: checked by the local verifier.
- **Classical external theorem**: cited but not formalized here.
- **Numerical evidence**: computed, not proof.
- **Frontier conjecture**: the new mathematical payload.
- **Rejected route**: known obstruction or false target.

This keeps the project aggressive without allowing proof-shaped speculation to
masquerade as a proof.
