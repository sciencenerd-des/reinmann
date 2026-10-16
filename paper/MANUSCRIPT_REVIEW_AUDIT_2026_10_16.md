# Audit of the 16 October manuscript review

Each claim in the cross-manuscript review was checked against the current files:
`rh-structural-theory` at `4fbdf5b`, plus the newer DH paper in the Codex
worktree. Numerical checks used mpmath at 30 digits.

**Verdict.** The review is a good presentation audit, and most of its figure
proposals are worth doing. It has three problems:

1. It misses two **mathematical errors** that matter more than clarity: the
   HEF definitions, and the sign in the same-height Dyson argument.
2. Three of its own claims are **wrong**: the Λ₀ plot premise, the size of
   the P_H/Q ratio, and the "RH corridor" label.
3. Many **line numbers are stale**. The DH section reviews the older 661-line
   draft, not the current 1,020-line one.

Fix correctness first, then figures.

## 1. Mathematical errors the review missed

### 1a. HEF companion: the functional is undefined (most serious)

The paper defines `b_m(t) = (−1)^m H_t^{(2m)}(0)`. With
`H_t(z) = 2∫Φ e^{tu²} cos(uz) du` this gives

    b_m(t) = 2 ∫ Φ(u) e^{tu²} u^{2m} du > 0,

which is a **raw moment** sequence. Cauchy–Schwarz then gives
`b_{n+1}² < b_n b_{n+2}` for every n and t, unconditionally. Hence

    Δ̄(2,n,t) = (b_{n+1}² − b_n b_{n+2}) / |b_n b_{n+2}| < 0   for all n, t.

The data confirm this at t = 0: b = 0.4971, 0.02297, 0.002963, … and
b_{n+1}² − b_n b_{n+2} = −9.5e-4, −5.0e-6, −1.2e-7, −5.9e-9.

Consequences:

- `log Δ̄(2,n,t)` is undefined for every n, so ℋ₂(t) does not exist.
- Theorem 1 ("absolute convergence") is false as stated.
- The quadratic "Jensen polynomials" `b_n + 2b_{n+1}X + b_{n+2}X²` always
  have nonreal roots.
- GORZ applies to `γ_n = n!μ_n` with `μ_n = 2M_n/(2n)!`, not to raw moments.
  The reduction paper (§4.3–4.4, H_n ≤ 1 is moment log-convexity) already
  documents exactly this distinction. HEF therefore contradicts the flagship
  manuscript.

The transport identity `∂_tΔ̄ = (Δ̄+1)Δ²ρ_n` is correct algebra, but it
concerns the wrong sequence.

Two corrections to the review's own HEF points:

- The review says Theorem 1 "silently assumes Δ̄ > 0 for n < M₀". In fact
  Δ̄ < 0 for **all** n.
- The review calls positivity of these finitely many terms "equivalent to
  hyperbolicity (and thus RH)". For fixed d that is not RH-strength:
  - for the correct sequence, d = 2 is the Turán inequality (CNV 1986);
  - fixed d is GORZ;
  - only all-degree hyperbolicity is RH.

The monotonicity-direction point (dℋ/dt ≥ 0 bounds ℋ(0) above, not below) is
correct but moot.

**Action:** do not add figures. Either withdraw HEF, or rewrite it on the
correct sequence γ_n, where the heat flow acts on μ_n with factorial weights.
The transport identity then has to be rederived. Delete §5.1 ("Dyson
stiffness") outright.

### 1b. Same-height paper §9.3 (Dyson force): the sign is wrong

The paper's ODE `dβ_k/dt = +Σ 2(β_k−β_j)/|s_k−s_j|²` has the wrong sign. For
`∂_tH = −∂²_zH`, a simple zero moves by

    ż_k = H_zz/H_z = 2 Σ_{j≠k} 1/(z_k − z_j).

With `s = 1/2 + iz` this gives `β̇_k = −2 Σ (β_k−β_j)/|s_k−s_j|²`.

Conjugate partners attract. The outermost off-line zero therefore moves
**toward** the critical line. This is de Bruijn's 1950 strip-shrinking
theorem, which the repository already uses (Λ ≤ 9/32 from the 7/8 strip). The
section's conclusion, "a complete dynamical repulsion pathway" ruling out
off-line zeros, contradicts a classical theorem.

**Action:** remove §9.3. The review proposed a panel drawing force vectors
pushing the outermost zero outward. Do **not** draw it: it would illustrate
a false claim.

### 1c. Same-height §9.1 (spectral operator): the argument fails for any boundary condition

The review's objection is right in spirit. The paper's domain is
`f(0) = f(1) = 0`; the review assumed periodic boundary conditions. The
gauge identity makes the point exactly:

    T_γ = e^{−iΘ} (−i d/dσ) e^{iΘ},   Θ' = θ'.

- **Dirichlet at both ends** (the paper's choice): T_γ is unitarily
  equivalent to −i d/dσ with the same conditions. That operator is
  symmetric but not self-adjoint, with deficiency indices (1,1), and its
  closure has spectrum equal to all of ℂ.
- **Periodic conditions:** the spectrum is exactly
  {2πk + ∫₀¹θ′ : k ∈ ℤ}.

Either way, sign changes of θ′ have no effect on the spectrum. The paper's
claims fail on both counts: that T_γ is "unitarily equivalent to a
self-adjoint operator", and that a zero of θ′ creates non-real spectrum.

Also correct "formalized in `SpectralPhaseBounds.lean.draft`". That draft
(`research/lean-drafts/`) contains three `sorry`s. **Action:** remove §9.1.

### 1d. Same-height §8 Step 4 (GUE), also flagged by the review

"Under GUE spacing … analytically impossible, proving that θ′ has constant
sign" is not a proof. Montgomery's pair correlation is an averaged
statistic, conjectural beyond restricted support, and gives no
deterministic bound at any individual zero. Reword it as a heuristic and
keep the empirical margin (|R−1| ≥ 0.0034 at zero #13) as data. The review's
two-panel P / N−E plot is a good replacement.

The §9.2 claim that conjugate symmetry confines saddles of the field to
σ = 1/2 is also unsupported. ζ′ has many zeros off the critical line
(Speiser; Levinson–Montgomery). Mark it as a conjecture or remove it.

## 2. Claims in the review that are wrong

| Review claim | What is true | Fix |
|---|---|---|
| Plot Λ₀(½+it) "crossing 0 near t ≈ 0.14 where Ξ(t) = ½" | Φ > 0 gives \|Ξ(t)\| ≤ Ξ(0) = ξ(½) = 0.497121 < ½. So Λ₀(½+it) ≥ 0.00576/(t²+¼) > 0, and Λ₀ has **no** zeros on the critical line (checked on [0,40]; the bound is global). | Strengthen the reduction paper's sentence: the level set {Ξ = ½} is empty on the line, and Λ₀ is strictly positive there, so every zero of Λ₀ is off the line. The plot is still worth making: Ξ(t) against the line y = ½ (gap 0.0029), plus Λ₀ > 0 with the true zeros marked. |
| DH: \|P_H\| is "10³ to 10⁴ times" \|Q\| "across every single control" | The ratios are 258 (DH5), 7157, 12570, 3375, 4328, 2700 and 5753, a range of **2.6·10² to 1.3·10⁴**. | Quote the actual range. In the bar chart, label Q − P_H as an *implied remainder*, not certified. The 99.9% figure is wrong for DH5 (99.6%). |
| Shade a "feasible RH corridor" between (n+2)/((n+1)s_n) and 1 | That band is the degree-2 Jensen/Turán corridor for γ_n, which is unconditionally true (CNV 1986). It is not RH. With s_n = (2n+3)(n+2)/((2n+1)(n+1)), the lower curve is exactly **(2n+1)/(2n+3)**, so the corridor width is **2/(2n+3)**, not "1 − 1/s_n ~ 2/n". | Label it "Turán (d=2) corridor" and annotate the width as 2/(2n+3). |
| README references deleted files `CREATIVE_BREAKTHROUGH_ATTEMPTS.md` and `NEAR_COINCIDENCE_COMPLETE.md` | The first exists at `research/CREATIVE_BREAKTHROUGH_ATTEMPTS.md`, but the README links it without the `research/` prefix. Only the second is missing. | Prune the section as proposed. |
| Weil §7: "far-block direct inverse energy ~9×10⁻²³" | **Correction to this audit:** the value is in the manuscript, as the direct far-block response energy ‖Q_M A c‖² < 9.0061×10⁻²³ (the line before Open Problem 7.2). All the scale-bar values are sourced. | Keep it, labelled "direct far-block energy" (it is a squared norm, not an inverse energy). |

Correct as stated:

- the Λ₀ formula `(1−2Ξ)/(t²+¼)`;
- the definitions of b_n, μ_n, γ_n, M_n;
- the Fekete prose (`Fin.insertNth`, `Fin.cycleRange`, `xiMinor_contigRows`);
- the Weil numbers (4.870e-41, 32 subcells, δ ≈ 0.0556);
- the DH bracket arithmetic (γ₁² ∈ (25.6, 26.3), γ₂² > 79.88);
- the Rouché conjugate-pair argument;
- the duplicate imports in `Reinmann.lean` (CoupledRankEnergy at 99 and 104,
  WeilRankTail at 97 and 105).

## 3. Stale references

- Same-height: the review cites §6.2–§8 at lines 331–508. The current
  sections are §7 (line 438), §8 (526) and §9 (576).
- Weil: the subcell text is at lines 874–925, not 441–545.
- DH: the review audits the older main-checkout draft. The current worktree
  draft (1,020 lines) already has:
  - the split-pair theorem (§`sec:splitpair`);
  - both shift-44 bands, 664–1099 and **1536–1972**, the second matching the
    pre-registered forecast of 1537 ± 2 to 1972 ± 2;
  - four figures (sector grid, second-band column, calibration, mixture
    collision path).

Re-target the DH suggestions to that version. The highest-value DH figure is
now the shift-44 sign column with the asymptotic cos curve of period
872.67, and it already exists.

## 4. Figure proposals worth keeping, with corrections

1. **Two-routes, Fekete engine (three matrix grids).** Keep it. The caption
   must credit Fekete, Gasca–Peña and Mao 2608.29224 Thm 2.5 for the
   mathematics; the contribution is the formalization.
2. **Weil, L-plane geometry plus a log-scale bar.** Keep both, with values
   from the paper, including the direct far-block energy 9.0061×10⁻²³.
3. **DH wedge figure.** Keep it, on **log-radial** axes. The disk |w| ≤ 64,
   the folded pair at |w| ≈ 7344 and a 0.41° wedge cannot share linear
   axes.
4. **DH attribution chart.** Keep it with the corrected ratio range. Show
   the quartet, the on-line sum and P_H as certified-sum quantities, and
   Q − P_H as an implied remainder.
5. **Reduction, Ξ-versus-½ plot and Turán corridor.** Keep them with the
   corrected premise and label from §2.
6. **Same-height winding schematic, panel (a).** Optional, and only after
   the §9 removals.
7. **HEF trajectories of ℋ_d.** **Drop.** The functional is undefined (§1a).

## 5. Recommended order of work

1. Withdraw or rewrite HEF. Remove same-height §9.1 and §9.3, reword the GUE
   sentence, and mark the §9.2 saddle claim as a conjecture. Neither paper is
   in any Zenodo metadata, so nothing published needs correcting.
2. Strengthen the reduction paper's Λ₀ sentence: Λ₀ has no zeros on the
   critical line.
3. Remove the duplicate imports in `Reinmann.lean`. Restructure the README
   into a four-track table, as the review proposes, and drop the June
   section.
4. Add figures in this order: reduction (Ξ vs ½, corridor), Weil (geometry,
   scale bar), two-routes (Fekete grids), DH (log-wedge, attribution).
5. Turn `RESEARCH_OBJECTIVE.md` into a comparison matrix, as proposed.
