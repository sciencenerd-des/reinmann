# Research directions after the October 2026 frontier (2026-10-12)

Status: an assessment of the program plus new floating-point measurements
made today. **No new theorem, no certificate, no RH claim.** Every number in
§2 is an approximate eigenvalue of a finite Fourier compression of the
semilocal Weil form, computed with Arb midpoints. These numbers are
diagnostics, not proofs. Prior-art checks marked **[check]** have not been
done. Do not write novelty language until they are.

## 1. Where the program stands

| Route | Proved / certified | Open core | Quantitative reality |
|---|---|---|---|
| Toeplitz PF∞ of Xi coefficients | Lean reduction, axiom-clean; finite PF43 (classical) and PF58 (quasi-RH); strict finite PF by zero extraction | strict ladder at unbounded rank | Rank r is "RH up to height ≈ r/π". With Platt–Trudgian this is r ≈ 10¹³ ([novelty review](OPENAI_MATH_RELEASE_AND_NOVELTY_REVIEW_2026_10_07.md)). Fixed rank is zero verification in another form. |
| Jensen / HPSS | Lean interfaces; degree ≤ 3 pieces | HPSS + all-degree hyperbolicity | Fixed degree is classical (GORZ). |
| Weil windows | Arb certificates up to C ≈ 4.9998, a replication of Zhu; Lean scalar interfaces | cofinal positivity | Margin ≈ e^{−11.6 C}. Liu claims C ≈ 8.37. |
| Trace / prime activation | Written analysis: renewal traces, δ/log(1/δ) entry law, cluster Feshbach bound | trace-transfer gate | Assembled trials **fail** the gate, certified by a lower bound ([note](prime_spectral/ASSEMBLED_TRIAL_FULL_RESIDUAL_2026_10_07.md)). |

The infrastructure is real: Lean audit, Arb pipelines, and honest gating.
Three observations decide the next steps:

1. **Every route measures zero information in disguise.** The Toeplitz rank
   corresponds to a zero height. §2 shows the window size does too.
2. **Finite certificates cannot become cofinal.** The margins decay
   exponentially in C. §2 explains this decay.
3. **The trace/activation analysis is the most original material.** It has
   not produced a transfer theorem.

## 2. New measurements today

Reproduction: run the scripts from `experiments/prime_spectral/` with
python-flint 0.8.0. Outputs are in
`research/prime_spectral/directions_2026_10_12/`.

### 2.1 Twist fragility: positivity is not robust under prime phases

Replace `p^{-it}` by `e^{iθ_p} p^{-it}`, with `θ_{p^k}=kθ_p`, keeping the
archimedean and pole terms (`bohr_twist_probe.py`). At θ=0 the twisted
matrix agrees with `closed_weil.entry_closed` to `3·10⁻¹⁸⁰` (`check` mode).

- **Grids (N=24).** Every nonzero twist on a 5-point grid per prime gives a
  negative form. The minima are −1.02 at C=3.2, −1.67 at C=4.5, and −2.54 at
  C=6.5. At θ=0 the values are +6.9e-9, +3.8e-15 and +4.2e-25.
- **One-prime sensitivity at C=6.5 (`bohr_twist_controls.py eps`).** Twisting
  only p=2 by ε gives `λ_min ≈ −a·ε`, with `a` between 0.97 (ε=0.1) and
  0.48 (ε=10⁻¹⁴). Positivity therefore survives only for |ε| ≲ 10⁻²³. The
  mechanism is the near-degenerate lowest pair (4e-25, 6e-22): an
  antisymmetric twist couples the two states at first order.
- **Pole-free control.** Dropping the pole term gives λ_min = −3.99 at θ=0.
  Positivity depends on an exact cancellation between the pole and the prime
  sum.

**Consequence.** An argument that tolerates operator-norm errors of size η
cannot prove positivity at window C unless η ≲ λ_min(C). This holds even
for structured perturbations of a single prime phase. Coupling budgets,
comb-norm bounds and scalar Cauchy budgets are excluded at scale. The
repository had seen this informally; here it is quantified. A cofinal
argument must be an **exact identity**: the explicit formula and
self-duality, used without loss.

### 2.2 A Weyl law for the window form: ⌊2C − 7/4⌋ near-null directions

Count the eigenvalues of the window-C form below 0.3 (N=56, 1400 bits,
`window_near_null_counts.py`):

| C | 2 | 3 | 3.5 | 4 | 5 | 5.5 | 6 | 7 | 8 | 9.5 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| count | 2 | 4 | 5 | 6 | 8 | 9 | 10 | 12 | 14 | 17 | 20 | 22 |
| ⌊2C−7/4⌋ | 2 | 4 | 5 | 6 | 8 | 9 | 10 | 12 | 14 | 17 | 20 | 22 |

All 12 agree. Galerkin counts are lower bounds by min–max, and every one
already equals the prediction.

**Correction (same day, after the D1–D6 follow-up).** The agreement above
is a sampling coincidence. **⌊2C − 7/4⌋ is not an exact staircase.**
Re-checking the 141-window sweep below gives 70 mismatches out of 282
(C, threshold) pairs. Each mismatch lies within about 0.15 of an onset:
at threshold 0.3 the count is one higher just before
`C = (n+7/4)/2`, and at threshold 0.1 it is one lower just after. For
example, C=2.3 has 3 eigenvalues below 0.3, while ⌊2C−7/4⌋ = 2. What
survives is the ½ spacing (slope 2) with a threshold-dependent offset.
The certified follow-up result N₃(0.1)=4 agrees with ⌊2·3−7/4⌋ = 4. The "5"
it was compared against is the `+1` cluster size in D1 below, which was my
error, not the count law.

A finer sweep (141 windows, C=2 to 9, N=32,
`window_weyl_count_sweep.py`) shows two things:

- A new eigenvalue drops below 0.3 every **ΔC = 0.5045**, a slope of 1.98
  per unit C.
- The onsets sit at `(n+7/4)/2 − 0.12 ± 0.05`. The offset depends on the
  threshold, but within one threshold it is stable.

Above the near-null cluster the spectrum has a fixed plunge profile
(~1e-4, ~3e-3, ~0.1, then a bulk at 0.4–1).

**Heuristic derivation.** Assume RH. Then `Q(f)=Σ_γ|F(γ)|²`, with
F ∈ PW_{L/2} and L = log C. Landau–Pollak gives about `LT/π` degrees of
freedom concentrated in `[−T,T]`. There are `2N(T)` zeros there, with
`N(T)=(T/2π)log(T/2πe)+7/8`. The excess `(T/π)(L−log(T/2πe)) − 7/4` is
largest at `T=2πC`, where it equals **`2C − 7/4`**. The window "sees" zeros
up to height about 2πC; above that the zeros oversample. The −7/4 is twice
the 7/8 in Riemann–von Mangoldt.

**Direct confirmation (`ground_state_zero_sampling.py`).** The Fourier
transform of the ground state is about 1e-18 to 1e-28 at each of the 16
lowest zeta zeros. At the midpoints between consecutive zeros it is 1e-3 to
1e-9. Data: C=6.5 (2πC ≈ 40.8) and C=9.5 (2πC ≈ 59.7).

**Prior art.** The ground-state/zeros phenomenon is essentially
Connes–Consani–Moscovici's observation (prolate/Weil-form eigenvectors whose
transforms reproduce low zeta zeros). The "absorption" count with the 7/8
term goes back to Connes (Selecta 1999), via semiclassical counting.
**[check]** whether the window-form count ⌊2C−7/4⌋ and its exact ½ spacing
are stated anywhere. If not, the counting law and its use in §3 are the
candidate contribution.

This also explains the margin law: λ_min is the energy of the deepest of
about 2C functions forced to nearly vanish on the zeros below 2πC.

## 3. Directions, ranked by value per unit effort

### D1. Certify the near-null cluster as one block (Priority A engineering)

The [forward plan](RH_FORWARD_PLAN_2026_10_07.md) proposes Temple–Kato with
a lower bound μ on the **second** eigenvalue. §2.2 shows why that stalls.
There are about 2C−7/4 eigenvalues inside a geometric ladder with ratios
of 10³ to 10⁴, so λ₂ is as hard as λ₁.

**Change of target.** Take the cluster dimension as the number of
eigenvalues below a fixed separator, certified by interval inertia. §2.2
predicts it as about 2C plus a threshold-dependent offset. (The original
`⌊2C − 7/4⌋ + 1` was one too many. At C=3 it pulls λ₄ ≈ 0.688 into the
block, as the follow-up certificate showed.) Apply Lehmann–Goerisch or Temple to the **first eigenvalue
above the cluster**: the plunge level, about 1e-4 to 0.1. It is well
separated and certifiable with modest rank. Then certify positivity of the
n_C-dimensional compression exactly, in the prolate-adapted basis
(Rump-style LDLᵀ in balls).

- **Kill criterion:** the coupling between the cluster and its complement
  exceeds the plunge gap.
- **First run:** C = 6.5 (about 11 levels below 0.3), then C = 9.5 (about 17).
- **Context:** this is standard block eigenvalue inclusion. Its value is
  that it turns an exponentially ill-conditioned scalar problem into a
  well-conditioned block problem of predictable size.

### D2. An unconditional Weyl law for the Weil window form

**Target theorem.** For each fixed ε in the gap (say 0.3):

```
#{eigenvalues of A_C below ε} = 2C + c(ε) + o(1)   as C → ∞,
```

proved from the **prime side**, without RH, by semiclassical
(Landau–Widom/Szegő) counting for the symbol `Ψ_C(t)` on `[0, log C]`.
The constant should come out as `−7/4 + (plunge correction)`.

Why it matters: an off-line zero does not change the count. It changes the
sign of members of the cluster, by the Krein–Langer index. Combined with D3,
the count fixes how many sign-indefinite directions an off-line zero can
create inside a window. The archimedean part is a log-type symbol whose
counting is classical. The prime comb needs a trace estimate for
`tr f(A_C)` at mesoscopic scale, with the explicit formula as the
consistency check.

**[check]** Connes 1999, Connes–Consani 2021 (archimedean place), Suzuki
2606.09096, and Kim et al. 2607.24830 before claiming it.

### D3. Exchange rate: window positivity ⇒ an explicit zero-free region

**Target theorem.**

```
Weil positivity on all windows ≤ C  ⇒  every zero has β ≤ 1/2 + Φ(γ)/log C.
```

The test function is a modulated two-endpoint profile
`f = e^{iγ₀x}(1_{right end} − 1_{left end})`. An off-line pair contributes
`≈ −e^{bL}/(stuff)`, with b = β − ½. The on-line zeros contribute about
`log γ₀`. Nearby off-line zeros could cancel. Turán's second main theorem on
power sums, applied over a range of L, prevents that and gives
`Φ(γ) ≍ log γ · log log γ`. An isolated zero would allow `Φ ≍ log log γ`.

- **Outputs:** a calibrated exchange rate. Certified C converts to a
  zero-free region. Conversely, D2 plus Platt–Trudgian bounds how much a
  window certificate can ever add beyond zero verification. Expect the
  verdict to be "nothing at feasible C". Proving that rigorously is still
  publishable.
- **Calibration (D4):** the Davenport–Heilbronn function, whose lowest
  known off-line zero is near 0.8085 + 85.70i **[check the digits]**. The
  heuristic predicts its window form turns indefinite around C ~ 10² (an
  isolated zero, b ≈ 0.31).
- **[check]** Bombieri (2000, "Remarks on Weil's quadratic functional"),
  Yoshida 1992, Burnol's Sonine-space papers, Suzuki's screw-function
  papers. A statement of this type may exist.

### D4. Euler-product control harness (falsification gate for every open Prop)

Any lemma that also holds for an L-function with the same Gamma factor but
off-line zeros cannot be the missing ingredient. Build one harness that
evaluates every named open input on:

- (a) ζ;
- (b) a Dirichlet L-function with a matching Gamma factor;
- (c) Davenport–Heilbronn.

The inputs to test are the strict ladder rungs,
`KernelEffectiveCertificates`, the cofinal window bounds, the
trace/activation law, and the Weyl law. First two runs:

1. **Toeplitz.** Compute Ξ_DH Taylor coefficients at the center. Find the
   first contiguous minor that turns negative, as (rank, shift). Compare
   with the sector-theorem guarantee from the steepest off-line folded zero
   (angle ≈ 2·atan(0.3085/85.70) ≈ 0.0072, so PF up to about 435 if that
   zero is the steepest). Michałowski's large-shift positivity holds for
   both functions, so failure must sit at moderate shift. This measures
   whether rank is a sharp or a weak detector of off-line zeros. That
   question decides whether the strict-ladder program carries any
   information beyond zero verification.
2. **Window.** Build the DH Weil form: coefficients of −f′/f, which are not
   supported on prime powers, plus its archimedean factor. Find the C at
   which it first turns indefinite. This calibrates D3.

### D5. A "no robust proof" theorem (makes §2.1 rigorous)

**Statement.** For each C ≥ C₀ there is a Hermitian perturbation P of the
window form with operator norm ‖P‖ ≤ K·λ_min(C) that makes it indefinite;
a one-prime phase twist suffices. Rigorous version: a certified two-level
reduction at C = 3.2 or 4.5. The ingredients are the certified near-null
pair, its gap, and an interval enclosure of the antisymmetric coupling
`⟨u₀, i(T−T*)u₁⟩`.

This converts the repository's informal "do not use scalar budgets" rule
into a theorem. Any proof of window positivity must be exact to relative
precision λ_min, and so must go through an identity. It is cheap, uses
existing certified machinery, and is a clean short note. **[check]**
Weil-twist literature for prior statements.

### D6. Speculative: one-vector-at-a-time induction on the cluster

§2.2 shows the near-null cluster gains **exactly one direction per ΔC = ½**.
That is the cleanest scale-indexed structure seen in this program. An
inductive approach would show that each entering direction keeps the
compressed form positive.

The Schur complement of the new direction is its plunge energy (~0.1)
minus `|coupling|²` over cluster eigenvalues as small as 1e-70. D5 says
couplings are O(1). The induction step therefore cannot be perturbative. It
would need an exact identity for the entering direction's Schur complement,
for example one expressing it through the next zero or the next prime power.

- **First test (cheap):** in the 141-window sweep data, check whether the
  entering eigenvalue's Schur complement against the existing cluster
  stays O(1) while the cluster's own eigenvalues collapse.
- **Kill criterion:** if it does not, drop D6.

This is the only direction here that aims at RH itself. Expect it to fail;
it is listed because the structure is new.

## 4. Stop / deprioritize (additions to the forward plan's §4)

- Temple–Kato with a second-eigenvalue μ at C ≳ 3. Replace it with D1.
- Trace-transfer trials that preserve the saved bulk and repair only the
  endpoints. Certified failed (2026-10-07).
- Any new positivity argument that is not exact to relative precision
  λ_min(C). D5 rules these out.
- Paper drafting on trace activation until D4 shows that the δ/log(1/δ)
  law behaves differently for Davenport–Heilbronn and for ζ. If it is the
  same for both, it is archimedean, not arithmetic.

## 5. Next actions (concrete, in order)

1. **D5 at C=3.2:** certify the two-level twist reduction with existing Arb
   code. This is a short note.
2. **D1 at C=6.5:** certify the plunge-level eigenvalue and an exact 12×12
   cluster compression. Compare cost with the current single-vector
   approach.
3. **D4.1:** compute Ξ_DH coefficients and run the Toeplitz first-failure
   scan.
4. **D2/D3:** run the prior-art checks marked above, then write the
   heuristic derivation of 2C − 7/4 as a lemma-level outline. The first
   rigorous target is the archimedean-only count.
