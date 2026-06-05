# Three Bold Structures for Fully Solving RH

**Date:** 2026-06-05
**Status:** research program design (not proofs). Each structure names the precise
*new* mathematical object/theorem it must create, what verified result it builds on,
why it escapes the back-calculation trap, and a concrete first formalizable step.

---

## The constraint every structure must respect

We proved (machine-checked):
- `riemannHypothesis_iff_zeroImUniqueness` (RH ≡ "≤ 1 zero per imaginary height"), and
- the **back-calculation lemma**: any *faithful sufficient* condition for the gap is
  logically equivalent to RH.

**Consequence.** A winning structure cannot be a reformulation of the zero set alone
— that is always ≡ RH and circular. It must import a **genuinely external handle**:
an object with *its own independent theory and tools* (combinatorics of polynomial
real-rootedness, PDE/dynamics, operator metrics) that is provably tied to the zeros
yet provable *by methods foreign to the zeros themselves*. All three below do this.

What we have that is unusually powerful as a launch pad:
- **Z-function realness** (`completedRiemannZeta₀_real_on_critical_line`): `Λ₀` is
  **real** on the critical line. This is the single most leverage-giving verified fact
  — it makes the critical-line slice a genuine real-analytic real function with real
  Taylor coefficients.
- **Dihedral symmetry of `Λ₀, Λ₀′`** (reflection × conjugation), `Re Λ₀′ = 0` on line.
- **Energy/centroid calculus**: per height, centroid `= 1/2` unconditional; RH ⟺ all
  fiber energies (second moments) vanish; spectral-gap lower bound on any off-line
  energy.
- **HP sufficiency** (polymorphic in `E`) + finite faithful converse + `spectralParam`.
- **Hardy sign-change counting** on the real Z-slice.

---

## STRUCTURE A — Laguerre–Pólya / Jensen-Hyperbolicity Closure  ⭐ (most concrete)

### Core idea
Let `Ξ(z) := Λ₀(1/2 + iz)` (a renormalization of the Riemann ξ). By **our verified
realness**, `Ξ(z)` is *real for real `z`*; by the functional equation it is *even*.
Hence
  `Ξ(z) = ∑_{n≥0} b_n z^{2n}` with **all `b_n ∈ ℝ`** (real, well-defined).
RH ⟺ all zeros of `Ξ` are real ⟺ `Ξ` lies in the **Laguerre–Pólya class** (Pólya).

The Pólya–Jensen criterion turns this into combinatorics: for the sequence `(b_n)`,
form the **Jensen polynomials**
  `J^{d,n}(X) = ∑_{j=0}^{d} \binom{d}{j} \frac{b_{n+j}}{b_n} X^j` (suitably normalized).
Then `Ξ ∈ LP ⟺ every J^{d,n} is hyperbolic (all real roots)`. So:

  **RH ⟺ every Jensen polynomial of `(b_n)` is real-rooted.**

### What it builds on (verified here)
`completedRiemannZeta₀_real_on_critical_line` is *exactly* what makes the `b_n` real,
so the whole real-rootedness machinery is even applicable. (Without realness, `b_n`
are complex and the LP/Jensen criterion is meaningless.)

### Why non-circular
Real-rootedness of an explicit polynomial sequence is attackable by **independent
tools**: discriminants, Newton/Turán inequalities, Hermite–Biehler, asymptotics of
the `b_n`. This is *not* about the zeros directly — it is about combinatorial
positivity of derivatives/coefficients. Crucially, large parts are **already proven
unconditionally**:
- Csordas–Norfolk–Varga (1986): the **Turán inequalities** `b_n² ≥ b_{n-1}b_{n+1}`
  (the `d=2`, all-`n` case) hold unconditionally.
- Griffin–Ono–Rolen–Zagier (2019): for **each fixed `d`**, `J^{d,n}` is hyperbolic
  for **all but finitely many `n`** (unconditional), via Hermite-matrix positivity and
  the asymptotics `b_n ∼ ...` of the ξ-coefficients.

### The genuinely new mathematics required
Upgrade "**eventually** hyperbolic (per degree)" to "**always** hyperbolic (all `n`,
all `d`)". Concretely: a *uniform* hyperbolicity theorem controlling the finitely many
exceptional `n` for every `d` simultaneously — e.g. an effective lower bound on the
discriminant of `J^{d,n}` valid for all `n`, or a monotone "hyperbolicity margin" that
is positive for small `n` and matches the GORZ asymptotic regime. This is the crux and
is open.

### First formalizable step (buildable now)
1. Define `Ξ : ℝ → ℝ`, `Ξ t = (Λ₀(1/2 + t·I)).re`; prove real-analytic & even (we have
   realness + reflection).
2. Define `b : ℕ → ℝ` via `iteratedDeriv`; prove `b n` real (immediate) and the
   even-function vanishing of odd derivatives.
3. Define `JensenPoly d n : Polynomial ℝ`; state
   `RH ↔ ∀ d n, (JensenPoly d n).roots are all real` (the Pólya–Jensen equivalence).
4. Port Turán `d=2` as the first verified unconditional fragment.

**Assessment:** highest payoff-to-tractability. Our realness theorem is the key, and
the literature already supplies half the ladder. The new math is a *uniformization* —
hard but concrete, with a clear formalization runway.

---

## STRUCTURE B — Heat-Flow Energy Rigidity (de Bruijn–Newman dynamics)

### Core idea
Deform `Ξ` by the backward heat flow: `H_t` with `H_0 = Ξ`, giving the de Bruijn–
Newman constant `Λ_{dBN}` (threshold for all-real zeros). Known: RH ⟺ `Λ_{dBN} ≤ 0`;
**Rodgers–Tao (2018): `Λ_{dBN} ≥ 0`**. So **RH ⟺ `Λ_{dBN} = 0`** — a knife-edge.

Bold move: treat the zeros `ρ_k(t)` as interacting particles (they obey a real
gradient/repulsion dynamics in `t`). Define the **off-line energy**
  `E(t) = ∑_k (Re ρ_k(t) − 1/2)²` (regularized via our fiber-energy functional).
Prove `E` is a strict **Lyapunov functional**: monotone under the flow with the
critical-line configuration as the *unique* fixed point and global attractor.

### What it builds on (verified here)
Our `fiberEnergy` and the **unconditional centroid = 1/2** (first moment already
pinned) give the natural order parameter `E`; `riemannHypothesis_iff_forall_fiberEnergy_zero`
makes "`E ≡ 0`" literally RH; the spectral-gap bound quantifies deviations.

### Why non-circular
The handle is **dynamics/PDE**: monotonicity of a Lyapunov functional under heat flow
is proven by differential inequalities (entropy/energy dissipation), tools entirely
outside zero-counting. Rodgers–Tao already supply the matching inequality `Λ ≥ 0` by
such methods; the structure seeks the dual `Λ ≤ 0` via energy contraction.

### The genuinely new mathematics required
A **strictly dissipative, bounded-below Lyapunov functional** for the zero dynamics
whose only stationary configuration is "all on the line", with enough regularity to
conclude `Λ_{dBN} ≤ 0`. Open; the regularization and the strict monotonicity at the
threshold are the crux.

### First formalizable step
Formalize the deformation `H_t` and the *definition* of `Λ_{dBN}`, and re-express
`Λ_{dBN} = 0 ↔ RH` in our energy language (`E ≡ 0`). (Heavy: needs the heat kernel on
`ξ`, not yet in Mathlib.)

**Assessment:** physically principled, ties to a celebrated half-result (`Λ ≥ 0`).
Heavier formalization runway; the crux is a genuine analysis theorem.

---

## STRUCTURE C — Pseudo-Hermitian / PT-Symmetric Realization (Bender–Brody–Müller × our involution)

### Core idea
Hilbert–Pólya fails naively because the diagonal operator is unbounded/non-total. Drop
*Hermiticity* and keep a weaker symmetry: seek `H` with spectrum `{γ_k}` that is
**pseudo-Hermitian** — `η H η⁻¹ = H†` for a positive metric `η` (Mostafazadeh) — or
equivalently **PT-symmetric** with unbroken PT (Bender–Brody–Müller, PRL 2017, proposed
a concrete `H = (xp+px)/2` conjugated by `(1−e^{−ip})`). Then:

  **RH ⟺ the metric `η` is positive-definite (PT unbroken ⟺ real spectrum).**

Use **our `zetaInvolution` `s ↦ 1 − s̄`** as the geometric PT operator: we proved it is
an involution, preserves the strip, and **its fixed-point set is exactly the critical
line**. Combined with our **conjugate symmetry** and **`symmetric ⇒ real eigenvalue`**,
the structure is: realize the zeros as a `(H, J)`-spectrum where `J = zetaInvolution`,
and show `J`-compatibility + a positive metric forces eigenvalues onto `Fix(J)` = the
line.

### What it builds on (verified here)
`zetaInvolution_fixed_iff_onCriticalLine`, `zetaInvolution_involutive`,
`zetaInvolution_preserves_strip`; `symmetric_eigenvalue_conj_eq`;
`riemannHypothesis_of_symmetric_eigendata` (polymorphic) and the finite faithful
converse; `spectralParam` encoding (`μ(s)` real ⟺ on line).

### Why non-circular
The handle is **operator theory + a positivity (metric) condition**, with tools
(quadratic forms, self-adjoint extensions, similarity to self-adjoint) independent of
the zeros. PT-symmetry's "unbroken ⟺ real spectrum" is a theorem about operators, not
a restatement of RH — the content is constructing `H` and proving `η > 0`.

### The genuinely new mathematics required
(i) A rigorous quantization of the BBM symbol as a self-adjoint operator on a concrete
rigged Hilbert space with eigenvalues provably `{γ_k}`; (ii) construction of the metric
`η` and proof of its positivity. Both open (BBM gave only a formal/heuristic argument).

### First formalizable step
Generalize our `HilbertPolyaWitness'` to a **pseudo-Hermitian witness** `(E, η, H)` with
`η` positive and `H` `η`-self-adjoint, and prove `η`-self-adjoint ⇒ real eigenvalues
(an `η`-inner-product version of `symmetric_eigenvalue_conj_eq` — directly adaptable).
Then `pseudoHermitianWitness → RH`. This is *immediately* formalizable from our existing
proof, packaging the harder existence as the open input.

**Assessment:** boldest; ties to a real 2017 proposal and our involution. Existence is
open, but the *reduction* (pseudo-Hermitian witness ⇒ RH) is formalizable now and would
be a genuine new packaged theorem.

---

## Recommendation & honest verdict

- **Pursue A first.** It is the most concrete, rests squarely on our verified Z-realness,
  has an existing unconditional ladder (Turán + GORZ), and a clear Lean runway (define
  `Ξ`, real coefficients `b_n`, Jensen polynomials, the hyperbolicity equivalence, port
  Turán). The new mathematics — *uniform* hyperbolicity — is hard but well-posed.
- **C gives an immediate formalizable artifact** (the pseudo-Hermitian reduction
  theorem) even though existence stays open.
- **B is the deepest analytic bet**, anchored by Rodgers–Tao's `Λ ≥ 0`.

None of these is a proof, and by the back-calculation lemma none *can* be without the
named external theorem (uniform hyperbolicity / Lyapunov dissipation / metric
positivity). But each is a genuine, bold, non-circular *structure*, each with a verified
foothold from this development and a concrete first step.
