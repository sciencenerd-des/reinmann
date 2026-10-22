# Xi normalization and local eigenvector reduction

Status: active research objective; initial conditional reductions implemented on
2026-10-10. An arithmetic coefficient-domain candidate and its selected-state
masses are constructed below. No realization satisfying the full paired
mass-and-defect requirements, or proof of RH, is supplied.

The first construction milestone is documented in
[FOCK_CANDIDATE.md](FOCK_CANDIDATE.md): an Xi-defined coefficient domain,
an invariant differential action, and explicit zero states with finite mass.
This is a candidate rather than a symmetric realization. Its diagonal symmetry
obligation remains equivalent to RH, and the raw sequence carrier has not been
promoted to a fully formalized Hilbert-space operator domain.
The [analytic domain and mass argument](FOCK_DOMAIN_ESTIMATES.md) separately
establishes bounded arithmetic row functionals and a closed restricted operator
in Fock space. That written argument has not been formalized or independently
reviewed; it supplies neither symmetry nor density of the restricted domain.

The next [arithmetic divided-difference form](XI_DIVIDED_DIFFERENCE.md)
supplies a written bounded Hermitian form and symmetry on that same Xi
operator domain. Its kernel and actual-domain Jordan obstruction are checked
separately in Lean. Exact coherent-state non-isotropy for this form would
require both criticality and simplicity.
The [approximate packet mass construction](APPROXIMATE_PACKET_MASS.md) instead
uses higher jets to obtain absolute form mass one and vanishing ordinary
residuals at every Xi zero without those assumptions. That construction is a
written proof for the full Hilbert-space compatibility, without independent
review. Generic mass and residual bounds, a simple reflected-pair arithmetic
core, and all-order arithmetic jet and kernel-derivative lemmas are now checked
in Lean. The paired residual defect remains
exactly twice the distance from the critical line.

The [fixed algebraic jet construction](ALGEBRAIC_JET_MASS.md) now provides a
separate Lean-checked same-form mass bridge. It has unique finite coordinates
inside the actual coefficient space, the existing Xi row domain and restricted
arithmetic action, and one Hermitian form on all parameters and jet orders.
Every Xi zero has a nonzero actual-domain cross-pairing, explicit isotropic
packet mass bounds and a state of unit absolute mass. Action symmetry and the
relative paired budget for this algebraic form remain unproved.

## Candidate comparison matrix (as of 16 October 2026)

The five priorities are defined in the table under "Construction milestone and
remaining obligations" below. Key: **L** = Lean-checked (standard axioms only);
**W** = written argument, not formalized or independently reviewed; **✗** = fails
for this candidate; **open** = not established; **partial** = established only
in a restricted case.

| Candidate form (notes; Lean modules) | P1 action, space, domain | P2 state for every zero | P3 mass | P4 symmetry | P4 paired residual budget | P5 Xi identification |
| --- | --- | --- | --- | --- | --- | --- |
| Natural Fock pairing ([FOCK_CANDIDATE](FOCK_CANDIDATE.md); `FockEigenvectors`, `XiAnnihilator`) | L (row domain, invariance, membership); W (Hilbert domain) | L (unit-mass eigenstates) | L | ✗ (diagonal defect `2\|Re s-1/2\|`; cross-state symmetry fails) | ✗ (equivalent to RH for this pairing) | L (zero transfer) |
| Divided-difference form ([XI_DIVIDED_DIFFERENCE](XI_DIVIDED_DIFFERENCE.md); `XiDividedDifference`, `XiJordanDomain`) | L (same domain) | W (via approximate packets) | exact non-isotropy needs criticality and simplicity; approximate packets W, generic bounds L | W | open | L (kernel identities, Jordan obstruction) |
| Xi kernel packets ([APPROXIMATE_PACKET_MASS](APPROXIMATE_PACKET_MASS.md); `XiKernelPackets`) | L (injective realization intertwining the action) | partial (L for a hypothetical *simple* off-critical zero) | L (unit-mass packet for every residual tolerance) | open | open; the norm-product criterion is not necessary (`PseudoHermitianNormProductObstruction`) | W (Fock transfer and pairing compatibility) |
| Fixed algebraic jet form ([ALGEBRAIC_JET_MASS](ALGEBRAIC_JET_MASS.md); `XiAlgebraicJetSpace`, `XiAlgebraicJetForm`, `XiAlgebraicMass`) | L | L (every zero, all jet orders, no simplicity) | L (isotropic packet bounds, unit mass) | open | open (named `ArithmeticUnitMassPairedBudget`) | L (all-order reflection and conjugation; `XiHigherJet*`) |
| Green recurrence form ([GREEN_RECURRENCE_MODEL](GREEN_RECURRENCE_MODEL.md); `XiGreenGram`, `XiAlgebraicRows`, `XiGreenModel`) | L (same space, action and domain as the algebraic jet form) | L | L (same-form all-zero masses) | **L** (Green identity and actual-domain symmetry) | **open, and Lean-proved equivalent to RH** (`green_paired_budget_iff_riemannHypothesis`) | L (entries built from actual Xi derivatives) |

**Reading the matrix.** The Green recurrence form is the first candidate with
P1–P3 and P4 symmetry all Lean-checked for one fixed form. The only missing
acceptance condition is the arbitrarily small *relative paired residual
budget* at every zero. Lean proves that this budget is *equivalent* to RH
(`GreenUnitMassPairedBudget ↔ RiemannHypothesis`). The construction is
therefore a verified reformulation of RH, not a reduction to something weaker.
Any further progress must prove the budget by an argument that does not
already presuppose RH. The
Green modules are built by the root `Reinmann.lean` (full build of 3,560 jobs
on 16 October 2026; recorded source hashes unchanged since the 11 October
canonical checks). A fresh run of `green_model_axiom_audit.lean` on 17 October
2026 audits 48 theorems, all using only `propext`, `Classical.choice` and
`Quot.sound`.

## Finite formalization matrix (22 October 2026)

These auxiliary milestones do not discharge an open Green-form budget above.
All fourteen jobs passed at proof commit
`150537bf1d94eced1c22db7660f9c32936372831` in
[CI run 39470397281](https://github.com/sciencenerd-des/reinmann/actions/runs/39470397281):
main build/guard, shared dependencies, eleven tile shards, and final rectangle
assembly with explicit PF43 axiom checking. At that proof source, the default
guard had 2,608 rows; the optional rectangle has its own 1,700-declaration audit.
The current finite-width closeout passed all 34 jobs at `b4ec4a3` in
[run 39733278869](https://github.com/sciencenerd-des/reinmann/actions/runs/39733278869).
Its root guard covers 2,643 declarations; separate PF58 and PF97 audits cover
47,896 and 363,579 distinct implementation theorem constants, respectively.
See the [current closeout](../prime_spectral/PF97_CERTIFIED_2026_10_22.md) for
the exact checked source, public statements and audit scope.

| Milestone | Status | Remaining boundary |
| --- | --- | --- |
| Target A, entire-function split-pair extension | **L, proved** (`SplitPairMixedRows`, `AnalyticSplitPair`, `AnalyticToeplitzJacobi`) | Simple selected zeros and an isolated boundary-pair modulus tie; standalone, no PF-to-RH rewiring |
| Target B, actual-Xi low rectangle | **L, proved; CI verified** (`XiRectangle.rectangle_nonzero`, `XiRectangle.zetaNoLowStripZero`) | Closed `0 ≤ Re(s) ≤ 1`, `|Im(s)| ≤ 14.1`; higher finite-width boxes allow critical-line zeros |
| Actual folded-Xi canonical product and fixed-rank sector bridge | **L, proved; CI verified** (`XiHadamardProduct`) | Attributed PNT+ Hadamard backport discharges inverse-zero summability and normalized genus-zero identity, with multiplicities retained; the angle bound is still needed at each rank |
| Ordinary-coefficient PF43 | **L, unconditional; CI verified** (`XiFinitePFCertified.finitePF43`) | All ordered minors through rank 43 are nonnegative; no unbounded-rank or strict-positivity conclusion |
| PF58 | **L, unconditional; CI verified** (`XiFinitePFCertified.finitePF58`) | Width 3/8 through height 19; all 17 jobs of [run 39730502820](https://github.com/sciencenerd-des/reinmann/actions/runs/39730502820) passed at `1d97a06`; no external seven-eighths input |
| PF97 finite-width extension | **L, unconditional; CI verified** (`XiFinitePFCertified.finitePF97`) | Width 9/40 through height 32; all 67 tiles and final assembly checked by all 34 jobs of [run 39733278869](https://github.com/sciencenerd-des/reinmann/actions/runs/39733278869) at `b4ec4a3`; critical-line zeros allowed |

[Current product/sector scope report](../prime_spectral/PNT_HADAMARD_BACKPORT_2026_10_20.md).
The root CI coverage now supersedes that report's dated local-only coverage
paragraph. The [DH gate](../RH_DH_DISCRIMINATOR_REGISTER.md) retains the missing
arithmetic discriminator for the RH-equivalent Green budget.

The dated sections below are kept as the historical validation record.

Branch: `codex/xi-eigenvector-reduction`.
Base: `f62bb7f7d32f572d5d92300693b3ca4962ce942b`.
The managed worktree contains a hash-recorded copy of the current manuscript
revision; see [worktree_seed.json](worktree_seed.json). Other uncommitted research
files from the original checkout were not copied.

## Objective and three strands

> We distinguish ordinary coefficients µn from the classical Jensen coefficients
> n!µn, explain why Mathlib's entire pole-subtracted completed zeta is not itself
> the correct zero-set target, and record a separate pseudo-Hermitian eigenvector
> reduction.

1. Preserve the distinction between ordinary coefficients `μₙ` of the folded Xi
   series and classical Jensen coefficients `γₙ = n! μₙ`. Results for the
   diagnostic polynomials formed directly from `μₙ` cannot be substituted for
   the classical Jensen criterion without a bridge.
2. Use the entire Xi extension
   `xiCompleted(s) = 1/2 + s(s-1) completedRiemannZeta₀(s)/2`.
   At a nontrivial zeta zero `ρ`, the pole-subtracted completed zeta instead has
   value `1/ρ + 1/(1-ρ)`, which is nonzero. Its zeros are not the desired target.
   The seed manuscript states the established zero-set transfer and remaining
   analytic identification obligations.
3. Improve the operator reduction by minimizing assumptions, exposing domains,
   and replacing exact identities by rigorously controlled relative defects.
   Then seek an arithmetic construction that satisfies these hypotheses without
   assuming zero reality, RH, or an equivalent positivity statement as input.

## Initial formal improvement

The old `PseudoHermitianForm` asks for `η(v,v) ≠ 0` for every nonzero vector.
This is diagonal anisotropy, stronger than ordinary nondegeneracy. Its fields
contain scalar homogeneity, but neither additivity nor Hermitian symmetry.

The new [PseudoHermitianLocal.lean](../../Reinmann/PseudoHermitianLocal.lean)
needs only scalar homogeneity and, at each selected zero state, diagonal
symmetry and nonzero mass. States lie in a separate domain `D`; a specialization
accepts a linear operator `T : D →ₗ[ℂ] E` for a submodule `D` of `E`. It does not
require an everywhere-defined extension or a positive form on unrelated states.
The old global interface is proved to supply this weaker interface.

Write `λ(s) = -i(s-1/2)`, `q = η(v,v)` and
`d(v,w) = η(w,v) - η(v,w)`. For an exact eigenpair `w = λ(s)v`, Lean proves

```text
d(v,w) = (λ(s) - conjugate(λ(s))) q
2 |Re(s)-1/2| |q| = |d(v,w)|.
```

Additivity permits a residual `w = λ(s)v + r` and gives

```text
(λ(s) - conjugate(λ(s))) q = d(v,w) - d(v,r).
|d(v,w)| + |d(v,r)| ≤ 2 ε |q|,  q ≠ 0
    implies |Re(s)-1/2| ≤ ε.
```

The approximate RH reduction asks for such a state for each critical-strip
zero and every positive `ε`. It needs no uniformity over zeros and no convergence
of the states to an exact eigenvector. It still needs a single fixed form and
action, with the budgets established for all those states and tolerances.
Absolute residual smallness alone is insufficient if the diagonal mass collapses.

[PseudoHermitianIsotropy.lean](../../Reinmann/PseudoHermitianIsotropy.lean)
checks the obstruction in `ℂ²`: the nondegenerate indefinite form
`η(x,y)=x₁ conjugate(y₂)+x₂ conjugate(y₁)` makes `diag(i,-i)` symmetric, yet
the nonzero state `(1,0)` has eigenvalue `i` and zero diagonal mass. Ordinary
nondegeneracy therefore cannot replace the selected-state non-isotropy condition.

## Construction milestone and remaining obligations

The coefficient candidate now defines the state domain by convergent rows of
`ξ(A)`, independently of a supplied list of zeros. Lean checks its invariance,
the exact membership criterion `v_s ∈ D_ξ iff ξ(s)=0`, and unit-mass eigenstates
for every critical-strip zeta zero. The natural pairing still lacks the needed
symmetry: its normalized diagonal defect has norm `2 |Re(s)-1/2|`.

| Priority | Deliverable | Acceptance condition |
| --- | --- | --- |
| 1 | An arithmetic action, ambient space and explicit domain | Define these independently of an assumed real zero set; check domain membership and each operation used in the form identity. |
| 2 | A zero-to-state construction | Obtain nonzero states or approximate states for every critical-strip zero; a finite height sample is insufficient. |
| 3 | A mass estimate | Prove non-isotropy at exact states, or a lower bound sufficient for relative defect control at approximate states. |
| 4 | Form symmetry and paired residual estimates | Bound both `d(v,w)` and `d(v,r)` relative to `|q|`, to arbitrarily small positive tolerance for each zero. |
| 5 | Connection with Xi and coefficients | Prove all needed function and coefficient identifications with the corrected normalization and zero-set target. |

For this candidate, priorities 1–3 and the zero transfer in 5 have coefficient
proofs; the written Hilbert-space analysis supplies additional domain estimates.
Priority 4 remains open. The pairing also fails cross-state symmetry for
distinct critical-line coherent states. A future globally symmetric realization
therefore requires a change to the form or operator, beyond this candidate's
selected-state diagonal criterion.

The divided-difference candidate makes that change of form explicitly. Its
written Hilbert construction supplies symmetry, and its written approximate
packet argument supplies nonzero masses for the same form and action. The
remaining priority-4 requirement is an independent paired residual estimate
at every zero, to arbitrarily small positive relative tolerance. Small ordinary
residuals do not meet it. The Fock unit-mass estimate and divided-difference
symmetry must never be combined as though they concerned one form.

The checked first-jet domain theorem also shows why imposing global symmetry
and exact non-isotropy on the full Xi differentiation domain would additionally
exclude multiple zeros. The approximate reduction accommodates multiplicities;
assuming simplicity would unnecessarily strengthen the original RH objective.

The packet milestone improves the estimates without changing their form:
for `B=η(v,w)≠0`, `η(v,v)=0` and `C=η(w,w)` real, Lean checks

```text
x_h=v+h B w,                 0<h≤1/(1+|C|),
h|B|² ≤ η(x_h,x_h) ≤ 3h|B|²,
η(ψ_h,ψ_h)=1,               ψ_h=x_h/sqrt(η(x_h,x_h)),
||(T-λ)ψ_h||≤sqrt(h)||(T-λ)w||.
```

`XiKernelPackets` checks the actual Xi kernel Gram form on two coherent
states and an injective realization into the existing coefficient domain,
intertwining its independently defined differential action. For a hypothetical
simple off-critical zero, it supplies the nonzero cross pairing `iξ'(s)`
and a unit-mass packet for every ordinary residual tolerance. Its formal norm
is a coordinate norm; the Fock transfer and pairing compatibility remain
analytic obligations. This core does not replace the full Hilbert construction
or restrict the objective to simple zeros.

For a form bounded by `K||x|| ||y||`, Lean additionally checks
`|Re(s)-1/2|≤K||x|| ||(T-λ(s))x||` at absolute mass one and diagonal
form symmetry. Making that product arbitrarily small would suffice for local
criticality. The isotropic packet construction alone cannot establish this
estimate off the line, even though its ordinary residual tends to zero.
This is an optional sufficient criterion, not the required acceptance condition.
A checked real Jordan example has unit mass and zero paired defect with
arbitrarily small ordinary residual, while every unit-mass state's norm product
is at least `1/2`. The research objective therefore retains the weaker paired
budget and all multiplicities; it does not require this stronger norm criterion.

The [higher-jet mass bridge](HIGHER_JET_MASS_BRIDGE.md) now checks arbitrary
coefficient jets in the actual Xi domain, their Jordan action, all-order Xi
reflection and conjugation, finite multiplicity at every zero, and the nonzero
kernel derivative `i(-1)^(m+1)ξ⁽ᵐ⁾(ρ)/m`. The remaining formal bridge identifies
that derivative with the full Fock-space form value. These results neither
assume simplicity nor establish the independent paired residual budget.

Start with a tractable arithmetic candidate and test the mass estimate early.
A formal construction that merely assigns `λ(s)` to a basis indexed by zeros
does not establish non-isotropy or symmetry independently; the missing RH content
can be hidden in those hypotheses. A metric obtained by assuming a real spectrum
also cannot be used to prove that spectrum real.

For an unbounded Hilbert-space realization, any claims about self-adjointness,
similarity, resolvents or the full spectrum need additional domain and analytic
proofs. The present Lean results concern selected eigenpairs and do not assert
these stronger properties. Numerical matrix experiments are candidate diagnostics,
not certification of the infinite operator or all zeros.

## Prior art and contribution scope

The non-isotropy mechanism is classical: Mostafazadeh's
[Pseudo-Hermiticity versus PT Symmetry, Proposition 2](https://arxiv.org/pdf/math-ph/0107001)
states that a nonreal eigenvalue forces its eigenvector to have zero metric norm.
Our contribution at this stage is a checked weaker interface, explicit residual
budgets, and a checked scope counterexample. No mathematical novelty is claimed;
a dedicated wider prior-art audit remains required before any novelty claim.

For infinite-dimensional metric claims, see Krejčiřík, Siegl, Tater and Viola,
[Pseudospectra in non-Hermitian quantum mechanics](https://arxiv.org/html/1402.1082),
especially Propositions 2 and 4 on bounded invertible metrics, similarity and
Riesz bases. These results motivate explicit analytic hypotheses; they do not
provide an arithmetic operator for this project.

## Reproduction and next handoff

```sh
lake build Reinmann.PseudoHermitianLocal Reinmann.PseudoHermitianIsotropy
bash scripts/safe-verify.sh research/pseudo_hermitian/axiom_audit.lean
lake build Reinmann.FockEigenvectors Reinmann.XiAnnihilator
bash scripts/safe-verify.sh research/pseudo_hermitian/construction_axiom_audit.lean
python3 research/pseudo_hermitian/check_fock_candidate.py
lake build Reinmann.XiDividedDifference Reinmann.PseudoHermitianJordan Reinmann.XiJordanDomain
bash scripts/safe-verify.sh research/pseudo_hermitian/symmetry_mass_axiom_audit.lean
lake build Reinmann.XiKernelPackets
bash scripts/safe-verify.sh research/pseudo_hermitian/packet_mass_axiom_audit.lean
lake build Reinmann.XiHigherJetCoupling Reinmann.PseudoHermitianNormProductObstruction
bash scripts/safe-verify.sh research/pseudo_hermitian/higher_jet_axiom_audit.lean
lake build Reinmann.XiAlgebraicMass
bash scripts/safe-verify.sh research/pseudo_hermitian/algebraic_mass_axiom_audit.lean
```

The companion validation record and saved logs give the exact toolchain, source
hashes and theorem-axiom results for this milestone. The copied manuscript PDF
predates this operator extension and has not been represented as incorporating it.
The construction milestone has a separate
[dated validation record](construction_validation_2026_10_10.json): the full
3,535-job build passed, the shortcut scan covered 98 project Lean files, and
all 27 construction theorem audits use only `propext`, `Classical.choice` and
`Quot.sound`. The original
`validation.json` remains the record of the earlier conditional reduction.
The [form validation record](form_validation_2026_10_10.json) records the newer
kernel and actual-domain Jordan milestone, separately from the written Hilbert
and general packet arguments. The full 3,538-job build passed, the shortcut
scan covered 101 project Lean files, and the 28 new theorem audits contain
only standard Lean axioms. Six exact synthetic polynomial packets passed
independent algebra checks; these are not Xi-zero certificates.
The [packet mass validation record](packet_mass_validation_2026_10_10.json)
records the later generic mass bounds, norm-product criterion and checked Xi
packet realization. The full 3,541-job build passed, the shortcut scan covered
104 project Lean files, and all 25 new theorem audits use only standard Lean
axioms. The earlier records are retained as historical snapshots.
The [higher-jet validation record](higher_jet_validation_2026_10_10.json)
records the all-order arithmetic domain and kernel-derivative milestone, with
the full 3,544-job build, 107 project files scanned and 42 new theorem audits
using only standard Lean axioms. It also records the checked real Jordan
counterexample to treating the stronger norm-product criterion as necessary.
The [algebraic mass validation record](algebraic_mass_validation_2026_10_10.json)
records the fixed algebraic space/form/action/domain and actual all-zero mass
milestone: the full 3,548-job build, 110 project files scanned and 35 theorem
audits using only standard Lean axioms. The conditional RH endpoint names the
still-unproved `ArithmeticUnitMassPairedBudget`; no instance is asserted.
The original 14 manuscript seed files remain unchanged in both checkouts.
Continue by checking the arithmetic Green identity for this algebraic form and
proving the missing paired defect bound, while retaining
the explicit operator domain and the mass estimate for the same form.
Preserve the full objective: a valid arithmetic realization and the mass
estimates it needs, not merely the existence of a nonsymmetric eigenvector model.

## Green recurrence verification (completed 2026-10-11; historical notes)

The [universal Green recurrence implementation](GREEN_RECURRENCE_MODEL.md)
now defines a second fixed arithmetic Gram form on the same all-parameter jet
space, coefficient action and Xi row domain. Its proposed Green and row proofs
seek action symmetry, with masses re-established for that same form. The
combined Lean check now passes all 48 theorem audits using only standard axioms,
including symmetry and all-zero mass estimates. Separate canonical module
builds, the full project build and the canonical-import audit are still pending,
so the preceding algebraic mass record remains the latest fully built milestone.

An independent exact diagnostic passed 288 recurrence-versus-kernel comparisons
and both nonzero-boundary finite Green identities for synthetic polynomials.
These are neither Xi certificates nor general formal proofs. The
[working tracker](green_working_state_2026_10_10.json) records live compiler
handles, the guarded sequential resumption and the pending 48 theorem audits.
The arbitrarily small relative paired budget remains an explicit requirement.
The isolated worktree still retains its 14-file manuscript seed; the original
checkout's source and PDF have since changed and are preserved independently.

## Explicit Fock constants while the Green checks run

The [all-order written norm derivation](EXPLICIT_JET_FOCK_NORMS.md) now gives
`||z^p exp(sz)||^2=p! exp(|s|^2) sum_(j=0)^p binom(p,j)|s|^(2j)/j!`,
an adjacent-jet pairing formula and explicit finite constants for the packet's
ordinary residual. Exact diagnostics passed 2,025 coefficient comparisons and
25 symbolic derivative identities through order 12. This refines the analytic
estimates without changing the full objective. It does not establish the
remaining relative paired budget, the full Fock compatibility bridge or a
new Lean result.
