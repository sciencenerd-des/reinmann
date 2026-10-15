# Universal Xi Green recurrence on the actual coefficient domain

Status: combined Lean check passed, 2026-10-11. The current namespace bodies of
all three modules passed in one incremental workbench, with zero errors and all
48 theorem audits using only `propext`, `Classical.choice` and `Quot.sound`.
Their exact equality with the canonical module bodies was checked. This covers
the Green identity, actual-domain symmetry and same-form all-zero mass estimates.
The separate module builds and full project verification are now running in
sequence. Until those finish, the earlier algebraic mass record remains the
latest fully built milestone; no full-construction validation certificate or
RH proof is claimed.

## Why this construction is aligned with the original objective

The ambient space, arithmetic coefficient action and Xi row domain are exactly
those of the [fixed algebraic jet space](ALGEBRAIC_JET_MASS.md). The parameters
still cover every complex number and every jet order, before selecting zeros.
The form is specified once on the whole span. This construction seeks to check
both action symmetry and all-zero packet mass estimates for that same form.
It does not narrow the domain to simple zeros, finite samples or separately
chosen metrics. It does not replace the required paired budget by a norm-product
condition.

The earlier mixed-derivative form has checked masses, but a complete formal
calculation of its mixed derivatives and Green identity remains open. Here a
universal arithmetic recurrence defines the Gram entries directly. Equality
of every entry with that earlier mixed-derivative Gram matrix is not assumed.
The coherent-to-reflected-jet coupling and mass estimates are therefore proved
again for this recurrence form, rather than transferred without a bridge.

## Universal entries

Write `delta=s+conjugate(t)-1` and `D_p(s)=Xi^(p)(s)`. At `delta=0`, put

```text
C_(p,q)(s) = i (-1)^q p! q! D_(p+q+1)(s)/(p+q+1)!.
```

Away from `delta=0`, define the raw entries recursively in `p+q` by

```text
delta R_(p,q) + p R_(p-1,q) + q R_(p,q-1)
  = i ([q=0]D_p(s) - [p=0]conjugate(D_q(t))).
```

A term with a zero prefactor is omitted. Division occurs only in the branch
where `delta` is nonzero. The confluent entries obey this same balance:
interior neighbor terms cancel, and the boundary cases use Xi reflection and
conjugation. Hermitianize once by

```text
K(a,b) = (R(a,b)+conjugate(R(b,a)))/2.
```

The right side of the balance transforms correctly under conjugate exchange,
so the Hermitianized entries retain it. At the reflected partner,

```text
K((s,0),(1-conjugate(s),p)) = i(-1)^p D_(p+1)(s)/(p+1).
```

These definitions and candidate proofs are in
[XiGreenGram.lean](../../Reinmann/XiGreenGram.lean).

## Actual row compatibility

For any parameter and jet order, the proposed row calculation is

```text
sum_k derivativeRowTerm(j,0,J(s,p),k) = D_(j+p)(s),
```

with a `HasSum` theorem, not just a formal series identity. It follows from
the checked creation/row shift and the entire Xi derivative Taylor series.
Finite addition and scalar multiplication then give the actual zeroth Xi row
on every finite jet expansion:

```text
R_0(realize(c)) = sum_a c_a D_(order(a))(parameter(a)).
```

This is the row functional used in the independently defined arithmetic
coefficient domain. The finite coordinate action is transported from the
already defined coefficient differentiation via the checked injective
realization. Its jet formula is verified rather than used to prescribe a
zero-indexed spectral model.

See [XiAlgebraicRows.lean](../../Reinmann/XiAlgebraicRows.lean).

## Finite Green identity and masses

Finite sesquilinear extension of the entry balance is intended to yield

```text
eta(Tc,d)-eta(c,Td)
  = R_0(c) conjugate(d_0)-c_0 conjugate(R_0(d)).
```

Both row values vanish on the actual arithmetic domain, proving action symmetry
there if the implementation passes. The all-zero finite multiplicity theorem
and reflected jet membership then give a nonzero cross partner for this same
form. The generic packet lemma supplies

```text
h |B|^2 <= q_h <= 3h |B|^2,
eta(psi_h,psi_h)=1,
(T-lambda(s))psi_h = h B/sqrt(q_h) (T-lambda(s))w.
```

The non-isotropic case uses direct absolute-mass normalization. The candidate
therefore includes an actual-domain state of unit absolute mass at every Xi
zero, with no RH or simplicity premise.

See [XiGreenModel.lean](../../Reinmann/XiGreenModel.lean).

## The remaining RH-strength condition

Action symmetry and nonzero approximate-state masses do not alone prove RH.
For this symmetric form the candidate identity is

```text
|d(x,(T-lambda(s))x)| = 2 |Re(s)-1/2| |eta(x,x)|,
d(x,y)=eta(y,x)-eta(x,y).
```

At unit absolute mass, the paired residual is exactly twice the critical-line
distance. `GreenUnitMassPairedBudget` names the required arbitrarily small
positive-tolerance bound at every critical-strip zeta zero. The module includes
a proposed equivalence of this condition with RH; it does not supply a proof
of either side. Small ordinary residuals and the packet mass estimate must not
be represented as proving this missing bound.

No Hilbert completion, positive global metric, closedness, self-adjointness,
resolvent control or full-spectrum claim is made for this algebraic construction.
No novelty claim or publication is made.

## Verification sequence

```sh
lake build Reinmann.XiGreenGram
lake build Reinmann.XiAlgebraicRows
lake build Reinmann.XiGreenModel
```

After these targets pass, add their root imports, run the full project build,
and audit every new theorem for verification shortcuts and axiom dependencies.
Until then, the files are research implementations with unresolved formal
verification, not a replacement for the previous successful validation record.

The combined check subsequently passed at version 3 after the localized proof
repairs described below. Its immutable diagnostics, canonical source hashes and
48 axiom messages are saved in
[`verification/green_workbench_v3_passed.json`](verification/green_workbench_v3_passed.json).
The [canonical execution tracker](green_canonical_checks_2026_10_11.json) records
the separate builds, full build and audit as they run. It guards the three
canonical source hashes and adds root imports only after all three target
builds pass. It is an execution tracker, not a goal-completion certificate.

The first Gram build returned exit code 1 after reaching the proofs. Its
diagnostics concerned the zero-order reflection simplification, conjugation
through conditionals and the orientation of the reflected derivative identity.
Localized repairs have been written but are not yet checked. The failed log
and the exact source hash used for that attempt are retained in the working
tracker. The same row compiler was resumed after the Gram check ended; an
incremental combined checker is queued behind it. This records progress without
promoting the recurrence model to a verified result.

The first row build subsequently returned exit code 1 with one zero-case
`HasSum` simplification error. The repair now explicitly proves that the zero
coefficient vector has the zero Xi-row sequence before applying `hasSum_zero`.
The remaining seven row/action theorem declarations reported no errors in that
attempt, but clean module verification is still pending. The guarded checker
then launched `lake serve` and was sampled while loading its workspace.
The project shortcut scan passed for all 113 Lean files, and the prepared axiom
audit was checked to cover every one of the 46 new theorem declarations exactly
once. Neither check substitutes for the pending successful theorem builds.

Two additional candidate Fock coefficient-series lemmas make the coherent-to-jet
pairing explicit at every order. They are kept separate from the Green metric
and bring the prepared audit to 48 theorem declarations, all covered exactly
once. The source shortcut scan was rerun after that addition and again passed
for all 113 project files. The incremental workbench opened successfully; its
worker is processing the unchanged common imports before the proof checks.

## Independent synthetic diagnostic

`python3 research/pseudo_hermitian/check_green_recurrence_polynomials.py` passed
288 exact comparisons of recurrence entries against separately differentiated
polynomial divided-difference kernels. The degree-4 and degree-8 inputs cover
mixed jet orders through three, reflected and nonreflected parameter pairs,
Hermitian symmetry, and the complete finite Green matrix identity with nonzero
boundary terms. This checks more than a zero-domain cancellation.

The [diagnostic record](green_recurrence_polynomial_diagnostics.json) concerns
these two synthetic polynomials only. It is not a general proof, a Lean result,
a Xi-zero certificate or evidence that the remaining RH budget holds.
