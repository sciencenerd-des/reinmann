# First actual Xi tile and mixed analytic-error rows

This round implements the requested first evaluator tile and the finite-algebra
and analytic-patching obligations for the standalone split-pair extension.
It does not prove RH, certify the full low-height rectangle, or replace a
classical PF-to-RH bridge with simple-zero or modulus-genericity assumptions.
The published DH controls preprint remains the unreviewed release at
https://doi.org/10.5281/zenodo.23401370; its files and scientific claims are unchanged.

## Target B: one genuine tile

`Reinmann/XiFirstTile.lean` proves

    norm (xiCompleted (1/2) - 397/800) <= 3/20
    norm (deriv xiCompleted w) <= 10    when norm (w-1/2) <= 1/4
    xiCompleted z != 0                 when norm (z-1/2) <= 1/100.

The first statement evaluates the actual entire Xi target. It keeps the n=1
theta term on [1,4], rewrites the real power as exp((-3/4) log t), encloses the
midpoint sample by 1/100 with error 13/50, and encloses variation throughout the
panel. The resulting quadrature error is 39/50 before multiplication by 1/8.
The omitted theta terms contribute at most 3/1024 and the actual infinite
Mellin tail at most 1/4, also before the 1/8 prefactor. The exact identity then
gives the rational centre error 3/20. The tile margin is

    3/20 + 10/100 = 1/4 < 397/800.

This is a deliberately coarse, single-panel enclosure with proved variation,
not a high-order quadrature result. In particular, its midpoint error is not
the precision that will be needed near the first zero. It uses no imported
Arb value and no floating-point oracle. Exp/log inequalities and real/complex
branch identification are proved in Lean.

`XiAdaptiveTiles.lean` supplies a finite-cover rule with a different derivative
bound for each convex tile. Its quarter reduction uses the proved identities
xi(conj s)=conj xi(s) and xi(1-s)=xi(s), including every boundary. The reduced
rectangle is 1/2 <= Re(s) <= 1, 0 <= Im(s) <= 14.1.

`XiLocalCauchy.lean` proves the actual-Xi majorant 1000 on each unit circle
centred in that quarter, and the corresponding ordinary Taylor-coefficient
bound. The latter supplies the majorant used by the external pilot.

## Compatibility and cost

LeanCert current main uses a newer toolchain. The historical official commit
`5a59804aa7c499f81ffd5eedf2a2cc5f9e8766d1` pins Lean and Mathlib v4.30.0.
The isolated replay in `check_leancert_v430.py` compiles its thin rational Taylor
interval API and proves exp(1)<=3 and log(3/2)<=1/2 with `decide +kernel`.
Both proofs depend only on propext, Classical.choice and Quot.sound. No project
dependency or toolchain file is changed.

The broader `evalIntervalCore1_correct` theorem carries native proof dependencies
from its Euler-Mascheroni named-constant cases. Avoid that theorem and the
default native-decision tactic path under this repository's standard-three-axiom
policy. The direct exp/log interval theorems pass the policy. This distinction
comes from an actual dependency audit, not from the presence of a tactic name
in a source file.

With dependencies cached, re-elaborating the full first-tile source took 38.6
seconds in the initial timing run and 22.6 seconds for the final source. This is evidence that a coarse genuine tile
is affordable. It is not a timing model for complex high-height centres or
Taylor jets.

The 192-bit Arb pilot on the quarter proposes 35 adaptive tiles using degree-16
point jets and a Cauchy tail. It evaluates the actual Xi function, with its
removable pole treated by deflation. An alternate direct interval-derivative
pilot accepted 2498 tiles in 5000 attempts and still had 5 boxes pending; this
is a budget-limited partial cover, not a certified tile count.

The 35-tile geometry remains external evidence. Its point-jet enclosures,
derivative-series tail identity and complete cover have not been instantiated
in Lean. The next useful performance test is a complex centre near height
14.1 with its required small absolute error, followed by its jet/derivative
certificate. Do that before scaling or extrapolating 35 times the coarse-tile
runtime. There is not yet evidence requiring a switch to a boundary-only
argument-principle method.

## Target A: finite algebra and common remainder

`SplitPairMixedRows.lean` proves the exact row-choice expansion for a determinant
with analytic-error rows. Repeated pole rows cancel even in mixed terms. A
normalized subset-product inequality controls the surviving distinct poles,
and the Leibniz bound keeps each row's own weight. Combining these proves

    norm(det H_n - det M_n) / D^n
      <= (m+1)^s * s! * (C B^(2s-2))^s * (rho/d)^n,

for coefficient errors bounded by C rho^n, residues bounded by C,
B >= max(1,rho,max pole modulus), and a top set of s poles with all retained
moduli >= d and all other moduli <= d. With rho=1/R, this is the draft's rate
q=1/(R d). The estimate permits q=1; exponential decay requires the strict
q<1 condition. It also permits modulus ties in the ordered-product estimate.
Strict separation and the isolated split pair are separate oscillation-model
hypotheses, not hidden conditions on the PF-to-RH implication.

`SplitPairPatchedRemainder.lean` constructs one analytic function from the
already proved simple-pole germs. It agrees with 1/F minus the full sum of
principal parts away from the selected zeros, and is analytic through every
selected zero. The construction uses distinct selected zeros with nonzero
F' and an exact local zero-set condition on the chosen closed disk.

`SplitPairCoefficientIdentity.lean` derives the actual ordinary Taylor
coefficient identity, including the principal-part coefficient

    coefficient(r/(z-a), n) = (-r/a) (1/a)^n.

For r=1/F'(a), the sign is therefore -1/(a F'(a)). The common remainder's
analyticity supplies a finite circle bound and the Cauchy error C/R^n.
Neither coefficient decomposition nor exponential coefficient error is an
assumption of the final reciprocal coefficient-error theorem.

These are standalone prerequisites for the entire-function split-pair result.
The final sign-oscillation/Jacobi assembly is not asserted here as a new complete
genus-zero theorem. Arbitrary zero multiplicities and further modulus ties are
not handled by the simple-pole analytic construction. No PF-to-RH theorem or
its hypotheses have been modified.

## Verification and release separation

The complete build passes (3595 jobs), and all 348 audited theorems depend only
on the standard three axioms. There are 35 newly audited public declarations,
with no sorry, admit or project-declared axioms.

Run:

    lake build
    bash scripts/verify_axiom_clean.sh
    uv run --offline --with python-flint==0.8.0 --python 3.12 python \
      experiments/prime_spectral/xi_adaptive_tile_pilot.py --output tmp/xi-pilot.json
    python3 experiments/prime_spectral/check_leancert_v430.py
    python3 experiments/prime_spectral/verify_first_tile_round.py

The verification folder binds the new sources, receipts and pilot, and preserves
pre-round copies of the two integration files changed from publication commit
0e4a6e8203c570be8d52246650dc0c1b294b47c6. The old publication manifest remains
immutable. Its other 1068 bound artifacts are checked against the existing
release hashes. The split-pair and local-Xi modules are imported by the aggregate
and covered by the standard axiom audit. No public upload, reviewer message,
Liu note, numerical forecasting or stopped scan was performed in this round.
