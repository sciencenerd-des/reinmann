# Quantitative recurrence: a rank-two mechanism

This continuation makes two advances: an abstract all-rank implication is now
formalized, and the rank-two Xi inequality is reduced to a specific scaled-deficit
log-concavity condition. Neither asserts that the unbounded Xi hypothesis holds.

## The all-rank deduction

`all_ranks_pos_of_quantitative_condensation` in `Reinmann/TuranDeficit.lean`
proves positivity at every rank and shift assuming:

1. Positive rank-zero and rank-one data, and the positive shift-zero boundary.
2. The condensation recurrence at every rank and positive shift.
3. `(m+r) D_r(m-1)D_r(m+1) <= m D_r(m)^2` at every r,m>=1.

The proof uses two-step induction on rank, handling shift zero separately.
This closes the induction step left informal in the preceding report.
It is a theorem about an arbitrary array D. Specializing it to Xi still requires
the stated hypotheses. The general determinant identity is classical, but the
repository's `DodgsonCondensationIdentity` remains an unproved all-size Lean
target; its size-two and size-three cases alone do not instantiate this theorem.

## A simpler sufficient condition at rank two

Use normalized coefficients `a_m=mu_m/mu_0` and define, for m>=1,

```
gamma_m = m! a_m
q_m = a_(m-1) a_(m+1)/a_m^2
epsilon_m = (m+1)(1-q_m).
```

Here q uses the **central** index m. The earlier laboratory's q_n has index
n=m-1. The Lean definition `scaledTuranDeficit a n` represents epsilon_(n+1).

The exponential reference gives `P_2(m)=1/(m!(m+1)!)`. Direct algebra yields

```
A_2(m) := D_2(m)/P_2(m) = gamma_m^2 epsilon_m.
```

If gamma and epsilon are nonnegative and log-concave, their indicated product
is log-concave. Lean proves both this product implication and the exact
factorization. Since
`P_2(m-1)P_2(m+1)/P_2(m)^2=m/(m+2)`, log-concavity of A_2 gives precisely

```
(m+2) D_2(m-1) D_2(m+1) <= m D_2(m)^2.
```

The rank-one strengthened Turan inequality is the gamma condition. The missing
sufficient condition is therefore **positivity and log-concavity of epsilon at
all positive indices**. This is stronger than necessary: gamma's own curvature
could compensate for some positive log-curvature of epsilon.

The neighbor argument above applies at m>=2. At m=1 the determinant uses the
zero-extension boundary. There `A_2(0)=1`, `A_2(1)=2(a_1^2-a_2)` and
`A_2(2)=12(a_2^2-a_1 a_3)`. That separate boundary inequality must also be
established; one must not invent epsilon_0 using a negative coefficient moment.

## Certified finite evidence

`experiments/certified_xi/rank_two.py` consumes the existing exact rational
coefficient enclosures; it does not recompute or relabel the old decimal cache.
It checks the factorization against direct determinants and outputs interval
slacks and the theta moment interpretation below.

- 117 positive epsilon log-concavity slacks, centers m=2 through 118.
- Five positive slacks using only independent theta enclosures, centers m=2..6.
- At m=118, epsilon is approximately 1.52976210 and its unnormalized
  log-concavity slack is approximately 1.09987913e-5.
- All five small independent windows and all 117 Taylor windows also have a
  positive rank-two logarithmic budget slack.

These are bounded numerical certificates under the documented FLINT trust
boundary. The first-shift boundary is also certified positive using each coefficient
source independently. The script does not prove a tail estimate or any
unbounded-order conclusion; these ball certificates have not been imported
as coefficient theorems in Lean.

## Exact counterexample to a shortcut

For `F(z)=2 exp(z)-1`, the exponential coefficients are `gamma=(1,2,2,2,...)`.
They are globally log-concave; Lean proves that statement for every index.
The ordinary coefficients begin `(1,2,1,1/3,1/12,...)`.

At rank two the determinants at shifts 1,2,3 are `(3,1/3,1/36)`. Thus

```
eta_2(2) = 1 - (3 * 1/36)/(1/3)^2 = 1/4 < 1/2.
```

Equivalently, `A_2=(6,4,4)` on those shifts has log-concavity slack -8, and
epsilon `(3/2,1,1)` has slack -1/2. These values are regression controls;
Lean also checks the strict failure of the proposed rank-two inequality.
This function's nonreal zeros are explicit, `-log(2)+2 pi i k`, k nonzero.
It is not a positive theta-kernel model. Its role is to rule out deduction
from the rank-one coefficient condition alone.

## What the theta estimate needs to control

Write `I_m=integral_0^infinity u^(2m) Phi(u) du`; then
`mu_m=2 I_m/(2m)!`. For the probability measure proportional to
`u^(2m-2) Phi(u) du`, put Y=u^2. Its squared coefficient of variation is
`v_m=Var(Y)/(E Y)^2`. Algebra gives

```
c_m = (2m)(2m-1)/((2m+2)(2m+1))
q_m = c_m (1+v_m)
epsilon_m = (m+1)(1-c_m(1+v_m)).
```

Thus the strengthened rank-one bound is equivalent to
`v_m <= 2/(2m-1)`. This is a variance budget, not yet the rank-two condition:
rank two needs control of how that budget changes under successive tilts.
The script reports interval values for v_m and its rank-one budget slack.

An analytic route is to interpolate m by a real variable x>=1. Where
`0<q(x)<1`, set `ell(x)=log q(x)`. Direct differentiation gives

```
(log epsilon)'' = -1/(x+1)^2
                 - q ell''/(1-q) - q (ell')^2/(1-q)^2.
```

Consequently, proving

```
q(1-q) ell'' + q (ell')^2 + (1-q)^2/(x+1)^2 >= 0
```

on x>=1 is a sufficient continuous route to the discrete epsilon condition.
For `K(x)=log I_x`,
`ell=log c+K(x-1)+K(x+1)-2K(x)` and
`K''(x)=4 Var_x(log u)` under the u^(2x) tilt. This identifies the needed
higher variation of the tilted variance. None of the derivative bounds or
continuous inequalities is certified by the finite integer data.

## Literature boundary

[Huh–Matherne–Mészáros–St. Dizier](https://arxiv.org/html/1906.09633v3) prove
Lorentzian/log-concavity statements for a monomial-factorial normalization of
Schur polynomials at a fixed partition. Their normalization is not division
by our exponential-reference determinant, and their variable directions are
not the changing rectangular shape here. Applying that theorem directly would
need a separate representation and preservation argument.

[Lam–Postnikov–Pylyavskyy](https://arxiv.org/html/math/0502446v3) establish Schur
positivity and Schur log-concavity results. A positive-variable specialization
would itself require a justified representation of the Xi coefficient sequence.
Assuming such a representation from a real-negative zero product would place
the desired RH content in the input. These sources suggest possible structures;
this review establishes no direct theorem that settles the new epsilon target,
and makes no exhaustive claim that it is absent from the literature.

## Replay

```sh
uv run --with python-flint==0.8.0 --python 3.12 python experiments/certified_xi/rank_two.py --coefficients research/certified_xi/coefficients_120.json --output research/certified_xi/rank_two_120.json
uv run --with python-flint==0.8.0 --python 3.12 python -m unittest discover -s experiments/certified_xi -v
lake build
bash scripts/verify_axiom_clean.sh
```

The next experiment should estimate the continuous curvature terms with
rigorous logarithmic-moment integrals. The next proof should bound their
combination uniformly, treating the first-shift boundary separately. A larger
integer scan alone would not resolve that obligation.

## Validation completed

- `lake build`: passed (3,524 jobs).
- `bash scripts/verify_axiom_clean.sh`: passed; 101 audited theorems, no
  `sorry`/`admit` or project-declared axioms.
- Direct `safe-verify.sh` check of `Reinmann/TuranDeficit.lean`: passed.
- Certified-Xi unittest suite: 11 tests passed, including five new rank-two
  tests and the existing coefficient/recurrence controls.
- The rank-two generator completed; its source and coefficient-input hashes
  match the artifact. Both first-shift boundary enclosures are positive.
- `git diff --check`: passed.

Changed in this continuation: `Reinmann/TuranDeficit.lean`,
`Reinmann/AxiomAudit.lean`, the new `rank_two.py` and `test_rank_two.py`, their
JSON artifact, this note and documentation links. Historical manuscript and
unrelated existing work were preserved. No commit or push was performed.

## Continuous-parameter continuation

The [continuous theta laboratory](RH_CONTINUOUS_THETA_2026_09_14.md) now
implements logarithmic-moment integration with explicit tails, fractional-point
curvature checks, and interval covers. Its separate report records the exact
certified domain; it supplies no unbounded tail estimate.
