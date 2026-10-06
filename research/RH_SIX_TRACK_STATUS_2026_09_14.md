# Six-track RH research status

The active program has repaired interfaces and numerical classifiers, rigorous
finite coefficient enclosures, an explicit finite-order literature baseline,
a certified theta interval laboratory, and one separate prime-defined route.
No unbounded Xi inequality or RH proof has been obtained.

| Track | Current evidence | Remaining obligation |
|---|---|---|
| 1. Interfaces and classifiers | Classical Jensen coefficients use n! mu_n; complex convergence requirements are explicit; misleading scalar discriminant/flow classifications repaired. Current Lean build and classifier tests pass. | Analytic bridge premises must be proved, not supplied as circular certificates. |
| 2. Certified Xi coefficients | 121 Taylor coefficient balls through index 120; a separate theta integration check through index 8. The loader checks interval consistency and source linkage for this run. | Formalize coefficient identification and import numerical certificates into Lean if that trust reduction is required. Current rigor relies on FLINT and documented analytic bounds. |
| 3. Finite positivity baseline | PF43 used conservatively from Katkova's printed argument; finite-PF algebraic transport is proved in Lean. | The analytic PF43 premise remains explicit. Naming the proposition is not a formal import of the external analytic theorem. |
| 4. Theta deficit laboratory | Coupled third-moment derivative bounds certify strict scaled-deficit log-concavity on [1,3], with 1,018 cells. | An unbounded theta estimate with explicit uniform remainders. |
| 5. Unbounded-rank mechanism | Abstract conditional induction is formalized. New exact normalized recurrence and 4,230 finite transport windows; all full curvature balances positive. | A preserved bound for the combined curvature and separate boundary control, uniform in rank and shift. Correction-factor log-concavity alone is false in 13 tested windows. |
| 6. Independent arithmetic program | One finite prime-power Weil-matrix implementation, separate from Xi coefficients and zeta-zero inputs; four regression tests pass. | Rigorous quadrature/eigenvalue bounds, omitted-mode control, the intended perturbed operator and locally uniform determinant convergence. Current spectra are floating diagnostics. |

## This continuation

The main new result is an obstruction to an overly strong sufficient condition
in track 5, with a precise replacement target. See
[the normalized recurrence derivation](RH_NORMALIZED_RECURRENCE_2026_09_14.md)
and `certified_xi/normalized_recurrence_120.json`.
The first negative correction at rank 34, shift 4 was recomputed from fresh
determinants using the original coefficient enclosures. Its inherited
curvature more than compensates for the negative correction.

The finite baseline remains grounded in
[Katkova's paper](https://arxiv.org/abs/math/0505174), with the printed sector
issue explained in [the baseline note](FINITE_PF_BASELINE_2026_09_13.md).
The single arithmetic route remains grounded in
[Connes–Consani–Moscovici](https://arxiv.org/abs/2511.22755);
the paper's convergence strategy is not a completed convergence proof in this
repository. Its actual perturbed scaling operator must not be confused with
the finite Weil form currently implemented.

## Current validation

- `lake build`: passed, 3,524 jobs.
- `bash scripts/verify_axiom_clean.sh`: passed, 101 audited theorems, no sorry/admit or project-declared axioms.
- Certified-Xi suite: 25 tests passed with python-flint 0.8.0 on isolated Python 3.12.
- Classifier suite: 5 tests passed with isolated Python 3.12 and mpmath/numpy/sympy.
- Prime spectral suite: 4 tests passed with system Python.
- New normalized recurrence generator: completed; 4,230 positive transported curvatures, 13 negative correction curvatures, fresh negative determinant check passed.

The first system-Python classifier attempt could not import mpmath; the isolated
environment resolved that dependency without changing system packages. A new
reference test initially required containment of one rounded ball inside
another; it was corrected to overlap, the appropriate comparison of two
independent rigorous enclosures of the same exact value. Final suites passed.

The numerical and proof gaps above remain research work. The strongest next
step is a quantitative invariant that tolerates negative correction curvature,
paired with explicit theta tail estimates. More finite positive windows alone
would not establish that invariant.

## Subsequent tail and rank-budget continuation

The [new derivation](RH_EVENTUAL_TAIL_AND_RANK_BUDGET_2026_09_14.md) establishes
a qualitative eventual discrete scaled-deficit conclusion from O'Sullivan's
asymptotic expansion, but gives no explicit threshold or continuous derivative
bound. Two additional conditional Lean theorems prove cumulative rank slope
and linear lower-bound implications. The finite budget laboratory checks
4,347 prefixes; all pass a half-base loss budget. This does not settle the
unbounded Xi-specific budget or shift-one boundary.

## Effective remainder and boundary continuation

The [effective remainder note](RH_EFFECTIVE_REMAINDER_BOUNDARY_2026_09_14.md)
now supplies explicit uniform omitted-theta bounds for moment orders 0..4.
It does not yet bound the first-summand saddle approximation error. The
shift-one boundary is reduced to a reciprocal-coefficient ratio band and
checked through rank 119. Dual determinants extend the budget stress test to
560 interior prefixes and 113 boundary prefixes, all passing. A uniform
all-rank loss bound and the full continuous theta curvature estimate remain
open. Current validation is 33 certified-Xi tests and 104 audited Lean theorems.

## Uniform boundary update — 2026-09-15

The [two-pole boundary certificate](RH_UNIFORM_BOUNDARY_CURVATURE_2026_09_15.md)
now closes the shift-one boundary inequality and the zero-negative-loss
boundary budget for every rank, under FLINT and the documented complex-analysis
argument. Its two tails begin at ranks 26 and 61, with finite bridges covering
all smaller indices. This supersedes the previously finite-only boundary status.
The analytic proof is not formalized in Lean. The interior all-rank budget
remains open. A conditional moment-to-curvature error-transfer module is also
implemented; the effective first-summand saddle errors it needs remain open.
Current certified-Xi validation: 37 tests passed.

## Localized saddle update — 2026-09-15

The [localized saddle calculation](RH_LOCALIZED_SADDLE_2026_09_15.md) now
provides effective first-summand moment errors at individual parameters,
including both infinite spatial tails. Combined with the uniform omitted-theta
bound, these certify true negative log-epsilon curvature at x=257, 4097,
65537. This supersedes the absence of an implemented first-summand error
bound at points; a uniform continuous tail bound remains open. The new note
also derives the conditional fixed-shift pole asymptotic and explains its
failure to provide the required uniform all-shift argument without assuming
global zero information. The prior shift-one boundary result remains intact.
Current certified-Xi validation: 41 tests passed.

## Uniform quadratic remainder update — 2026-09-15

The [uniform quadratic saddle bound](RH_UNIFORM_QUADRATIC_SADDLE_2026_09_15.md)
now supplies a full first-summand model error for every real parameter beyond
a declared threshold, including the central interval and both infinite tails.
This closes the absence of any uniform computable saddle-model remainder,
but the bound is not sharp enough to establish the desired curvature sign.
The derivation identifies both the near-unit-q error requirement and a fixed
window's nonzero tail-error floor. Higher-order phase control, amplitude
retention, and improving tail treatment remain necessary for this approach.
The uniform interior cumulative rank budget remains open.
Current certified-Xi validation: 45 tests passed.

## Higher-order growing-window update — 2026-09-15

The [higher-order saddle calculation](RH_HIGH_ORDER_SADDLE_2026_09_15.md)
retains the amplitude and uses a growing standardized window, eliminating
the fixed-radius tail floor. Its degree-16 relative moment errors are below
1.184e-34 uniformly for every real x>=10^8. Full error propagation certifies
negative true curvature at x=100000001; x=1000001 remains unresolved with
these bounds. The outstanding analytic step is now uniform sign control
of the model-moment curvature expression, followed by the necessary bridge.
The uniform interior rank budget remains separate and open. The shift-one
boundary certificate remains unchanged.
Current certified-Xi validation: 49 tests passed.

## Leading-model proof and literature audit — 2026-09-15

The [leading Lambert sign theorem](RH_LAMBERT_SIGN_AND_SCOPE_2026_09_15.md)
proves a negative curvature margin for every real x>=256 using a Laplace
variance bound and a monotone endpoint budget. This concerns a simpler explicit
model, not the degree-16 moment model or the true Xi deficit. A coupled residual
derivative criterion is proved, but its Xi hypotheses remain open. An exact
counterexample shows that real-zero structure and double-Turan inequalities
alone do not imply normalized-deficit concavity. Five algebraic controls build
in Lean with standard axioms only. The uniform interior rank budget remains open.
Current certified-Xi validation: 53 tests passed.

## Common-remainder derivative theorem — 2026-09-15

[Freezing the saddle reference at each anchor](RH_COMMON_REMAINDER_2026_09_15.md)
now gives one analytic remainder across the neighboring-parameter interval.
Explicit complex-disk domination proves zero exclusion and uniform bounds
on its second through fourth derivatives for every anchor beyond a threshold.
The tent-kernel identity preserves cancellations in the curvature transfer.
At a=1000001 the joint bound certifies negative curvature where independent
moment errors were inconclusive. This constructs an anchor-indexed family,
not a global identification with the moving or leading Lambert model.
The uniform reference-curvature sign and interior all-rank budget remain open.
Current certified-Xi validation: 57 tests passed.

## Decaying common-remainder refinement — 2026-09-15

The [new theta bound and power-law envelope](RH_DECAYING_COMMON_REMAINDER_2026_09_15.md)
remove the fixed omitted-theta contribution from the common-remainder budget.
From X=10^6, derivative order j has a proved uniform envelope
E_j(X)(u(a)/u(X))^16(X/a)^(7+j/2), for every a>=X and |y-a|<=1.
This makes the error decrease explicitly across the unbounded anchor domain.
The uniform reference-curvature sign and the interior all-rank budget remain
unproved. A recent rank-uniform cubic-wedge preprint was located and its scope
recorded; no external theorem or certificate was imported.
Current certified-Xi validation: 59 tests passed.

## Conservative unbounded curvature tail — 2026-09-19

The [Gaussian cumulant proof](RH_GAUSSIAN_CURVATURE_TAIL_2026_09_19.md)
now establishes negative frozen-reference and true Xi curvature for every
real anchor a>=2000*pi*exp(4000), in ordinary analysis. The cubic-square
and quartic contributions combine to give the strictly negative leading
coefficient -(4u^2+8u+1)/(1+2u)^4. A complex Gaussian replacement estimate
bounds derivatives of the common error; an elementary monotone budget
controls the whole tail. Exact multivariate polynomial identities and the
budget endpoint are checked by FLINT rational arithmetic. The analytic
argument is written, not Lean formalized. This does not prove negativity
at every smaller anchor, or the interior all-rank budget. The existing
shift-one boundary result is unchanged.

Validation: all 63 certified-Xi unit tests passed, including the four new
Gaussian identity, cubic-square regression, tail budget, and domain tests.

## Effective Gaussian tail threshold — 2026-09-19

The [explicit Gaussian majorants](RH_EFFECTIVE_GAUSSIAN_TAIL_2026_09_19.md)
reduce the sufficient curvature tail threshold to a>=80*pi*exp(160),
approximately 7.7154e71. The uniform relative error is below 0.009502 of
the negative leading margin. The proof uses decreasing envelopes for the
finite phase remainder, Gaussian tails, amplitude, analytic logarithm,
Cauchy derivatives, and the true theta transfer. Every sufficient endpoint
condition passes with FLINT balls; exact rational upper bounds are saved.
The written analytic proof is not Lean formalized. Lower anchors and the
interior all-rank budget remain unproved. Validation: 68 tests passed.

## Integrated Gaussian error and larger reference disk — 2026-09-19

The [integrated error argument](RH_INTEGRATED_GAUSSIAN_TAIL_2026_09_19.md)
reduces the sufficient threshold to a>=40*pi*exp(80). Absolute Gaussian
moments replace window suprema in the central error integral. A reference
disk of radius sqrt(a)/2 improves Cauchy derivative bounds, with its full
complex-tilt penalty included. All sufficient conditions pass, and the
uniform relative error is below 0.038351 of the negative leading curvature.
Both reference and true Xi curvature are covered. This is a written
analytic proof with ball-checked constants, not a Lean formalization.
Lower anchors and the interior all-rank budget remain unproved.

Validation: 71 certified-Xi tests passed. Both tail artifacts match the
current implementation hash; `git diff --check` passed.

## Conditional self-sustaining rank tail — 2026-09-19

The [new rank-tail bound](RH_RANK_TAIL_BOOTSTRAP_2026_09_19.md) derives
C_r(m)>=-2exp(-delta_r(m))/(1-exp(-delta_r(m))) under positive neighboring
correction factors. A head curvature d and slope v sustain a slope b>0
forever if 2exp(-d)/[(1-exp(-d))(1-exp(-b))]<=v-b. The written proof uses
induction and a geometric-series bound. Finite Xi heads pass at ranks
24,28,51,43,59 for shifts 2,3,4,5,6, respectively, with b=v/2.
These are conditional head witnesses. Uniform compatible head bounds at
all shifts and the neighboring-factor condition are still unproved;
no unconditional interior all-rank or RH conclusion has been established.
The note spells out the simultaneous induction needed to discharge that
dependency and preserves the separate shift-one boundary control.

Validation: 75 certified-Xi tests passed; input/source hashes match the
current files, and `git diff --check` passed.

## Compensated rank-tail budget — 2026-09-19

The [compensated theorem](RH_COMPENSATED_RANK_TAIL_2026_09_19.md) retains
both the exactly telescoping positive factorial baseline and m/(r+m).
A finite comparison prefix plus a proved infinite geometric tail bound
sustains a positive rank slope under the same explicit neighboring-factor
hypothesis. First passing Xi heads in ranks 2..113 are now 16,21,33,34,44
for shifts 2..6. The artifact stores every prefix margin and infinite
residual bound. Uniform compatible heads across every shift remain
unproved, so these are conditional witnesses, not an all-rank Xi proof.

Validation: 79 certified-Xi tests passed, input/source hashes match, and
`git diff --check` passed.

## All-rank shift-two certificate — 2026-09-19

The [three-pole certificate](RH_UNIFORM_SHIFT_TWO_2026_09_19.md) now proves
D_r(2)>0 and 0<t_r(2)<1 for every integer r>=1 under the analytic-numerical
trust boundary. A 512-arc contour certifies exactly three zeros in |z|=800;
three real brackets account for all of them. Removing the poles gives a
Cauchy coefficient remainder. Determinant error bounds preserve vanishing
repeated rank-one columns, so all normalized error terms decay. The tail
starts at rank 45 and coefficient intervals cover ranks 1..44.
This is independent of future neighboring-factor assumptions. It does not
prove positive C_r(2), the all-shift rank budget, or RH. The written proof
is not Lean formalized. The existing shift-one certificate remains intact.
Validation: all 83 certified-Xi tests passed.

## Fixed-shift inference obstruction — 2026-09-19

The [deformation proof](RH_FIXED_SHIFT_OBSTRUCTION_2026_09_19.md) constructs
E_tilde(z)=E(z)*(1+(z/3200)^122). Its first 122 coefficients and three
interior zeros are unchanged; all coefficients remain positive. Recomputed
pole remainder bounds and 88 inherited bridge cells establish both
strengthened shift-one and shift-two inequalities at every rank, despite
an exact added nonreal folded zero at 3200i. This is not Xi and is not an
RH counterexample: the full theta/arithmetic identity is not preserved,
and no all-index PF43 preservation is claimed. It proves that the specified
finite-prefix and fixed-shift certificates alone cannot imply the global
zero statement. A genuinely all-shift or arithmetic input remains necessary.

Validation: 87 certified-Xi tests passed; source/input hashes and all 88
bridge cells were verified. `git diff --check` passed.

## Independent prime-program finite certificates — 2026-09-19

The [certified Weil calculation](prime_spectral/CERTIFIED_WEIL_GATES_2026_09_19.md)
replaces refinement diagnostics with interval integration and inertia at
cutoff 13, modes 4 and 8. Both finite forms are positive definite with a
simple even lowest eigenvector and nonzero boundary evaluation. Their
lowest eigenvalues are approximately 9.6793e-15 and 7.6744e-23; the latter
has a certified gap above 3.9071e-20. These are Weil-form eigenvalues, not
zeta ordinates. No Xi coefficients or zero data are inputs. The perturbed
operator and all-mode/all-support determinant convergence remain open.
All 9 prime-program tests passed; the analytic argument is not Lean formalized.

## Certified finite-mode eigenvector comparison — 2026-09-19

The [same-support comparison](prime_spectral/CERTIFIED_MODE_COMPARISON_2026_09_19.md)
encloses boundary-normalized eigenvectors via a rigorous projected solve.
At cutoff 13 the modes-4 and modes-8 unit vectors have distance about
0.1376, while the origin-normalized coefficient distance is about 0.2699.
Their Rayleigh excess divided by the certified gap is about 247731, so
that spectral estimate does not prove closeness. A complex-disk bound for
the two entire profiles is proved, together with explicit conditional
summability and weighted-kernel targets for future convergence. No bound
on all omitted modes or convergence to Xi has been established.
Validation: all 12 prime-program tests passed.

## Finite quotient construction and necessary joint scaling — 2026-09-19

The [quotient proof](prime_spectral/QUOTIENT_OPERATOR_2026_09_19.md) constructs
the 16-dimensional prime-defined perturbation for cutoff 13 and modes 8.
Its positive quotient metric is certified. Exact displacement algebra proves
metric self-adjointness; a determinant identity proves the associated entire
Fourier profile has only real zeros. Interval zero-containing residuals are
only consistency checks, not the proof of those identities. These profiles
are not identified with Xi. Their forced grid zeros imply the necessary
condition modes/log(cutoff)->infinity for a nonzero locally uniform limit
as support grows. Uniform spectral gates and convergence/identification
remain unproved. All 15 prime-program tests passed.

## Direct common-remainder derivatives — 2026-09-20

The [Gaussian Taylor-jet proof](RH_GAUSSIAN_JET_TAIL_2026_09_20.md)
bounds four derivatives under the same residual integral and preserves the
quadratic cancellation when taking its logarithm. Sharper elementary
denominator bounds remove unnecessary powers of u. It proves negative
reference and true curvature for every u>=14 (a>=14*pi*exp(28)), with
relative error <0.274447. The previous sufficient threshold was u=40.
The written continuum proof includes both Gaussian tails, amplitude variation,
and the earlier true I/Q remainder. It is not Lean formalized.

The interval 10^6<=a<14*pi*exp(28) and a uniform compatible head region
for every shift remain unproved. No all-rank or RH conclusion is drawn.
Validation: all 91 certified-Xi tests passed, including independent direct
integral/logarithm derivative checks at three neighboring parameters.

## Cubic cancellation in the shared remainder — 2026-09-20

The [third-order expansion](RH_CUBIC_GAUSSIAN_TAIL_2026_09_20.md) proves
that the cubic logarithm correction is an odd polynomial of degree five;
the degree-seven and degree-nine terms cancel exactly. Its fourth derivative
vanishes at the center. Keeping this polynomial and bounding the next
remainder yields reference and true curvature negativity for every u>=7,
equivalently a>=7*pi*exp(14), with relative error <0.742183. Amplitude
variation, both Gaussian tails and the full common I/Q error remain included.

The lower-anchor interval 10^6<=a<7*pi*exp(14) and uniform compatible heads
at every interior shift remain open. The theorem is a written analytic
proof with ball-checked constants, not Lean formalized or an RH proof.
Validation: all 95 certified-Xi tests passed, including exact polynomial
cancellation and independently integrated fourth-order log-remainder jets.

## Coefficientwise remainder and deficit-sensitive transfer — 2026-09-20

The [coefficientwise proof](RH_COEFFICIENTWISE_CURVATURE_2026_09_20.md)
keeps each Taylor coefficient's error separately and retains the reference
deficit in the curvature sensitivity bounds. It establishes reference and
true theta curvature negativity for every u>=6, equivalently
a>=6*pi*exp(12), about 3.068e6. The uniform combined relative error is
<0.468174. Full theta and spatial-tail errors remain included.

The lower-anchor bridge 10^6<=a<6*pi*exp(12) is still unproved. This result
also does not supply all-shift head inequalities for the interior rank
recurrence. It is a written analytic proof, not Lean formalized or an RH
proof. All 99 certified-Xi tests passed, including independent checks of
each remainder derivative at the three neighboring offsets.

## Uniform sign on the common-reference domain — 2026-09-20

The [shifted Gaussian proof](RH_SHIFTED_GAUSSIAN_CURVATURE_2026_09_20.md)
absorbs the linear saddle phase into the Gaussian tilt exactly, retaining
the original degree-16 reference. Its coefficientwise common-remainder
bounds establish reference and true theta curvature negativity for every
real anchor a>=10^6, including the endpoint. The combined relative error
is <0.229338. The previously missing lower-anchor bridge in this defined
reference domain is closed by analytic monotonicity, not a point scan.

Parameters below 10^6 and the uniform compatible head estimates needed
for the interior all-rank budget remain unproved. This theorem is written
analysis with FLINT-checked constants, not Lean formalized or an RH proof.
Independent tests integrate the unchanged phase and also use the existing
neighboring-moment routine to check the new derivative/curvature bounds.

Validation of the shifted curvature result: all 102 certified-Xi tests
passed; all nine source hashes and fifteen sufficient conditions were
verified. No Lean source was changed or rebuilt.

## Exact limitation of the positive-slope rank bootstrap — 2026-09-20

The [repeated-root control](RH_REPEATED_ROOT_RANK_CONTROL_2026_09_20.md)
derives all-rank determinant and curvature formulas for `(1+z/N)^N`.
At interior shifts, all required neighboring factors are positive and
delta_r=log(1+r/(N-m))>0. Every finite cumulative slope margin stays
positive, but tends to zero. Thus neither existing positive-uniform-slope
criterion can pass any head of this control, although all its zeros are
negative real. This is a proved limitation of the sufficient method, not
a counterexample to Xi or either conditional theorem. It motivates
retaining neighboring cancellation and allowing zero limiting slope margin.

## Logarithmic rank comparison and persistent slope surplus — 2026-09-20

The [logarithmic comparison](RH_LOGARITHMIC_RANK_TAIL_2026_09_20.md) proves
a conditional all-rank barrier from exact rational head tests:
m*(R+m)*t_R<=1 and t_(R-1)/t_R>=(R+m)/(R+m-1). It allows equality in
both head tests. Finite Xi witnesses occur at ranks 22,28,46,45,60 for
shifts 2..6, later than the corresponding compensated-criterion heads.

The attempted relaxation does not remove the growth restriction. The
strictly positive neighboring terms at the first step create a positive
slope surplus which persists at every later step. The full hypotheses
therefore still imply linear growth. This is an exact obstruction to
that particular workaround, not an RH or Xi counterexample. A rank budget
that accommodates critical logarithmic behavior must retain quantitative
neighboring compensation; the uniform Xi estimates remain unproved.
All 111 certified-Xi tests passed; source/input hashes were verified.

## Two-sided neighboring-ratio comparison — 2026-09-20

The [two-sided rank theorem](RH_TWO_SIDED_RANK_TUBE_2026_09_20.md) bounds
both curvature and its rank slope. The lower correction uses a lower
central curvature and upper neighboring curvatures; the upper correction
uses the opposite bounds. Under explicit head and exterior boundary
hypotheses, simultaneous induction preserves the bounds and determinant
positivity. Future neighboring positivity follows inside that induction.

For rational ratio envelopes, each correction inequality reduces to a
degree-at-most-six polynomial on r>=R. Exact nonnegative coefficients in
powers of r-R give sufficient all-rank certificates. On `(1+z/N)^N`,
both polynomials vanish identically for every degree, rank and interior
shift, and the exact determinant formulas supply both boundary tubes.
The method therefore admits zero limiting rank slope, unlike the prior
scalar criteria. No Xi two-sided envelopes or all-shift head/boundary
bounds have been established. RH remains unproved. All 115 certified-Xi
tests passed; artifact source hashes and exact control conditions match.

## Xi shift-two exponential boundary tube — 2026-09-20

The [three-pole refinement](RH_SHIFT_TWO_EXPONENTIAL_TUBE_2026_09_20.md)
proves v_r(2)=delta_r(2)-delta_(r-1)(2)>0.06085 at every rank r>=1,
and t_r(2)<=exp(-0.06085*r). Fresh determinants cover slope ranks 1..59;
the uniform tail from rank 60 has slope lower bound >0.2803876. Its
value and slope errors are controlled geometrically around the shared
model beta*r-log(r+2)-log A, beta approximately 0.34747728.

Integrating the slope-error bounds produces compatible two-sided value
and slope boundary functions for the general comparison over shifts
m>=3. No additional global zero assumption is used. The same existing
exponential tail also excludes every positive rational lower envelope
a/(r+k) at shift two. Thus the rational checker cannot be imposed on
this Xi tail; the new exponential envelopes fit its proved decay. Higher-shift
head and comparison inequalities remain unproved. All 119 certified-Xi
tests passed; base/input/source hashes and the complete bridge match.

## Positive shift-two correction and cumulative gain — 2026-09-20

The [second-difference proof](RH_SHIFT_TWO_CORRECTION_2026_09_20.md)
cancels the common affine pole model before bounding its remainder.
It proves C_r(2)>11/[100(r+2)^2] for every integer r>=1. The finite
bridge covers 1..89; from rank 90 the stronger constants 1/2 and 3/2
bound (r+2)^2 C_r(2) uniformly. The geometric scaled-error ratio is
below 0.799020, so this continuation covers an infinite tail.

The slopes increase strictly to beta and the exact cumulative sum is
beta-delta_1(2), approximately 0.286623351129241. The remaining gain
beta-v_r(2) lies between 1/[2(r+2)] and 3/[2(r+1)] for r>=90.
This supplies stronger shift-two boundary control without assuming
positive t_r(3) or D_r(4). It does not extend to every interior shift;
the existing negative shift-four corrections prohibit such a sign claim.
The uniform interior budget and RH remain unproved. All 123 certified-Xi
tests passed. Six source hashes, the coefficient hash, and the base
certificate hash match the saved artifact; git diff --check passed.

## Rectangular comparison width obstruction — 2026-09-20

The [width theorem](RH_RANK_TUBE_WIDTH_2026_09_20.md) subtracts the
two comparison inequalities and proves
Delta_r^2(h-g)>=2d_m+d_(m-1)+d_(m+1), where
d_j=Phi(h_j)-Phi(g_j)>=0. Any positive width in that triple forces
at least linear subsequent central width growth. Thus sublinear-width
interior tubes are impossible under this comparison, and its rational
specialization admits only coinciding envelopes in each interior triple.
This strengthens an unresolved polynomial check into a proved obstruction
to the proposed family; it does not contradict the exact control or Xi.

An exact error equation identifies the required replacement quantity:
the spatial second difference of the shared nonlinear error H, before
bounding its absolute value. Uniform Xi control of that quantity and
the interior all-rank budget remain unproved. Added exact-fraction
diagnostics and four regression tests; all 127 certified-Xi tests passed.

## Exact correlated-error amplification — 2026-09-20

The [linearization theorem](RH_RANK_LINEARIZATION_2026_09_20.md) derives
the complete spatial spectrum n(n-1), 2<=n<=N, in the repeated-root
control. The corresponding radial solutions are degree-n polynomials.
In particular, an initial curvature error constant across shifts has
derivative response r(r+N)/(N+1). The proof realizes these modes as
derivatives of actual positive-coefficient deformations, with positivity
and differentiability justified separately on each finite rank horizon.
No uniform nonzero perturbation neighborhood is assumed.

This excludes a rank-independent unweighted local Lipschitz estimate
for the control and shows why spatial smoothness alone does not repair
the rectangle obstruction. The spatial polynomials match the classical
Hahn equation; no novelty claim is made for that spectrum. Xi-specific
mode or weighted remainder control is still missing. Four additional
tests verify exact polynomial identities and independent determinant
derivatives; all 131 certified-Xi tests passed. RH remains unproved.

## Forced-mode Green budget — 2026-09-20

The [Green formula](RH_RANK_GREEN_BUDGET_2026_09_20.md) gives the exact
growing amplitude M=a+sum d_k F_k for each repeated-root scalar mode,
where d is its positive decaying companion. When M=0 and |F_r|<=B V_r,
the written proof establishes |e_r|<=B(1-d_r)<=B at every rank. This
retains signed cancellation before taking absolute values and supplies
a conditional response to the previously proved amplification.

The N=2 implementation evaluates infinite moments exactly for rational
prefixes followed by a specified inverse-quadratic tail. It rejects even
a 10^(-12) nonzero balance mismatch as a bounded-response certificate.
This is a control-equation theorem; the Xi reference operator, residual
identification, signed balance, and noncircular boundary control remain
unproved. Four new regression tests passed; the full suite now has 135
passing tests. RH remains unproved.

## Prime-program grid factor and stronger scaling — 2026-09-20

The [grid-tail proof](prime_spectral/GRID_TAIL_SCALING_2026_09_20.md)
factors the finite Fourier profile as P=R*G, where R is the normalized
prime-defined quotient characteristic polynomial and G is the forced
exterior grid product. It proves N/(log cutoff)^2 must tend to infinity
for the unmodified P profiles to converge locally uniformly to Xi.
The proof compares a positive imaginary-axis product lower bound with
Xi's unconditional subquadratic logarithmic growth, using the earlier
forced-zero escape condition first. At critical L^2/N -> alpha, G tends
locally uniformly to exp(-alpha*z^2/(4pi^2)).

An explicit disk bound controls G-1 when L^2/N tends to zero. A new
prime-only evaluator computes R directly, preserving its finite real-zero
property under the existing quotient gates. Neither uniform gates nor
convergence or identification of R with Xi is established. All 19
prime-program tests passed, including four new factorization/bound tests.
No Xi data enter this independent construction. RH remains unproved.

## Prime quotient compactness and coefficient budget — 2026-09-20

The [spectral-sum criterion](prime_spectral/QUOTIENT_COEFFICIENT_BUDGET_2026_09_20.md)
proves |R(z)|<=exp(S|z|^2), S=trace(B^(-2))/2, and bounds the Taylor
tail factorially. Uniform boundedness of S is equivalent to local
boundedness for the gated normalized real-zero quotient family. All-order
Taylor coefficient convergence would imply local uniform convergence;
the first coefficient only gives compactness, not identification with Xi.

Prime-only inverse traces and Newton identities now give certified
coefficient intervals. At cutoff 13, mode-4 and mode-8 quotient polynomials
differ by less than 0.003320983 throughout the unit disk. Their degree-six
Taylor tails are below 1.932e-10 and 7.410e-10. The proof, saved artifact,
and four new tests preserve the finite-only classification. All 23 prime
tests passed; uniform arithmetic spectral sums and coefficient convergence
remain unproved. RH remains unproved.

## Direct prime eigenvector coefficients — finalized 2026-09-22

The [shared-denominator identity](prime_spectral/EIGENVECTOR_COEFFICIENTS_2026_09_20.md)
expresses every quotient coefficient directly through its even eigenvector.
In particular S=(L/(2pi))^2 sum_(n=1)^N (1+2c_n/c_0)/n^2. This makes
the missing uniform compactness condition an explicit O(L^(-2)) signed
weighted eigenvector estimate. No such sequence-wide bound is proved.

For the unchanged cutoff-13 inputs, the mode-8 spectral-sum enclosure is
more than 10^10 times narrower than the inverse-trace enclosure, and the
mode-4/mode-8 unit-disk difference is below 0.003275386. Independent
inverse traces and direct determinant evaluations agree with the new
coefficients. All 27 prime-program tests passed; six source and two input
hashes match the artifact. The result remains finite, and neither
convergence to Xi nor RH is established.

## Positive prime kernels and the weak-convergence target — 2026-09-22

The [spatial-kernel proof](prime_spectral/POSITIVE_KERNEL_2026_09_22.md)
certifies whole-support positivity at cutoff 13 for modes 4 and 8,
including both endpoints. Bernstein coefficients use the exact boundary
normalization to avoid cancellation at the endpoint. The normalized
kernels are even probability densities with variances near 0.0902350
and 0.0621260. Their Fourier transforms are exactly the existing P profiles.

Together with the finite real-zero gates, a uniform variance bound would
give uniform entire bounds and Gaussian probability tails. Weak convergence
to the normalized Xi theta measure would then imply local uniform entire
convergence and the desired real-zero conclusion. The proof leaves that
weak identification, sequence-wide variance control, and uniform gates
explicitly open. All 31 prime-program tests passed, including independent
moment and complex-transform integrations. RH remains unproved.

## Higher prime modes through certified eigenpair isolation — 2026-09-22

The [alternative finite gate](prime_spectral/ISOLATED_KERNEL_2026_09_22.md)
resolves the interval LDL failures at cutoff 13, modes 12 and 16, using
FLINT's certified Rump eigenpairs of the same defining matrix blocks.
Strict spectral separation proves positive, simple even lowest eigenvalues;
nonzero boundary evaluation is checked directly on the enclosed vector.
Both new kernels pass whole-support Bernstein positivity. Their variances
are near 0.0530682 and 0.0489750. No existing source certificate was replaced.

All 35 prime-program tests passed, including agreement with the old mode-4
method and both higher-mode configurations. Both new artifacts' five source
hashes match. The finite variance trend is not a uniform bound, and the
weak limit has not been identified with the Xi theta measure. RH remains
unproved.

## Increasing-support prime audit — 2026-09-22

The [support audit](prime_spectral/SUPPORT_VARIANCE_AUDIT_2026_09_22.md)
certifies whole-support positive kernels at cutoffs 17 and 23, modes 16.
Their variances are near 0.0532823 and 0.0585733, larger than the cutoff-13
value at the same mode count. Cutoff 31 remains unresolved at even-block
certified eigenpair isolation; its odd block is isolated and positive.
No negative-spectrum conclusion follows from the even-block failure.

An independent post-construction target audit computes Xi variance
2*mu_1/mu_0 near 0.0462100 and strict W2 distance lower bounds for the
three finite kernels. Prime inputs remain independent of Xi data. The
variance identity also yields the necessary finite constraint
N+1>=L^2/(2pi^2*M) whenever V<=M. Neither lower bounds nor finite trends
supply the missing upper estimate or weak convergence. All 35 existing
prime tests passed; the two new inputs separately passed the actual gate.
RH remains unproved.

## Low-anchor reference sign audit — 2026-09-23

The [direct frozen-reference certificate](RH_LOW_ANCHOR_REFERENCE_COUNTEREXAMPLE_2026_09_23.md)
proves that the degree-16 reference extended to anchor `a=1` has positive
log-deficit curvature, approximately `0.88353050395877`; it remains positive
at `a=6` and is negative at `a=8`. The defining finite integral and its
first two tilt derivatives were enclosed with Arb balls. A separate direct
theta-moment certificate gives negative true curvature at `a=1`.
The existing uniform negative-sign theorem on `a>=10^6` is unaffected.
An all-anchor negative-sign theorem for this *unchanged reference* is false,
so the lower compact bridge needs the true integral or another reference.
No interior all-rank Xi budget or RH proof follows from this audit.

## Shift three at every rank — 2026-09-23

The [five-pole certificate](RH_UNIFORM_SHIFT_THREE_2026_09_23.md)
adds `D_r(3)>0` and `0<t_r(3)<1` for every integer rank. A new
201-coefficient FLINT certificate resolves five real reciprocal poles;
the geometric determinant error tail starts at rank 82. Certified dual
determinants cover ranks 1..81. The size-four residual expansion keeps
repeated-pole column cancellation and the normalized ratio upper bound
at rank 82 is below `3.586e-11`. This is a fixed-shift theorem under
the documented analytic-numerical trust boundary, not a uniform
interior budget or RH proof.

The [correction refinement](RH_SHIFT_THREE_CORRECTION_2026_09_23.md)
also proves `C_r(3)>1/[10(r+3)^2]` for every rank. Its geometric
error tail starts at rank 137; certified dual determinants bridge all
earlier ranks. The slope increases to a certified positive limit, with
an exact infinite cumulative-gain identity. Negative corrections at
shift four still rule out a uniform nonnegative-correction shortcut.

## Cutoff-31 prime kernel via matrix perturbation — 2026-09-23

The [perturbation proof](prime_spectral/PERTURBATION_KERNEL_2026_09_23.md)
resolves the previous cutoff-31, mode-16 eigenpair isolation failure.
A certified midpoint eigensystem has an even gap near 2.367e-38,
whereas the original interval matrix row-sum error is below 3.779e-71.
A symmetric perturbation bound transfers positive, simple lowest
spectral status and a componentwise eigenvector enclosure. Boundary
normalization is nonzero; every boundary-anchored Bernstein coefficient
is positive. The finite spatial kernel variance is near 0.0646575.

The full 39 prime-program tests passed and the new artifact's four source
hashes match. This removes one numerical certification obstacle but gives
no infinite-path variance bound or weak convergence to Xi. RH remains
unproved.

## Prime strip residual bridge — 2026-09-23

The [strip-transfer theorem](prime_spectral/STRIP_RESIDUAL_TRANSFER_2026_09_23.md)
shows that local uniform convergence of the real-zero finite profiles to
Xi on `|Im z|<1/2` suffices for RH; entire-plane convergence is not
needed for that deduction. It gives an explicit residual-over-gap
bound for an even unit candidate, followed by a Fourier-origin-normalized
profile error on each closed substrip. The norm depends on strip height
as `sqrt(sinh(sigma L)/(sigma L))`, not on the real part of `z`.
The cutoff-13 mode-4/mode-8 finite difference is below `0.293786`
throughout `|Im z|<=2/5`. This neither supplies a prolate candidate
nor proves the uniform residual, spectral gap, or Xi convergence.

## True-theta compact curvature through anchor 8 — 2026-09-23

The [joined coupled cover](RH_COMPACT_THETA_CURVATURE_1_8_2026_09_23.md)
certifies `(log epsilon)'' <= -97765/274877906944` at every real anchor
in `[1,8]`, under the FLINT/Arb and written theta-tail trust boundary.
The new `[3,8]` component has 1,812 positive cells; all three components
join to 2,830 cells with no unresolved gap. This is for the true theta
integral, not the unchanged degree-16 reference, whose negative sign is
false at low anchors. The interval `(8,10^6)` and uniform interior
rank-and-shift budget remain open. RH is not proved.
