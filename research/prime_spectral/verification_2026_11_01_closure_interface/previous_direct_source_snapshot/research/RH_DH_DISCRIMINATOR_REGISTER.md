# Standing Davenport–Heilbronn research gate

`RH_DH_DISCRIMINATOR_REGISTER.json` records the active RH-strength targets,
their DH analogues, retained counterexamples, and missing arithmetic
inequalities. `AGENTS.md` makes this a standing check before developing a
proposed RH-separating step. The register is a research discipline, not a
certificate that every DH instantiation has already been built.

| Target | DH information retained | Arithmetic gap / disposition |
|---|---|---|
| All-rank ordinary Toeplitz PF | Negative rank 664, shift 44; second negative band 1536–1972. These are tested witnesses, not a globally first failure. | Von Mangoldt sign/support alone has not been turned into a Schur sign theorem. Reformulation. |
| Weil positivity on every window | Full-form rational negative witness at C=7873/256, using the actual odd gamma/conductor and every DH logarithmic-derivative coefficient. | The complete Schur/coupling inequality is missing. Reformulation; finite-window engineering remains useful. |
| Every classical Jensen degree/shift | No first failing degree has been located in the n! normalization. The known off-line zero obstructs the full criterion, but is not a located finite Jensen witness. | No arithmetic discriminator. Reformulation; do not restart a grid scan. |
| Green paired budget | A same-domain, same-form DH realization has not been supplied. The off-line zero is a control datum, not a completed Green-form certificate. | Missing relative paired budget. Current Xi theorem is an RH equivalence, not a strategy. |
| Same-height phase hypothesis | Not instantiated for actual DH. The corrected paper already gives exp(i*z)*z*(z-1) as a generic failure of the proposed phase-crossing inference. | The paper explicitly does **not** assert a Lean equivalence of H_theta and RH; the bridge itself is missing. |

The DH Toeplitz family uses ordinary coefficients mu_n. Classical Jensen uses
n! mu_n. The full DH Weil form uses its logarithmic-derivative coefficients,
not either Taylor sequence. Its negative window endpoint is only an upper
bound on the support needed for a negative witness. Positive finite sections
do not give a lower bound on the full-window transition.

The complete height-340 atlas supports the classical sufficient PF435 sector
bound, so a globally first failing ordered-minor rank, if phrased by rank
alone, lies between 436 and the known rank-664 witness. The first failing
shift or arbitrary minor inside that range is unknown. This is a classical
inference from the certified atlas and factorization, not a DH instantiation
of our Lean Xi theorem.

Zeta's c_n=Lambda(n) are nonnegative and supported on prime powers. The retained
DH arithmetic control first violates the sign condition at n=3, and the support
condition at n=6. Those differences identify data an arithmetic proof could
use; neither proves a positivity inequality. Earlier sign/support ablations
are not substitutes for a zero-side identity.

A shared necessary lemma is not refuted merely because DH satisfies it.
Entireness, functional symmetry, genus-zero factorization, finite-rank sector
criteria, complementary minors and generic jump estimates belong in that
category. A sufficient RH argument that would also prove the false DH
analogue must be rejected. A route with no quantified arithmetic separator is
classified as a reformulation. Missing implementations remain explicitly
uninstantiated rather than being counted as passes.

The 7/8 half-plane is a finite strengthening, not an RH-strength target.
Its **global DH analogue is false**: Titchmarsh, second edition (1986),
[§10.25, pp. 282–285](https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf),
proves infinitely many zeros with Re(s)>1 for the same mod-5 function used
here. The coefficient period and displayed kappa agree with
`davenport_heilbronn_control.py`. This is classical literature evidence,
not a newly certified zero ball; the first such height remains unknown here.
The original Davenport–Heilbronn papers are
[JLMS 11 (1936), 181–185](https://doi.org/10.1112/jlms/s1-11.3.181) and
[307–312](https://doi.org/10.1112/jlms/s1-11.4.307).

The zero at real part 0.8085 and the height-340 atlas do not themselves
falsify 7/8; the separate classical theorem does. The external metaplectic
proof uses multiplicative Hecke/Mobius/Gauss-sum structure absent for DH.
That identifies the arithmetic obstruction to transferring its argument;
Euler-product signs or support alone are still no positivity proof. The
external 7/8 statement has now been rebuilt and standard-axiom audited on
Lean 4.34.1; see the [replay record](prime_spectral/EXTERNAL_SEVEN_EIGHTHS_REPLAY_2026_10_21.md).
The independent [finite-width certificate](prime_spectral/PF58_CERTIFIED_2026_10_22.md)
now proves PF58 on Lean 4.30. The global seven-eighths theorem remains a separate
Lean 4.34.1 reproduction. Its receipt's local-PF58 flag records that earlier
snapshot. The [height-32 finite-width certificate](prime_spectral/PF97_CERTIFIED_2026_10_22.md)
now also proves unconditional PF97 on Lean 4.30, checked at `b4ec4a3` by all
34 jobs of run 39733278869. Neither finite certificate imports the external theorem.

The finite ranks 58 and 97 are below the classical DH PF435 sector guarantee
already retained above. These controls are therefore shared finite strengthening,
with no new arithmetic discriminator proposed. No new DH scan or first-failure
claim accompanies these certificates.

## Short-family arithmetic candidate (source audit, 22 October 2026)

The `short_family_mean_square_row_density` entry now has a named structural
arithmetic separator and a quantified open estimate; see the
[row-density/cubic audit](prime_spectral/ROW_DENSITY_AND_CUBIC_OBSTRUCTION_2026_10_22.md)
and the [specialist review draft](prime_spectral/ROW_DENSITY_SPECIALIST_REVIEW_DRAFT.md).
The coefficients are ideal Mobius coefficients on Q(sqrt(-3)), not Xi Taylor
coefficients. The exact Hecke/Mobius-to-theta identity is the proposed arithmetic
input; multiplicativity alone is no cancellation proof.

For the assumed two-term extraction bound, the unrestricted optimum is
sigma=k/(k+1) at h=k/(k+1). In the actual source range h>1, the infimum is
1-1/(2k). Thus cubic rows would give 5/6 in the old range; 3/4 additionally
requires the unproved H=D^(3/4) range. At k=1 every h>=1/2 minimizes; h=1/2 is
not necessary. The literal order-one residue-character family is principal,
so neither a new varying family nor its mean square follows from this algebra.

The unchanged cubic substitution fails before a new exponent can be claimed:
sextic p^3 rows retain a quadratic twist; switching to cubic characters leaves
a squared cubic Gauss coefficient after Mobius-weighted Poisson, equivalently a
sextic Gauss coefficient needing a different coefficient/index realization. The existing
ordinary-theta reflection would also leave a cubic character, losing the
quadratic large sieve. These are gaps in that substitution, not impossibility
results for every metaplectic method.

A DH cancellation analogue **can** be stated using its Dirichlet inverse b.
The exact identity b_91-b_7*b_13=-1-kappa^2<0, with 7*13 coprime to 2*3*5,
refutes its identification with the multiplicative ideal-Mobius/Hecke input.
The verifier checks the inverse convolution through 91 with integer polynomial
arithmetic. A square-root reciprocal-DH bound for all smooth weights would also
contradict its classically known zeros with real part greater than 1. No first
failing cancellation scale is located, and a replacement DH metaplectic family
remains uninstantiated. The register's global flag for an active RH strategy
with a **proved** separating inequality remains false.

## Two literature-derived entries (24 October 2026)

Both entries are `uninstantiated`. No computation accompanies them. See the
[literature review](LITERATURE_REVIEW_AND_DIRECTIONS_2026_10_24.md).

`weil_ground_state_transform_convergence` is the Connes–Consani–Moscovici
spectral-triple route. The Connes–van Suijlekom real-zero theorem uses only a
real even form with a simple isolated even minimum. DH ground-state
transforms therefore have only real zeros too. By Hurwitz they cannot
converge to Xi_DH, which has the off-line zero 0.8085+85.70i. So the whole
RH content is the comparison of ground states with the prolate candidate,
and that comparison must fail for DH. No DH ground state has been computed.
Until a residual/gap term is found that is controlled for zeta and fails for
DH, the route is a reformulation.

`metaplectic_bootstrap_endpoint` is the B=1/2 endpoint of the OpenAI/Liu
exponent system. Liu's arXiv:2610.12234 reaches B≈0.874957. There the binding
character-count exponent is R*=2/3, which b cannot relax. Formally
B(ell)=11/12−ell/4, so B=1/2 needs ell=5/3. The DH half-plane analogue is
classically false. The proposed separators are the Hecke-family moments, but
the map from those exponents to B, and its value under the large-values
conjecture, has not been computed. The constant itself remains a finite
strengthening (`quasi_rh_seven_eighths`).

### Spectral experiment preregistration (24 October 2026)

The DH negative control is specified before implementation in
[DH_SPECTRAL_PREREGISTRATION_2026_10_24.md](prime_spectral/DH_SPECTRAL_PREREGISTRATION_2026_10_24.md).
It uses the conductor-5 odd prolate candidate and all DH log-derivative
coefficients. The suggested C~13.6 transition is heuristic. Finite projected
residual/gap is supplemented by second-minus-Rayleigh clearance and rank
and precision checks; it is not a full-operator estimate or RH discriminator.

### Spectral negative-control outcome (24 October 2026)

The route `weil_ground_state_transform_convergence` is now **reformulation**.
The [finite DH experiment](prime_spectral/DH_SPECTRAL_DIAGNOSTIC_2026_10_24.md)
instantiates the missing control. At C=35 the certified finite minimum is odd
at N=64 and even at N=96,128. At the latter ranks the rounded prolate trial
is nearly orthogonal to the ground despite residual/gap below 0.005: its
Rayleigh quotient is above the second eigenvalue. This identifies a failure
of the comparison diagnostic, not a proved zeta-specific arithmetic term.
The C~13.6 transition, full-operator behavior and globally first failure
remain unestablished. Exact prolate residuals are not certified here.

### Direction 2 gate before development (24 October 2026)

The [Liu v2 exponent audit](prime_spectral/LIU_EXPONENT_SYSTEM_2026_10_24.md)
will reconstruct the scalar count and bootstrap before substituting new
large-value inputs. Original ideal Mobius/unweighted detector coefficients,
sextic twists, common-character normalization and all length conditions must
be retained. The DH global half-plane analogue is false; its reciprocal
coefficient defect is already recorded. A new Hecke-family count estimate
and its DH implementation remain uninstantiated. The formal ell=5/3
substitution is outside the current length domain; no active RH strategy
or new analytic estimate is claimed. The parked row-density route stays parked.

### Direction 2 phase 1 outcome (24 October 2026)

The [exact Liu v2 scalar ledger](prime_spectral/LIU_EXPONENT_SYSTEM_2026_10_24.md)
reproduces 7/8 and both algebraic endpoints, verifies the uniform central
polynomial inequality and all 29 auxiliary reserves, and replays eight
bootstrap steps. A positive rational LP dual proves a count-free direct
floor of **13/15**: changing only count constraints in the unchanged full
direct architecture cannot reach RH. This is not a new analytic theorem.
The critical raw amplitude is N^0.694291677..., and the ordinary GM/CGL
theorems supply no proved transport to the required varying-conductor ideal
family. Moment sensitivities are hypothetical inputs, not achieved bounds.
The endpoint route remains `uninstantiated` as a new arithmetic strategy;
the existing DH reciprocal obstruction is retained. No old manifest was
updated, and the parked row-density route was not restarted.

## Direction 2 continuation: conditional long inverse moment (preregistered)

Retain the same ideal norms, ideal-Mobius inverse coefficients, common
sextic/ray twists, deleted Euler factors, zero extensions and smooth-weight
conventions. Price the explicit hypothesis that for sixth-power-free
q_u~U and inverse length D=U^r, 1<=r<=3/2, the long mean square improves
from U^((1+5r)/6+epsilon) to U^(1/5+4r/5+epsilon), uniformly with the
original polynomial height loss. Keep all short moments unchanged and use
kappa=3/4, supplied by the previous 7/8 bound.

Before arithmetic development, the next check is a uniform rational scalar
certificate below Liu's boundary, including the full direct majorant,
small/intermediate/large norm ranges and principal Euler restriction.
This is conditional sensitivity analysis. The proposed mean square is
unproved and its DH analogue is uninstantiated; the route stays
`uninstantiated` and its separating inequality stays null. The retained DH
reciprocal nonmultiplicativity witness prevents the verbatim ideal-Mobius
transfer but proves no new cancellation estimate.

The coefficient audit additionally tests the stronger, arbitrary-bounded-
coefficient variant by aligning squarefree-supported coefficients with one
family member. Such a failure would limit coefficient-insensitive
large-sieve substitutions; it would not refute the prescribed ideal-Mobius
moment, and would not itself be an RH discriminator.

The conditional scalar check is now complete at B=874793/1000000 under
H(4/5), with kappa=3/4 from the preceding 7/8 bound. Exact positive
coefficients prove the central endpoint uniformly, the full direct
majorant agrees, and thirty relevant fixed-parameter reserves are
positive. The same parameters fail with the original long moment.
The needed gain is (D/U)^(1/30); an arbitrary-coefficient extension is
excluded by one-character alignment, and cutoff rebalancing of ua^6
alone cannot earn this gain. See
[the conditional moment note](prime_spectral/LIU_CONDITIONAL_MOMENT_2026_10_24.md).
No new arithmetic estimate or zero-free theorem follows. Classification
and the null separating inequality are unchanged.

## Direction 2 localization preregistration

Keep the phase-2 rational B=0.874793 geometry and every arithmetic
convention. Enclose the zero/amplitude classes where the original
alpha=5/6 count fails its endpoint comparison. Price a localized
replacement there using R_req=1-[C0+(1/2+ell)delta+ell*x*delta+sigma]/h
for strict rational sigma>0, and identify which long inverse detector
lengths actually require improvement. No arithmetic estimate has been
proved; the replacement DH moment family remains uninstantiated and the
separating inequality remains null. This is a reduction of the existing
conditional target, not a new active RH route or parked cubic scan.

Localization is now certified: the original count handles the complement
of 1/3<=delta<=47/100, 21/50<=x<=1/2. Inside that box, it suffices to
prove either the alpha=4/5 inverse moment only for
1099/1000<=r<=119/100, or a direct class-count gain of 1/850 in the
original exponent. These are different unproved sufficient hypotheses.
Exact polynomial and Bernstein coefficients, including the original
moment below the proposed band, retain the conditional scalar B=0.874793
payoff and strict margins. Neither the box nor band is claimed minimal.
See [the localization note](prime_spectral/LIU_LOCALIZED_TARGET_2026_10_24.md).
There is no new arithmetic theorem or DH family implementation; the
route remains uninstantiated and its separating inequality remains null.

A further audit tests the optimistic mixed-moment extension obtained by
combining the original inverse-moment closure at enlarged range U^h with
the same sixth-power averaging cost U^(1/6+5h/6). It is not a new mixed
moment theorem; the check asks whether that proof architecture could
improve the long count even if all additional losses were absent.

The selected-prime extension audit fails even optimistically: enlarging
the old inverse range forces h>=r+2z, while the same sixth-power cost
and prime amplitude give excess >=(5/3-2delta*x)z>=(359/300)z in the
local box. Its best selected length is z=0. This rejects that proof-cost
substitution, not the unproved arithmetic targets or a different joint
large-values estimate.

## Architecture-floor preregistration (1 November 2026)

Historical planning text follows. Its uncertainty about the retained direct
side is superseded by the clarified relaxation and outcome below.

The [1 November literature update](LITERATURE_REVIEW_AND_DIRECTIONS_2026_11_01.md)
records two refinements of the same cubic-theta system. Xu–Sang
(arXiv:2610.15291) replace the pointwise direct numerator by an amplified
first moment of the reflected numerator, giving 0.8748867. Liu
(arXiv:2610.26835) proves B♭=0.874886647… is the exact infimum of the
resulting variable-kappa system. The certified 13/15 count-free floor
concerns the **unchanged** full direct majorant. It is not known to apply to
this changed numerator architecture.

Before any further development of `metaplectic_bootstrap_endpoint`, the next
check is the exact floor B_ideal of the averaged-numerator architecture under
idealized family inputs:

- delete all nonprincipal counts;
- amplification exponent a(r)→1;
- Lindelöf-on-average numerator;
- support, reflection and length conditions retained.

The Xu–Sang B₁ and Liu B♭ values are required regressions. If
B_ideal>1/2 has a rational dual certificate, it is a method barrier. If
B_ideal=1/2, the binding input becomes the candidate arithmetic target, and
its DH family analogue must be instantiated first. Nothing is computed yet.
The classification stays `uninstantiated`, the separating inequality stays
null, and no DH moment family is implemented.

### Direction A: clarified relaxation before development (1 November 2026)

Source inspection finds that the Xu–Sang numerator change is on the high
side; its Section 3 retains the direct low side and ell<=1/5. Liu v2
Section 14.8 explicitly retains the same restriction. Before calculation,
define a stronger relaxation: delete every high-side/count/moment,
principal-assembly and bootstrap-licensing constraint, retaining only the
direct comparison. Check both balanced lengths and the existing full
free-length Gram/reflection maximum. Its exact scalar infimum is only a
lower bound for a full idealized family-input system. No numerical value
is newly certified at this preregistration step. This is a method audit,
not a new RH-separating lemma; the route remains uninstantiated and the
separating inequality remains null. Any later endpoint arithmetic target
still requires an instantiated DH analogue.

### Direction A outcome (1 November 2026)

The [refined comparison audit](prime_spectral/LIU_REFINED_ARCHITECTURE_2026_11_01.md)
corrects the preregistration's premise: the averaged reflected numerator is
on the high side; Xu–Sang Section 3 and Liu Section 14.8 retain the direct
comparison and ell<=1/5. Deleting all high-side/count/moment, assembly and
licensing constraints gives a direct-only relaxation with exact minimum
**13/15**. Balanced length arithmetic and a free-length positive rational
dual certify it. It is a lower bound for the full idealized family system,
whose exact optimum is not computed. Thus the RH endpoint is excluded
within the retained direct Gram/reflection bound and signal normalization;
this does not exclude a different direct estimate or cubic-theta method.

The Xu–Sang two-stage and Liu four-stage rational scalar certificates are
reproduced with continuous polynomial certificates and positive reserves.
Critical-class elimination reproduces the B-flat quartic and its relevant
root; the full optimality and analytic proofs are not replayed. Newton's
DOI is identified from Liu's bibliography but its full text is not checked.
A dedicated prior-art check finds the same Xu–Sang floor in the 17 October
rStation discussion; no novelty is claimed. The broader route remains
`uninstantiated`, its separating inequality null, and its DH moment family
unimplemented. No new RH strategy, arithmetic estimate or publication.

## Direct-side endpoint pricing preregistration (1 November 2026)

Price B=1/2 for the SAME normalized signed Xu–Sang cubic-theta probe,
with its original cusp/Gauss coefficients, fixed finite subset compensation,
Eisenstein ideal norms, Hecke character zero extensions, excluded primes,
and disjoint physical prime windows. The proposed necessary direct target
is |J_eta(Z)| << Z^(1/2-(4+b)/6+epsilon) for every epsilon>0. Its separate
remainder and nonvanishing correction obligations are not assumed proved.

Audit length-cap changes with support positivity retained, and distinguish
the arithmetic probe from a Gaussian inverse Mellin transform of 1/L. For
the latter, instantiate DH with its original period-5 coefficients and
Dirichlet-convolution reciprocal, Gaussian exp((s-5/6)^2), and multiplier
1. Test against a retained certified off-critical DH disk; no new scan.
The actual DH metaplectic probe is missing: that target is uninstantiated,
not a separator. No arithmetic separating inequality is specified. Any
principal-model equivalence must state its growth/inversion assumptions;
sufficiency together with a remainder does not prove equivalence for J.
No whole-method closure, GRH equivalence for J, new arithmetic lemma, or
novelty claim is preregistered. Scalar pricing and implication audit only.

### Direct-side endpoint audit outcome (1 November 2026)

The [pricing and DH implication note](prime_spectral/LIU_DIRECT_ENDPOINT_2026_11_01.md)
finds the necessary actual-probe exponent -(1+b)/6. At the balanced
direct-only optimum the required gain is 11/30 (11/60 becomes -11/60).
Cap-only extension requires ell=5/3, incompatible with positive/support
lengths even if the reflection penalty is removed.

The Gaussian principal reciprocal model is explicitly instantiated for DH
using its original period-5 coefficients and convolution reciprocal. A
retained simple off-line disk is freshly replayed in 768-bit Arb, with a
nonzero Gaussian pole; its B=1/2 growth analogue is false. The universal
principal-model target is a reformulation under the note's explicit
reciprocal-growth and inversion hypotheses. This is not the actual theta
probe J_eta. Neither direction of GRH equivalence for that probe is proved;
a DH metaplectic construction is still missing. Linear combination of
Hecke probes fails to supply the reciprocal-DH principal identity. The
actual-probe target stays `uninstantiated`, its separating inequality null,
and no arithmetic work or whole-method closure is claimed. Earlier
verification manifests are unchanged; the preceding refined packet is
replayed against snapshotted source inputs because the shared registry has
now evolved. No publication, CI, new zero search or novelty claim.
