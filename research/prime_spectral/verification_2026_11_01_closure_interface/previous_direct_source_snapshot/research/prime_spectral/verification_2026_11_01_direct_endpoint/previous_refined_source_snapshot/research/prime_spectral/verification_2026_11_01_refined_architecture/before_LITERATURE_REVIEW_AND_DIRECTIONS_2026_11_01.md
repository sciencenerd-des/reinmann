# Literature review and next directions (1 November 2026)

Scope: a literature update since the
[24 October review](LITERATURE_REVIEW_AND_DIRECTIONS_2026_10_24.md), and a
ranked list of next directions. **No new theorem, certificate, scan or RH
claim.** All external works below are unrefereed preprints unless stated
otherwise. Summaries come from abstracts and HTML read on 1 November 2026, not
from refereeing; the binding constraints were not re-derived. The one
direction that changes a register entry is preregistered in the
[DH register](RH_DH_DISCRIMINATOR_REGISTER.md) before any development.

## 1. What is new since 24 October

### 1.1 The cubic-theta exponent system has been refined three times

| Work | Date | Boundary | Mechanism | Status |
|---|---|---|---|---|
| OpenAI, 7/8 preprint | 30 Sep | 7/8 = 0.875 | Kubota/Patterson cubic theta, family bootstrap | Lean-checked (v4.34.1); replayed here |
| B. Liu, [arXiv:2610.12234](https://arxiv.org/abs/2610.12234) | 8–12 Oct | 0.874957019… | Re-optimized parameters in the same system | Already audited here (exact scalar replay) |
| Y. Xu, H. Sang, [arXiv:2610.15291](https://arxiv.org/abs/2610.15291) (v2 15 Oct) | 11 Oct | 0.8748867 | **Amplified first moment of the reflected numerator** (from the plain fourth moment, Lemma 18.1 extended to 13/18 ≤ κ ≤ 1), plus a relaxed direct estimate that keeps the per-window decay (ℓ up to 1/5). Two-stage κ chain 3/4 → 29991/40000. | Conditional on the OpenAI analytic inputs. **New to the repo.** |
| "Newton" [New26], cited by Liu 2610.26835 | Oct | Fixed-range barrier ≈ 0.8748866496 | Exact rational certificate for the Xu–Sang system with 29991/40000 ≤ κ ≤ 3/4 | Not located. Known only from Liu's citation. |
| B. Liu, [arXiv:2610.26835](https://arxiv.org/abs/2610.26835) (v2 29 Oct) | 19 Oct | B♭ = 0.874886647039964…, a root of 133488B⁴ − 376596B³ + 384534B² − 167541B + 26231 | Variable-κ refined comparison system with the Xu–Sang numerator. Thm 14.13: B♭ is the **exact infimum** of that system, not attained by finite chains. Runs over F = K(ζ₁₂) and descends by class field theory, claiming the bound for **every finite-order Hecke L-function over every number field**. | Lean "in progress". Covering arbitrary K relies on Part III, which I could not check in the HTML read. |

Two related items:

- **Xu–Sang, [arXiv:2610.17675](https://arxiv.org/abs/2610.17675).** This is a
  matching lower bound for the sextic large sieve: the squared norm is at least
  Q^{7/6−ε} at balanced parameters. It also gives a structured-prime second
  moment bound ≪ Q^{(37−10√6)/6+ε}. The lower bound confirms our
  one-character-alignment observation (24 Oct §8): coefficient-insensitive
  large-sieve inputs are capped. Any gain must use the prescribed
  ideal-Möbius / prime structure. Already cited in the
  [row-density audit](prime_spectral/ROW_DENSITY_AND_CUBIC_OBSTRUCTION_2026_10_22.md).
- **Cureton–Thorner [CT26].** Cited by Liu 2610.26835 for Re s > 31/32 for
  every Dedekind zeta function (Thm 1.1, Cor. 1.2). Not located; cite only
  through Liu.

**Liu's own list of obstruction-changing inputs** (2610.26835 §2.12, as
summarized from the HTML) includes:

- a proved amplification exponent below 5/6;
- larger admissible prime lengths;
- a joint moment estimate for the detecting polynomials;
- better functional-equation or Gram estimates;
- restrictions on the actual critical classes.

Here a(r) = max{1, (1+5r)/6}. **Our conditional H(4/5) target is exactly the
first item.** The 24 Oct localization (only 1.099 ≤ log_U D ≤ 1.19 is needed)
quantifies where in r that input is needed. That localization was certified
in the *pre-Xu–Sang* system (Liu v2, B = 0.874793). It has not been re-priced
in the B♭ system.

### 1.2 Large values and zero density

- **Chen–Gupta–Li, [arXiv:2507.08296](https://arxiv.org/abs/2507.08296)
  (v2 27 Jul 2026).** Guth–Maynard for Dirichlet characters. Hybrid density
  Σ_{χ mod q} N(σ,T,χ) ≪ (qT)^{7(1−σ)/3+ε}, improving Huxley's 12/5.
- **Cossaboom, [arXiv:2609.27715](https://arxiv.org/abs/2609.27715).**
  Guth–Maynard extended to GL₂ coefficients under an ℓ^q condition. Gives
  N_π(σ,T) ≪ T^{5/2(1−σ)+o(1)}. Covers automorphic inductions of Hecke
  characters of quadratic fields.
- **R. Li, [arXiv:2610.18923](https://arxiv.org/abs/2610.18923).** Trilinear
  short-interval sums via Guth–Maynard plus Chen–Gupta–Li.
- **Survey, [arXiv:2607.04632](https://arxiv.org/abs/2607.04632).**

None of these is a large-values theorem for the **sextic residue-symbol ×
ray-character family over Q(ω) with varying ideal conductor**. That is the
form the bootstrap needs. The 24 Oct finding stands: the critical raw
amplitude N^0.6943 lies below the ordinary Guth–Maynard range, and no
transport exists.

### 1.3 Spectral and positivity routes

- No new Connes/Consani/Moscovici result was found after the EMS volume
  (June 2026) and Connes–van Suijlekom (CMP, July 2026). The repo's
  [DH spectral diagnostic](prime_spectral/DH_SPECTRAL_DIAGNOSTIC_2026_10_24.md)
  already moved `weil_ground_state_transform_convergence` to *reformulation*.
- **Zhu, [arXiv:2608.24827](https://arxiv.org/abs/2608.24827)** and
  **Groskin, [arXiv:2607.02828](https://arxiv.org/abs/2607.02828).** Finite
  Weil-form Galerkin truncations. Zhu states that the window-positivity route
  cannot reach RH unassisted, which agrees with the register.
- **Michałowski, [arXiv:2602.20313](https://arxiv.org/abs/2602.20313) (v2).**
  The de Bruijn–Newman kernel Φ(|u|) is certified **not PF₅** via an
  interval-enclosed negative 5×5 Toeplitz minor at (u₀,h) = (0.01,0.05).
  v2 withdrew its global C₅ sign claims. This concerns the *kernel*, not the
  Taylor-coefficient Toeplitz sequence our PF58/PF97 certificates use. It
  does not touch our results. It kills kernel-side total positivity as an RH
  route, which was never active here.
- Jensen and de Bruijn–Newman: nothing new of research grade. Ignore the
  Preprints.org claim "Λ = 0" (Gershon, April 2026). It is unreviewed, and its
  finite hyperbolicity range is far below what the repo already certifies.

### 1.4 Verification status of the quasi-RH

There is still no referee report and no published error. Quanta (19 Oct) and
Science report cautious expert optimism about the human-edited 11/12 version.
The 7/8 Lean proof has independent replays (ours, tomoto0). A GitHub release
(TheRealDubb, 30 Oct) claims another Lean 7/8 replay; it is unverified and not
needed.

## 2. Reading the trend

The exponent system is **saturating**:

- 0.875 → 0.874957 → 0.8748867 → 0.8748866: total movement ≈ 1.1·10⁻⁴ in
  one month.
- Each step is an exact optimum of a slightly enlarged comparison system.
- The repo already proved that the *unchanged direct majorant* has a
  count-free floor of **13/15 ≈ 0.8667**. No count improvement can go below
  that.
- The Xu–Sang change is precisely a change of the numerator / direct side. So
  **the 13/15 floor may not apply to the B♭ architecture, and its floor is
  unknown.**

This is the single most informative open number for the RH question in this
literature. If the averaged-numerator architecture also has a floor > 1/2
under the strongest conceivable family inputs, the metaplectic bootstrap
**cannot reach RH even conditionally**. That would settle the debate that
Sawin and Bloom raised in Quanta. If the floor is 1/2, the input that reaches
it is the precise arithmetic target, and it is DH-separated by construction.

The second observation is competitive. Four groups (Liu, Xu–Sang, Newton,
Cureton–Thorner) are now working on this system. Pure decimal improvements
here will be overtaken within days. The repo's comparative advantage is
exact certification plus DH discipline, not parameter search.

## 3. Directions, ranked

Each direction gives its DH gate. None is an active RH strategy; the
register's global flag stays false.

### Direction A: intrinsic floor of the averaged-numerator architecture (cheap, decisive)

1. **Reconstruct.** Rebuild the Xu–Sang / Liu-B♭ comparison system exactly,
   reusing `liu_exponent_system.py`. Regressions:
   - B₁ = 8748867/10⁷ (Xu–Sang two-stage chain);
   - the B♭ quartic root (Liu Thm 14.13);
   - Newton's fixed-range ≈ 0.8748866496, if [New26] can be located.
2. **Idealize every family input.**
   - Delete all nonprincipal-count constraints (R → its trivial floor).
   - Set the amplification exponent a(r) → 1.
   - Set the fourth-moment / averaged-numerator exponent to its
     Lindelöf-on-average value.
   - Free ℓ subject only to the support/reflection length conditions, which
     are geometric, not arithmetic.
3. **Solve the exact LP / semi-algebraic floor B_ideal**, with a rational
   dual certificate as for 13/15.
4. **Decision.**
   - **B_ideal > 1/2.** This is a certified *method barrier*: the cubic-theta
     comparison cannot give RH under any family moment input. Record it, close
     the endpoint question as `reformulation` for RH purposes, and keep the
     constant as finite strengthening.
   - **B_ideal = 1/2.** The binding idealized input *is* the RH-relevant
     arithmetic target. State it precisely (coefficients, conductor
     uniformity) and instantiate its DH analogue before any further work.
5. **DH gate.** The DH global half-plane analogue is classically false
   (Titchmarsh §10.25). A barrier result needs no DH instantiation, since it
   is a statement about the method. An endpoint target must name the ideal
   Möbius / Hecke-family moment as separator. The b₉₁ − b₇b₁₃ = −1 − κ²
   obstruction is already retained.
6. **Prior art.** Before claiming anything, check [New26], Liu26c and Liu
   §2.12–§14.8. An informal 13/15 discussion already existed (rstation.ai), so
   a public floor discussion for B♭ may too.

### Direction B: re-price the localized H(4/5) target in the B♭ system (cheap)

Stack the 24 Oct localized amplification hypothesis (α = 4/5 only on
1.099 ≤ r ≤ 1.19) with the Xu–Sang numerator, and certify a rational
conditional B < B♭.

- Report how the needed r-band and the (D/U)^{1/30} gain move. Liu names this
  input type in §2.12 but does not localize it, so a localization is useful
  to anyone trying to prove it.
- This is **conditional finite strengthening only**. Write it as a short
  sensitivity note, with prior-art checks against Newton and Liu26c, if the
  user wants a timely Zenodo item. DH status is unchanged: the replacement DH
  moment family remains uninstantiated.

### Direction C: does Xu–Sang's structured-prime moment already supply the localized gain? (reading task)

Xu–Sang 2610.17675 proves a structured-prime second moment
≪ Q^{(37−10√6)/6+ε} for sextic characters. The 24 Oct note needs a gain
(D/U)^{1/30} for the **ideal-Möbius inverse polynomial**, which is a
different coefficient vector.

- Read their normalization and decide whether the method (Gauss second moment
  plus a column-scale comparison) adapts to Möbius coefficients of length
  U^{1.1–1.19}.
- If it does, the localized target becomes a provable lemma. That would be
  the first genuinely new arithmetic estimate this repo could contribute. It
  is still finite strengthening, and still DH-separated only through Möbius
  structure.
- If it does not, record why. The likely reason is that a prime-supported
  vector is not a Möbius vector, since Möbius has square-free composite
  support.

### Direction D: Lean toolchain catch-up (infrastructure)

The repo is on Lean v4.30. The external 7/8 proof is on v4.34.1, PNT+
(Hadamard factorization, `riemannXi` of order ≤ 1) on v4.35.0, and Liu's
forthcoming B♭ Lean will likely be on one of these.

A port or upgrade would let the folded-Xi product identity use PNT+ Hadamard
directly. It would also let PF58 import the 7/8 theorem in one toolchain
rather than a separate replay. Shared prerequisite, no DH issue. Watch the
root-import CI gap noted in project memory.

### Direction E: Carathéodory–Fejér in Lean (carried over, low priority)

This was Direction 3 of 24 Oct. The spectral route it served is now a
reformulation. Keep it only as a Mathlib-quality contribution.

### Not recommended

- Restarting the parked cubic row-density route before the Dunn/Platt
  replies arrive.
- New Toeplitz PF ranks, Weil windows or Jensen scans as RH strategy. These
  remain reformulations; finite strengthening is still fine.
- Porting the 199-page 7/8 Lean proof.
- Chasing decimal improvements of B by parameter search.
- Kernel-side PF (Φ) questions. Michałowski settles PF₅ negatively, and it
  is off-route.

## 4. Suggested order

Do A first. It is a few hours of exact scalar work on existing code, and its
answer decides whether B and C matter for RH at all, or only as finite
strengthening.

- If A gives B_ideal > 1/2: write the barrier up, demote the endpoint, and
  treat B/C as optional finite-strengthening work.
- If A gives 1/2: C becomes the main arithmetic task, preceded by a DH
  family instantiation as AGENTS.md requires.

Outreach is the user's call. Liu §2.12 overlaps directly with the localized
target, so a short note to B. Liu after A/B may be worthwhile. The
Dunn and Platt threads are still pending.

## 5. Honest assessment

No work surveyed reaches Re s = 1/2 or offers a mechanism that plausibly
does. The cubic-theta bootstrap is the only recent DH-separated progress, and
it is converging to a constant near 0.87489. The open RH-relevant question it
leaves is whether its architecture has a floor above 1/2 under ideal inputs.
That is cheap to settle with tools this repo already has.
