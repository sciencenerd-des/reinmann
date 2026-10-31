# Literature review and next directions (1 November 2026)

Scope: a literature update since the
[24 October review](LITERATURE_REVIEW_AND_DIRECTIONS_2026_10_24.md), and a
ranked list of next directions. The original review was literature-only.
**Subsequent Direction A audit:** see the
[exact scalar reconstruction](prime_spectral/LIU_REFINED_ARCHITECTURE_2026_11_01.md).
It corrects the architecture-floor discussion below; no new analytic theorem
or RH claim is made. All external works below are unrefereed preprints unless stated
otherwise. Literature summaries come from abstracts and HTML read on 1 November 2026,
not from refereeing. The subsequent scalar audit re-derives the retained
direct bound, rational endpoint certificates and quartic regression, but
does not reprove the external analytic inputs or full optimality theorem. The one
direction that changes a register entry is preregistered in the
[DH register](RH_DH_DISCRIMINATOR_REGISTER.md) before any development.

## 1. What is new since 24 October

### 1.1 The cubic-theta exponent system has been refined three times

| Work | Date | Boundary | Mechanism | Status |
|---|---|---|---|---|
| OpenAI, 7/8 preprint | 30 Sep | 7/8 = 0.875 | Kubota/Patterson cubic theta, family bootstrap | Lean-checked (v4.34.1); replayed here |
| B. Liu, [arXiv:2610.12234](https://arxiv.org/abs/2610.12234) | 8–12 Oct | 0.874957019… | Re-optimized parameters in the same system | Already audited here (exact scalar replay) |
| Y. Xu, H. Sang, [arXiv:2610.15291](https://arxiv.org/abs/2610.15291) (v2 15 Oct) | 11 Oct | 0.8748867 | **Amplified first moment of the reflected numerator** (from the plain fourth moment, Lemma 18.1 extended to 13/18 ≤ κ ≤ 1), plus a relaxed direct estimate that keeps the per-window decay (ℓ up to 1/5). Two-stage κ chain 3/4 → 29991/40000. | Conditional on the OpenAI analytic inputs. Two-stage scalar certificate now reconstructed in the Direction A audit. |
| "Newton" [New26], cited by Liu 2610.26835 | Oct | Fixed-range barrier ≈ 0.8748866496 | Exact rational certificate for the Xu–Sang system with 29991/40000 ≤ κ ≤ 3/4 | DOI located in Liu's source bibliography: [10.5281/zenodo.23414581](https://doi.org/10.5281/zenodo.23414581). Full text not retrieved; no independent replay. |
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
- **Correction from the Direction A source audit:** the averaged reflected
  numerator changes the **high side**, while Xu–Sang Section 3 and Liu
  Section 14.8 retain the direct comparison and ell <= 1/5. Therefore the
  **13/15 floor still applies when that direct side is retained**.

Deleting every high-side/count/moment and assembly constraint gives a
stronger, explicitly defined direct-only relaxation with exact minimum
13/15. Any idealized family-input system retaining the same direct bound
has boundary at least that large; its exact full optimum is not computed.
This excludes reaching 1/2 in that specified scope, including finite chains
and their limits. A different direct estimate or normalization is outside
the certificate. A public Xu–Sang discussion already states this floor
([17 October post and discussion](https://rstation.ai/r/riemann_hypothesis/posts/15));
no novelty is claimed. A binding constraint in any new system would be a
candidate target, not automatically a DH discriminator.

The second observation is competitive. Four groups (Liu, Xu–Sang, Newton,
Cureton–Thorner) are now working on this system. Pure decimal improvements
here will be overtaken within days. The repo's comparative advantage is
exact certification plus DH discipline, not parameter search.

## 3. Directions, ranked

Each direction gives its DH gate. None is an active RH strategy; the
register's global flag stays false.

### Direction A: retained-direct-side floor (completed scalar audit)

The [audit note](prime_spectral/LIU_REFINED_ARCHITECTURE_2026_11_01.md)
records the exact scope, proof and reproducible receipt.

1. **Reconstructed:** the Xu–Sang two-stage chain and Liu's four-stage
   rational chain. Polynomial completed-square certificates cover the full
   endpoint rectangle, with positive scalar and row-extension margins.
2. **Algebraic regression:** the critical-class elimination yields Liu's
   B♭ quartic and isolates its relevant root. The global tangent-family and
   optimality proofs were not independently replayed. Newton's DOI is
   identified through Liu's bibliography; its full text is not checked.
3. **Relaxation:** delete all high-side and assembly constraints, retaining
   the direct Gram/reflection majorant and its signal normalization. Its
   exact minimum is **13/15**, witnessed by balanced lengths; a positive
   rational dual independently checks the free-length version. This is a
   lower bound for a full idealized family system, whose exact optimum
   remains unknown.
4. **Decision:** RH is excluded through changes to high-side family inputs
   while retaining this direct comparison. The endpoint branch is closed
   in that scope. This does not exclude changing the direct estimate itself.
5. **DH gate:** this scalar method barrier needs no DH moment family. Any
   new arithmetic target still requires a precise inequality and an
   instantiated DH analogue. The broader route remains uninstantiated.
6. **Prior art:** a dedicated lookup finds the same Xu–Sang direct-side
   13/15 observation in the 17 October rStation discussion. No novelty claim.

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
  would still be finite strengthening. Möbius structure alone would not
  establish a DH discriminator; its precise inequality and analogue would
  still have to pass the research gate.
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

Direction A's retained-direct-side barrier audit is complete. B and C are
optional finite-strengthening tasks, with their arithmetic estimates still
unproved. Neither can reach RH through high-side changes while this direct
comparison remains fixed. A different direct-side target would need new
preregistration and DH analysis; no such route is opened here.

Outreach is the user's call. Liu §2.12 overlaps directly with the localized
target, so a short note to B. Liu after A/B may be worthwhile. The
Dunn and Platt threads are still pending.

## 5. Honest assessment

No work surveyed reaches Re s = 1/2. The published refined comparison has
an asserted exact boundary near 0.87488665. Our scalar audit confirms that
its retained direct side has a 13/15 floor even after all high-side and
assembly constraints are discarded. This closes the endpoint question for
that frozen direct comparison, not for every future cubic-theta method.
The exact optimum of a full idealized family-input system remains unknown
and is unnecessary for this exclusion. No new arithmetic estimate, RH proof
or novelty claim follows.
