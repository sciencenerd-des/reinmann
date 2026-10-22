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
snapshot. PF97 is a finite-width candidate awaiting its full CI gate.

The finite ranks 58 and 97 are below the classical DH PF435 sector guarantee
already retained above. These controls are therefore shared finite strengthening,
with no new arithmetic discriminator proposed. No new DH scan or first-failure
claim accompanies these certificates.
