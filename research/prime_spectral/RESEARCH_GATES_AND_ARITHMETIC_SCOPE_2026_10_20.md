# DH-first research gates and the arithmetic bottleneck

This round separates finite formalization from an RH strategy. No current
RH-strength route in the register has a proved quantitative arithmetic
separator. Shared necessary lemmas can still be useful; a sufficient step that
would prove the false DH conclusion is rejected.

| Direction | Concrete result | Remaining boundary |
| --- | --- | --- |
| Standing DH gate | `AGENTS.md`, five-target JSON register and executable provenance check | First global failures and the Jensen/Green/phase DH implementations are not invented |
| Alternate 11/12 argument | Reconstructed sixth-power extraction conditional on the central arithmetic mean square; exact two-term optimizer checked | Not a reproof of the central mean square; unchanged extraction cannot approach 1/2 |
| Per-prime endpoint source | Exact two-endpoint jump factorization; DH-first finite bands confirm N^-1 leakage and N^-3 after subtraction for a linear vector | Full Schur energy, the new directions' couplings and complement coercivity remain unproved |
| Small-shift corner | Exact ordinary-coefficient rank-three negative minor, while the corresponding real power-sum formula is positive at every positive order | A scalar trace sign cannot replace a Schur sign identity; no zeta-specific identity is supplied |
| Target B / PF43 | Related proof chain pushed through 150537b; main hosted build and root audit pass | Eleven shards and final rectangle assembly were still pending at this round's receipt |
| Height-32 calibration | Two Lean theorems give PF97 from the proved low bound plus an explicit width obligation | No height-32 exclusion certificate; critical-line zeros must be permitted |
| External 7/8 contract | One-file adapter and pinned external replay runner | Adapter not rebuilt on v4.34.1; local PF58 retains its named external input |
| Formalization release | Seven-page revision candidate compiled and visually checked, with PNT+ attribution and separate source pins | Hosted all-job gate and complete publication-file verification remain required |

## Mathematical decisions

The alternate 11/12 exponent is fixed by sparse sixth-power row extraction
after granting the mean square. The unchanged bound has exponents
`1/2+5h/12` and `1-h/6`; their maximum is at least 6/7 for every h, and its
infimum over the actually proved h>1 range is 11/12. This stops parameter
retuning of this extraction as an RH strategy. It does not rule out new
arithmetic input. It is separate from the independent report's roughly 0.8745
row-density extrapolation for the different 7/8 proof.

The endpoint experiment does **not** establish the proposed kill criterion
that every comparison must pay the full prime-comb cost A_L. Its jump constant
contains squared arithmetic weights. Removing the two endpoint profiles
improves the linear-vector source's regularity, but applying the shift operator
to the added profiles creates further breakpoints. A finite correction is not
yet a closed comparison operator. A candidate next lemma must bound the actual
complete Schur energy on the form domain, rather than only a source norm.
It must be tested against the retained negative DH window.

The corner counterexample is the cubic
`(1+z)(1+z/3+z^2/9)`. Its positive-order inverse-zero power sums are at least
1/3, but its shift-two rank-three determinant is -23/729. Lean proves the
real formula's bound and the exact sequence determinant; the explanatory
complex-root identification is not a separate formal theorem. Generic Schur
identities and a prime-side formula for individual power sums do not control
the mixed character weights. No semicircle limit is promoted to such a sign
identity.

## Verification and release scope

Both new Lean modules compile, including fresh source elaborations. A separate
audit checks their five public theorems using only `propext`, `Classical.choice`
and `Quot.sound`. They remain outside the current default import; the current
root build and its 2,608-row guard also pass. The historical checkpoint chain
replays successfully with exact historical root-file overlays, preserving all
old manifests. The numeric probes are floating diagnostics, not certificates.

The source/PDF of the old published formalization are unchanged. The second
version is in `paper/formal_split_pair/v2/`, and all seven pages were rendered
and inspected. It accurately describes the classical low rectangle and PF43,
the restricted standalone split-pair theorem, upstream attribution, and the
absence of a formal DH atlas. It explicitly labels its hosted rectangle gate
as pending. `prepare_formal_rectangle_release.py` refuses packaging until the
exact fourteen hosted jobs are successful and the manuscript and visual
receipt are current; it does not publish or create an external draft.

The already authorized closeout monitor follows
[run 39470397281](https://github.com/sciencenerd-des/reinmann/actions/runs/39470397281)
at `150537bf1d94eced1c22db7660f9c32936372831`. The older serial run is superseded.
New owned commits are held locally while this run is active, so a push cannot
cancel its expensive shards. The monitor now retains the subsequent human
authorization to release the formalization after the all-job gate and complete
file verification. No email, reviewer follow-up or Liu note is authorized or sent.

The detailed derivations are in `QUASI_RH_EXTRACTION_BARRIER_2026_10_20.md`,
`WEIL_ENDPOINT_JUMP_FACTOR_2026_10_20.md`,
`CORNER_POWER_SUM_OBSTRUCTION_2026_10_20.md` and
`FINITE_HEIGHT_PF_PLAN_2026_10_20.md`. The checksum-bound evidence is under
`verification_2026_10_20_research_gates/`. No forecasting, Toeplitz grid scan,
arithmetic ablation, D2 exact count or D6 induction was restarted.
