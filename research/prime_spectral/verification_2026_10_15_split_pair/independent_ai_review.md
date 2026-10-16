# Independent AI review — 15 October 2026

Reviewer: a separate AI agent, reviewing the manuscript and numerical evidence independently of its authoring agent. This is not human peer review or external analytic review. This report binds the source revision and data listed below; later revisions require a delta check.

## Outcome and scope

No mathematical error found in the split-pair theorem, the first-negative **shift-44 column** claim, or the revised small-offset subsection. Suitable in this reviewed scope for a clearly labelled computational preprint after final artifact checks. This does not approve publishing or substitute for human review. The final 1,450-coefficient calculation and any extended column are still pending and are **not** validated here.

The two earlier minor requests are addressed: the reproduction section lists the new split-pair scripts/records, and Alexandersson is cited in its published EJC form. The abstract, subsection 7.1, discussion and assistance disclosure accurately distinguish finite evidence, mathematical statements and AI review.

## Mathematical review

The split-pair theorem's local residue subtraction is valid for the stated real entire function: after removing the s+1 simple principal parts, the reciprocal is analytic on the closed radius-R disk. The Vandermonde/residue leading coefficient is correct and nonzero. Expanding by columns makes repeated pole directions vanish, and k remainder columns have the stated normalized exponential upper bound. The smaller all-pole terms are also exponentially suppressed. Both rational and irrational rotation cases give infinitely many positive and negative terms; the rational orbit has at least three points and cannot have all cosines zero.

I consulted the primary published Alexandersson paper, Theorem 1 and section 3.2, rather than relying on an attribution label: https://doi.org/10.37236/2651 (full EJC PDF). It supports the classical finite Widom–Schur mechanism. The manuscript supplies its own entire-function remainder argument rather than assuming that finite-product asymptotics automatically extend.

The 43 smaller real folded zeros identify shift 44. PF435, the previous grid through rank 520, and the new targeted column cover every preceding rank. Thus rank 664 is the first negative member of **this column**. The manuscript expressly leaves other shifts and non-solid minors open. The leading phase and period scale are correctly presented as asymptotic diagnostics, not finite-rank error estimates.

## Independent arithmetic checks

Using Python 3.12 / python-flint 0.8.0, I replayed the initial cached column at 33,024 bits: all 143 ranks 521–663 positive; all 14 ranks 664–677 negative. Direct 44-by-44 determinants at ranks 520, 521, 663, 664 and 677 agree. These checks share the cached coefficient enclosures and FLINT backend; they are not an independently implemented special-function evaluation. Input/source hashes inspected for the column and asymptotic records match.

The small-offset mixture is explicitly distinguished from a single character-label control. The exact rational weights sum to one and preserve conductor, odd gamma factor, root-number-one symmetry and first coefficient. Its recorded complete atlas and higher-precision replay contain 113 line zeros and five reflected off-line pairs: 123 zeros through height 160. I inspected that recorded replay and its provenance; I did not personally rerun its full contour here.

I freshly reassembled the exact negative witness at 2,176 bits for N=192, C=593/16: the quotient is approximately -7.3795602480288235512e-18 and overlaps its stored enclosure. I additionally reassembled the N=256 witnesses at C=37 and C=593/16: quotients approximately -1.9559386439695117761e-18 and -7.3795602480288235512e-18, both strictly negative and overlapping the stored enclosures. These runs regenerate the closed geometric matrices and evaluate the stored exact rational vectors, without relying on stored pivot signs.

All declared input/search-record hashes in the mixture atlas replay, search summary and attribution record match their current files. Exact rational interval comparison confirms that the lowest off-line quartet strictly dominates each other enclosed negative quartet.

## Small-offset interpretation

The held-out probe has b approximately 0.03, gamma approximately 31.4336216845, negative support upper bound C=37.0625 and r approximately 0.5698713. It is 7.19 percent above the previously recorded descriptive C prediction, within the earlier 16–20 percent leave-one-out errors. The original seven-point fit is not refitted. This is useful calibration, **inconclusive between proposed b-to-zero limiting behaviours**: one finite-offset upper bound cannot establish or exclude divergence, positive finite sections give no full-support lower bound, and other off-line pairs remain. The N=256 negative witness at C=37 makes the lower-bound limitation concrete.

The lowest quartet contributes approximately -1.11965e-13, more than 100 times the next individual negative quartet. The finite total is approximately -1.15183e-14, whereas the full geometric quotient is approximately -7.37956e-18. Omitted terms are material. Dominance within the atlas is evidence, not an isolated-pair detection theorem or a negligible-tail proof. The revised manuscript says this explicitly.

## Remaining limits

This review does not reprove every original atlas, every old grid entry, the full seven-control calibration or the Lean audit. It does not assess a completed Liu audit, Zenodo artifacts or the final PDF layout. A future extended column and regenerated coefficient input need a final sign/wording/provenance check. No human review has occurred through this AI report.

## Reviewed-file SHA256 hashes

Paths are relative to the worktree repository root. Code files were inspected; the 1,450-coefficient generator was reviewed as source only, with no completion claim.

- `paper/dh_controls_paper.tex`
  `35fb2100d33205320ad6af032d0338c9fc38f7756974fd1c4cd757c7245c19de`
- `experiments/prime_spectral/dh_split_pair_column.py`
  `17bd0de724ec0c43add4cd1b2e5348f87edd740ef64391bf9485abe6e7b88120`
- `experiments/prime_spectral/dh_split_pair_asymptotic.py`
  `588899d5f7e8c45409716cf81fde2288f715a51ab2f2f87a4f1597308d551e3d`
- `experiments/prime_spectral/dh_split_pair_coefficients.py`
  `791f4a712a7f9eb4a3e0c17a7092e1495cafc86c1237bee4207a4751151916ef`
- `experiments/prime_spectral/near_line_mixture_control.py`
  `f2a5e0de193fc744b1c7f2570ec0efcb1c6a21277615d7b4e6e5595c4200f856`
- `experiments/prime_spectral/near_line_window_calibration.py`
  `7f86645f994f60998d7898958102afcd604871df5fa526f6c52c7e93d317730b`
- `experiments/prime_spectral/near_line_attribution.py`
  `b925d923e8659f1834bb0b635ab45aede0ff1596a26eccdfa9c15aa037653273`
- `research/prime_spectral/verification_2026_10_15_split_pair/column44_rank521-677_32768bits.json`
  `0b04f3f1afd150bc48c9599c2d3dcd191235068dc7ec15db50a8b45eb2f32026`
- `research/prime_spectral/verification_2026_10_15_split_pair/split_pair_asymptotic.json`
  `c79112ffc5aaa21213f341573ae89860f09c89a3b1437e00933c6dda4e22f530`
- `research/prime_spectral/verification_2026_10_15_split_pair/near_line_mixture_definition.json`
  `7cec7cfe196ac00bbd77c379655039c17c06c1f7999ef31deae37ec83daac22f`
- `research/prime_spectral/verification_2026_10_15_split_pair/mixture13_H160/atlas.json`
  `90bf2f330dc9bec73b52ef7abceb6718ca82e2b7b662d335dbc9614fe98005ad`
- `research/prime_spectral/verification_2026_10_15_split_pair/mixture_atlas_replay.json`
  `501e0d1f2ae78c70e6090f44b73df150283f58f27a25b2f51d7f74103fb1606b`
- `research/prime_spectral/verification_2026_10_15_split_pair/mixture13_windows/search_N192_2048bits.json`
  `96a602621f8a299692d1cbe203587c417de07f67e0eea72d17e130ab7f5919ec`
- `research/prime_spectral/verification_2026_10_15_split_pair/nearline_attribution.json`
  `038b2721b2db3fb4f97d4c0bd51b59432d48eaab03ae9d0861111381947240cb`
- `research/prime_spectral/verification_2026_10_15_split_pair/near_line_forecast.json`
  `666b3f5de024b0f6ea88eaf29eb1edb9f0c2c69db0f9d357704d6acc68d24e6b`
- `research/prime_spectral/verification_2026_10_15_split_pair/mixture13_windows/C593_16_N192_2048bits.json`
  `7f7946e87691d4057bfc107c6eddf34e7161597d5778f57b70f63ce3d0a09cdd`
- `research/prime_spectral/verification_2026_10_15_split_pair/mixture13_windows/C37_N256_2048bits.json`
  `a721441a3fb8210cfc29008930d41bd382a25ee7406d37d40a581f0ba0c28f6f`
- `research/prime_spectral/verification_2026_10_15_split_pair/mixture13_windows/C593_16_N256_2048bits.json`
  `701460be1a759ec2cfd63aea6d5e49fd5e6a42eb3ea61b8beaf12a0ba8a67239`
- `research/prime_spectral/verification_2026_10_12_sector/dh_rank430-520_shift0-200_32768bits_coefficients.json`
  `bf1d312730ec861c00f9e1ecc84d703ef0aa725c36419d01c257e98b94ef8b16`

## Final extended-column delta review — 15 October 2026

This section supersedes the earlier pending status of the fresh 1,450-coefficient build and extended column. Earlier findings and their bound source revision are preserved above.

The fresh Dirichlet-L path supplies 1,451 strictly positive ordinary coefficient enclosures, with all 721 shared old enclosures overlapping. I independently replayed all 880 rank signs from those fresh inputs at 33,024 bits: ranks 521–663 positive, 664–1099 negative, and 1100–1400 positive. I additionally directly evaluated the 44-by-44 determinants at ranks 663, 664, 1099 and 1100, recovering signs positive, negative, negative and positive. All declared source/input hashes in the fresh coefficient, extended column and extended replay records match. The recorded extended replay also includes direct ranks 520, 521, 677 and 1400; those additional fresh-input direct evaluations were inspected rather than personally rerun here.

The revised abstract, proposition, proof and plot caption accurately describe the full negative band and its return to positivity. The first-negative claim remains restricted to shift 44, and the shared FLINT/Arb backend limitation is explicit. The asymptotic cosine is correctly separated from finite-rank certificates. The reserved DOI/date agree with the local unpublished-draft receipt and metadata; I did not access or publish the remote draft. No mathematical issue found in this delta.

### Release-script acceptance finding

The provenance verifier and deterministic packager were inspected for concrete acceptance defects; no further blocking issue found within that source review. The upload script currently validates the local repository via run(False), but accepts any supplied --bundle path without validating the archive against that current manifest. Server MD5 and size checks only confirm the bytes uploaded, so a stale or arbitrary archive could be accepted even while current repository checks pass. This needs a pre-upload archive inventory/member-hash check against the current manifest, including manifest bytes and README, before draft mutation. This is an engineering acceptance issue, not a numerical proof defect. No network actions were performed by this reviewer.

The review is mathematically complete in its stated scope, but release-script acceptance remains pending this guard and its read-only check. Human review and final PDF/archival checks remain separate.

### Extended-delta hashes

- `paper/dh_controls_paper.tex`
  `686e032de4e9f778e9b588a890f38c96ea62c956b636e08f8ce1567e3660c751`
- `research/prime_spectral/verification_2026_10_15_split_pair/dh_coefficients_1450_32768bits.json`
  `2b6a28d04cbdb0eddf3af391dbd0c1d483f47797553be6fe3958bd0f95a552e2`
- `research/prime_spectral/verification_2026_10_15_split_pair/column44_rank521-1400_32768bits.json`
  `68824bd90920e3f30f75d6a63fe7bda2585723795bfc1a31d56bc7d1e7a27b1c`
- `research/prime_spectral/verification_2026_10_15_split_pair/column44_extended_replay.json`
  `0f61629415749708054616c5623461314fdc5f5bc558a5bb50db9019803904fa`
- `research/prime_spectral/verification_2026_10_15_split_pair/zenodo_draft_receipt.json`
  `753c10ef249f2013bcc301ac79fd4f73e27667990bcf87b496a47b996a4d4f4b`
- `paper/zenodo_dh_controls.json`
  `ca6d3d31c3b722dcdc33e9d197c2bfaf03cd87735b6379bf2fefa76e38566a84`
- `experiments/prime_spectral/replay_dh_split_pair_extended.py`
  `70bf785c247f380c4df164152f363b7fbf0bf0296fea91799299242e3159efcc`
- `experiments/prime_spectral/verify_split_pair_round.py`
  `97cebb1feabc534f1190970491665707fd43bbf940b8c3b831a58a215bf62c6d`
- `experiments/prime_spectral/package_dh_controls.py`
  `2e5e097aa2b5096726b176d718c903cc10f5d6223bad64f32d7ded6feb635931`
- `experiments/prime_spectral/prepare_dh_zenodo_draft.py`
  `fbec3582cb9969faf5a21f59edaee1e69e7dfa590d9835d22801bd17b41472d6`
- `experiments/prime_spectral/plot_split_pair_column.py`
  `e8e620c8cdc40621ba0d721ea8cfdd634333e50362e589887bb4bd8c19355ebf`

## Release-guard resolution and review freeze — 15 October 2026

The upload acceptance finding above is resolved by source inspection. The upload entry point now calls read-only verify_bundle immediately after current-manifest validation, before reading credentials or making its first HTTP request. The archive verifier checks exact inventory/cardinality, file-only safe member names, each member SHA256, the current manifest bytes and the root README. Duplicate member names cannot pass the cardinality/inventory checks. Consequently a stale/arbitrary bundle no longer passes merely because the current repository and server MD5 checks succeed.

The provenance/package/upload delta was inspected; no further concrete acceptance defect found in this review scope. The authoring agent will run the focused valid/stale-bundle tests before the final package freeze. Those tests are not claimed as personally performed by this reviewer. No remote request, publication or draft mutation was performed by this reviewer.

This review report is now stable for final artifact hashing. The extended-column mathematical claims and small-offset scope pass the bounded independent AI review described above. Human review, final PDF checks, final deterministic-package verification and user-controlled publication remain separate.

### Freeze source hashes

- `paper/dh_controls_paper.tex`
  `686e032de4e9f778e9b588a890f38c96ea62c956b636e08f8ce1567e3660c751`
- `experiments/prime_spectral/package_dh_controls.py`
  `2e5e097aa2b5096726b176d718c903cc10f5d6223bad64f32d7ded6feb635931`
- `experiments/prime_spectral/prepare_dh_zenodo_draft.py`
  `fbec3582cb9969faf5a21f59edaee1e69e7dfa590d9835d22801bd17b41472d6`
- `experiments/prime_spectral/verify_split_pair_round.py`
  `6882d58f607b934742b498c1d4c7038ae573fd472ce6566068e2ab7c0732a9ef`
