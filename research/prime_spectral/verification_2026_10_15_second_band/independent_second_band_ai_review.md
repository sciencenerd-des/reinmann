# Independent second-band technical AI review — 15 October 2026

Reviewer: a separate AI agent from the authoring agent. This is a technical AI check, **not human review**. The user's required human read before publication remains pending. This report does not authorize publication. No publication, external contact or remote draft mutation was performed by this reviewer.

## Result

No mathematical or numerical error found in the reviewed positive-coefficient extension, second-band certificate or nearby-shift certificate. The checks below bind the files listed at the end. Mixture-path jobs and any subsequently revised manuscript are outside this review.

## Analytic coefficient extension

The existing written positive-theta lemma gives strictly positive ordinary folded Taylor coefficients. Its Mellin integral has a positive, faster-than-exponentially-decaying kernel, so every even Taylor moment is positive and the folded entire function has mu_n >= 0. For any real R>0,

    mu_n * R^n <= sum_k mu_k * R^k = F(R).

Thus 0 <= mu_n <= F(R)/R^n is valid. No fitted decay estimate or contour sup-norm assumption is needed. With R=2^20, the generator correctly evaluates

    F(R) = Lambda(1/2 + sqrt(R)) / Lambda(1/2)

using real completed values whose positivity is gated. It retains the 1,451 prior coefficient enclosures and encloses the next 600 coefficients by the positive bounds. Those are broad rigorous enclosures, **not 600 newly evaluated Taylor coefficients**.

I independently verified using exact rational endpoints that every appended interval contains zero and its upper endpoint is at least the stored upper endpoint of F(R) divided by R^n. I freshly evaluated F(R) at 33,280 bits and confirmed overlap with the stored ball. The prior coefficient input and source hashes match. The formal reciprocal coefficient through index n depends only on the original coefficients through n; no unknown tail beyond index 2050 is implicitly set to zero for the tested determinants.

The mathematical dependency is the written positive-theta proof and the classical DH normalization. This proof is not Lean formalized by this check. The arithmetic checks share FLINT/Arb and the same CharacterControl special-function path.

## Second-band replay

The preregistered local record predicts entry in ranks 1535–1539 and last negative rank in 1970–1974. I independently replayed all 600 signs at ranks 1401–2000, shift 44, using the supplied coefficient enclosures at 33,280 bits. Every cell resolves; ranks 1401–1535 are positive, ranks 1536–1972 are negative, and ranks 1973–2000 are positive. There are 437 negative cells.

I additionally evaluated direct 44-by-44 determinants from the reciprocal coefficients at both boundaries:

- rank 1535: positive, approximately 9.39671720995991e-83768;
- rank 1536: negative, approximately -1.16182182384201e-83823;
- rank 1972: negative, approximately -3.02252656963367e-107793;
- rank 1973: positive, approximately 1.06758253599698e-107847.

All four exclude zero and overlap the independently replayed condensation values. Both observed boundaries fall in their recorded forecast intervals. The registration is local timestamp/hash evidence, not an independently public timestamp. Agreement does not supply a finite-rank asymptotic remainder theorem or an exact integer period.

## Nearby-shift replay

I independently replayed all 1,620 cells for shifts 40–48 and ranks 521–700 at 33,280 bits. Every cell resolves. The only negative cells are shift 44 at ranks 664–700 (37 cells). I additionally directly evaluated ranks 663 and 664 at every one of the nine shifts. They are positive except shift 44 at rank 664, which is negative.

This verifies the specified rectangle and its lack of an earlier negative cell. It does not identify the globally first failing Toeplitz minor, establish PF663 or cover arbitrary row/column selections. Historical grid results and the split-pair theorem retain their previously stated scope.

## Provenance and limitations

All declared source/input hashes in the preregistration, coefficient-extension and two scan records match the current files. The manuscript hash below binds only the source containing the written positive-theta dependency as read here; this report does not certify any later second-band manuscript revision or final PDF layout. No pending mixture outcome or human-review completion is inferred. Publication must await the separately requested human read and the user's publication action.

## Reviewed-file SHA256 hashes

Paths are relative to the worktree repository root.

- `research/prime_spectral/verification_2026_10_15_second_band/preregistered_forecast.json`
  `3573621a6018433771cacc270b2aa8845c2a85696ec86ce65edd6c200d9134d0`
- `research/prime_spectral/verification_2026_10_15_second_band/dh_coefficients_2050_cauchy_32768bits.json`
  `b35d42f26feb463a33cfbf88df78050cb9280ef9bea2d4871e2657bc637b4969`
- `research/prime_spectral/verification_2026_10_15_second_band/shifts44-44_ranks 1401-2000_33024bits.json`
  `d36b1f359a91efff183946961ccc666d7938408538b3219cecde2c8365c1ee7c`
- `research/prime_spectral/verification_2026_10_15_second_band/shifts 40-48_ranks 521-700_33024bits.json`
  `a74edbc9c74a3c31733af15f69041d8eacb1a63a0e3e3787bc9622dfaf5b91d8`
- `experiments/prime_spectral/dh_cauchy_coefficient_extension.py`
  `5b14c5480d9b254e21f2c3638485dfd84fd7b87f0981f5c50fce2c850afd6935`
- `experiments/prime_spectral/dh_targeted_followup_scan.py`
  `bb395749909f8873f309a8ca0ffafab6b13835a5b1d27d28f2e535d39fdd4f31`
- `experiments/prime_spectral/dh_split_pair_column.py`
  `17bd0de724ec0c43add4cd1b2e5348f87edd740ef64391bf9485abe6e7b88120`
- `experiments/prime_spectral/character_zero_atlas.py`
  `8a918f78c685a864e860d436eb2b654673d5f46a7968e28e60a2e8bb88230dab`
- `research/prime_spectral/verification_2026_10_15_split_pair/dh_coefficients_1450_32768bits.json`
  `2b6a28d04cbdb0eddf3af391dbd0c1d483f47797553be6fe3958bd0f95a552e2`
- `paper/dh_controls_paper.tex`
  `6b7358defe384fd0d21bf0d7fd16828298f2bccc5c5d452305a94facee00fb74`

## Collision-path and final manuscript delta review — 15 October 2026

This bounded technical AI delta reviews the three completed path controls, the revised second-band/tail paragraphs, subsection 7.2, related-work scope and release wrappers. It does not satisfy the author's required human read. Human review remains pending, and publication remains gated on that read and the author's Publish action.

### New numerical evidence

The three recorded complete atlases each contain 123 upper-half-plane zeros through height 160:113 critical-line zeros and five reflected off-line pairs. Their complete-contour/root replays are recorded at 320/640bits. I inspected these records and their source/input provenance; I did not personally rerun the three full contour counts. I freshly reran the simple-root Rouché gate for each lowest off-line root using the existing 512-bit local-disk routine. Each radius 1e-80 disk is resolved, and every reflected-pair separation exceeds 0.0079. No unresolved near-collision disk is being accepted by these checks.

I independently reconstructed all six exact endpoint witnesses, regenerating the geometric matrices at 4352bits and evaluating their rational vectors. Each quotient is strictly negative and overlaps its stored enclosure:

| target offset | N 192 C | N 192 quotient approximately | N 256 C | N 256 quotient approximately |
| --- | --- | --- | --- | --- |
|0.015|39.5625|-1.886368344223751e-19|39.515625|-2.881504185226286e-19|
|0.008|41.28125|-2.150907074320004e-19|41.2421875|-1.871456462452406e-20|
|0.004|42.90625|-1.930408551281652e-21|42.875|-1.713198723121561e-20|

The normalized common-degree coordinates 0.6083124640,0.6347402523 and 0.6597263391 match 2*pi*C/(13*gamma). Relative to the original offset 0.03 point, the measured coordinate rises 15.7676percent. The four-point descriptive fit C=37.29608813+2.88553527*log(0.03/b), RMSE 0.22156869, agrees with the rounded manuscript coefficients. The original seven-control fit is not refitted. The small N 192/N 256 endpoint differences assess finite-family resolution, not full-support positivity or a minimum-support bracket.

Exact-rational interval comparisons confirm that the lowest enclosed quartet is the largest individual negative contributor for every new N 192 witness. Each finite total differs materially from its geometric quotient (by more than 100times the quotient magnitude). The paper correctly leaves infinite-tail cancellation, isolated-pair causation and the true b-to-zero limit open. This finite path does not prove boundedness, divergence or an asymptotic minimum-support law.

The initial recorded test failure was Python's 4300-digit integer parsing limit on trusted 32768-bit certificate endpoints; that diagnostic is preserved. The corrected test explicitly lifts that parser limit and its three substantive tests pass. The numerical evidence above was additionally checked by this reviewer; no arithmetic success is inferred from the original failed log.

### Revised manuscript scope

The final source says both second-band edges fall inside their previously recorded local forecast intervals, with nominal errors(-1,0), no phase/frequency refit, and no independently public timestamp claim. The positive-coefficient tail proof matches the already-reviewed analytic extension. The tested-cell scope remains explicit: rank 664 at shift 44 is first within the declared DH contiguous-minor sets, not globally first or a PF 663 assertion. The stale 'no rectangular grid' and unqualified 'every tested minor' sentences were corrected to cover the fixed column, specifically requested neighboring strip and historical grid precisely.

Subsection 7.2's counts, exact cutoffs, rounded coordinates, endpoint quotients, disk resolution and fit all match the records. Its cautions exclude a limiting-law, minimum-support or universal-exchange claim. The abstract/discussion retain these boundaries. The Liu paragraph agrees with the existing audit report's distinction between A retained-factor reconstruction, B clean rebuild, immutable frozen source and the explicit macOS runtime layout adaptation. This delta does not newly rerun Liu's computations or independently re-prove its analytic dependencies; it verifies that the paper reports the bounded audit scope and avoids a human-review claim.

### Release-wrapper source inspection

The new verifier checks immutable prior scientific artifact hashes, with an explicit list of mutable paper/document files; historical full-paper manifests remain historical. The new packager routes the current manifest through the previously checked exact archive inventory/member-byte guard. The update wrapper invokes current-manifest and bundle checks before credentials or HTTP requests, requires an unpublished draft, verifies returned upload checksums/sizes and final remote inventory, and has no publication endpoint. No new concrete acceptance defect was found by this source inspection. I performed no HTTP request or external action. Final PDF/render checks, actual package verification/upload and remote receipts remain the authoring agent's separate work.

Across the new round's JSON records, I independently checked 721 declared source/input/search-record hashes; all match. This count excludes mutable manifest/release receipts. The final source/data hashes below bind this review revision. No remaining technical correction is requested within this limited AI review scope. **The human-review publication gate remains unsatisfied.**

### Collision-delta reviewed-file SHA 256 hashes

- `paper/dh_controls_paper.tex`
  `e2113814e3a45c6e0113c17d8abb624f00146a2e170d0a2bb45bc8a600abcd4b`
- `research/prime_spectral/verification_2026_10_15_second_band/collision_path_dataset.json`
  `9d43ae4e7e1e46677d44ead59fc287921322bebd61d2c4b778b34878013b78b8`
- `research/prime_spectral/verification_2026_10_15_second_band/forecast_assessment.json`
  `8237b8512e0a71f38f79f7a1045becf89d27b20efce73b0c1e2e34aebd94c72a`
- `research/prime_spectral/verification_2026_10_15_second_band/tests.log`
  `7fd241a7c445725460d5200fff7a7fbbded956d5a3256c083037dbf6af6b3a42`
- `research/prime_spectral/verification_2026_10_15_second_band/tests_initial_digit_limit.log`
  `df0d535aadaad85135ec9fa8217b9d1dd87a5422473055d0a9516c53a48b5a56`
- `research/prime_spectral/verification_2026_10_15_second_band/b015/definition.json`
  `bf972cbea22f7bdc7f3f2b2edebe5a4c0f5716367dac0f0afd7c24922f9481ea`
- `research/prime_spectral/verification_2026_10_15_second_band/b015/atlas_H160/atlas.json`
  `d0ad7d272e45258a8c319e8342377bc6c2c2215f03e129850b3f726849723910`
- `research/prime_spectral/verification_2026_10_15_second_band/b015/atlas_replay.json`
  `3905db6cf47de39fbd4039f8cc1bac142b3267759853eea49479afaa6ebef5f1`
- `research/prime_spectral/verification_2026_10_15_second_band/b015/window_search.json`
  `2633a5f9d304d06f142d79623863e8df4a2101eb411b06b2cf8b94b50a7e72f6`
- `research/prime_spectral/verification_2026_10_15_second_band/b015/resolution_N256.json`
  `b5deb5976ffaa9337abd94ab7a698b7bc699b4315b5b2335f4bd5674efb95cb4`
- `research/prime_spectral/verification_2026_10_15_second_band/b015/attribution.json`
  `ced8bc157c10fb397ab4de12325c47edf3afe93aee58f89b576fb6e9cc181afc`
- `research/prime_spectral/verification_2026_10_15_second_band/b015/windows/C633_16_N192_4096bits.json`
  `8c968abb14cb879e0a6ffcee29686978629b48ff27f16ad018f4f50f0ee611d4`
- `research/prime_spectral/verification_2026_10_15_second_band/b015/windows/C2529_64_N256_4096bits.json`
  `3a41be0c2d640fad823537a11d4e72d5582431fbefc62df587cda2f5ca7e693e`
- `research/prime_spectral/verification_2026_10_15_second_band/b008/definition.json`
  `e889ff5241440787e50ecf2faec4ce235385ddfaf6ee8a40cbf2f42b3b49b713`
- `research/prime_spectral/verification_2026_10_15_second_band/b008/atlas_H160/atlas.json`
  `3fa807852dcb878c9d3f10ad5a502f1d8da89922fb117eb9ebbeba34ede35b06`
- `research/prime_spectral/verification_2026_10_15_second_band/b008/atlas_replay.json`
  `ecce9208f1fa1ae9fd0b74835e399779b0e6f09df48c6f57e9aef27e11800160`
- `research/prime_spectral/verification_2026_10_15_second_band/b008/window_search.json`
  `5681210182033c87377799ccb7d99815206c370e55833ab5fd19f1bd1ec9f867`
- `research/prime_spectral/verification_2026_10_15_second_band/b008/resolution_N256.json`
  `ea4004fcda9c1d7ed5bd6a259c9db93dec0dcf5b158cee4091ba8aa4b8b45148`
- `research/prime_spectral/verification_2026_10_15_second_band/b008/attribution.json`
  `7dbff4cfdd704c0948e1ad343e7f12045ac9da6411f3c177169aa77c2aad7f9c`
- `research/prime_spectral/verification_2026_10_15_second_band/b008/windows/C1321_32_N192_4096bits.json`
  `199a88567fb02c9dd8b2f25f6ca3250d5aecd686db461a2253e9b4f95ea1cfbf`
- `research/prime_spectral/verification_2026_10_15_second_band/b008/windows/C5279_128_N256_4096bits.json`
  `1f5a8ac16526b9f08192249486705da666db05abefea1281629bca406a2f825c`
- `research/prime_spectral/verification_2026_10_15_second_band/b004/definition.json`
  `304c7a253c35f2b4ef652d560a3b49fa0adf1208453e53fec5ae0f83e73cda3c`
- `research/prime_spectral/verification_2026_10_15_second_band/b004/atlas_H160/atlas.json`
  `c2d515d389604bd4248d58e3a165c084607dd26ad0c291df55044c4e70251b93`
- `research/prime_spectral/verification_2026_10_15_second_band/b004/atlas_replay.json`
  `fb5c27abebf02acd7a1513bfd157b21559adfbc1af22d11267ef8b88bb0cc5d5`
- `research/prime_spectral/verification_2026_10_15_second_band/b004/window_search.json`
  `8e0f33c8e959671b7275a586f8d2b0b0714bc912ac227688f01714499404ef2e`
- `research/prime_spectral/verification_2026_10_15_second_band/b004/resolution_N256.json`
  `a2bb02be4c478a9af5b28c3365d8302bc023e2d89bb2f2a508e3921611499a73`
- `research/prime_spectral/verification_2026_10_15_second_band/b004/attribution.json`
  `bfb2eebd149cdb569ef165aff54acc01fe8e1ed2361712abd6bc242261a6e02b`
- `research/prime_spectral/verification_2026_10_15_second_band/b004/windows/C1373_32_N192_4096bits.json`
  `b379e7166b8df60ab45e9fbe250c28a3ee764891a0a0caa0a26d6a29aeaed8fb`
- `research/prime_spectral/verification_2026_10_15_second_band/b004/windows/C343_8_N256_4096bits.json`
  `859b8be8d700649aa6728ba5a5ca5e3472a0739e0e385d098837a6924f0888ef`
- `experiments/prime_spectral/near_line_mixture_path.py`
  `db70cac087cb374cd163b90f666409d2c239164babee1b1daf9281c282ddd5ea`
- `experiments/prime_spectral/mixture_path_resolution.py`
  `fba885ba286f8421df31b1c78552f57c2bbafed790256822620d01cdbeda0277`
- `experiments/prime_spectral/attribute_mixture_path.py`
  `12cd2577117957179e921eb991fc7c84a2f53fc57978c876e3986f700398ff1e`
- `experiments/prime_spectral/build_collision_path_dataset.py`
  `1135a42fdf4b2f75af1587f5a151b56022bef4705736f7dfc130433dc0adf7a8`
- `experiments/prime_spectral/test_second_band_and_path.py`
  `d27e346a82718d76c1c49d9f25a7d81308fee8dd98d56f72f6c349013561164f`
- `experiments/prime_spectral/assess_second_band_forecast.py`
  `c425426df9dc88bb5c6b4566fcc836367b5f60ee56af3e859a75aac94e6aba0d`
- `experiments/prime_spectral/verify_second_band_round.py`
  `ac64d94038d4021857782f48381440f48cc4afd53fd1fd85ac26d3e7f1a54d55`
- `experiments/prime_spectral/package_second_band_revision.py`
  `ccbee84d2e1bf09e4c7bdae5d8d460295c5848132cb1178f40a17def2d3d0440`
- `experiments/prime_spectral/update_dh_review_draft.py`
  `fe0b5319ad89ae59fe791c9fe48154367c489c16a83f8a1bb7853c5ad773cc0d`
- `experiments/prime_spectral/package_dh_controls.py`
  `2e5e097aa2b5096726b176d718c903cc10f5d6223bad64f32d7ded6feb635931`
- `research/prime_spectral/LIU_FROZEN_RELEASE_AUDIT_2026_10_15.md`
  `4f59b4e3dba81b435831c8bed84668e87d24704cb5c99e213a14661b6d52b958`
- `paper/DH_CONTROLS_READINESS.md`
  `14aa1112d74ffe2c67b229356d71cfa48d4d70fff5edf7ef7a25df7db286351b`
- `paper/HUMAN_REVIEW_REQUEST.md`
  `2a7eb874c9e5cf097d7bd9fdef66afd4205aec5437438b012b8c5c16f56e94ca`
- `paper/LIU_REPLAY_NOTE_DRAFT.md`
  `7e38f17c7bd9aa5d555c74710b8e30f7aa82cde6bef4855d9df93fbaf463ab44`
