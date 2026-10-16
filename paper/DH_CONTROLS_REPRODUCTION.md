# DH-controls preprint: reproduction

This supplement accompanies *How sensitive are finite RH criteria? Certified Davenport–Heilbronn controls*, Biswajit Mondal, October 2026. It includes editable LaTeX, the current PDF, experiment sources and compact certificates. Calibration fits are descriptive. A negative rational trial certifies a support upper bound; a positive finite section does not certify a full positive window. AI review is disclosed and is not human peer review.

## Environment and checks

From the extracted supplement root, use Python 3.12 with python-flint 0.8.0, NumPy and mpmath. For example:

```
uv run --with python-flint==0.8.0 --with numpy --with mpmath --python 3.12 python experiments/prime_spectral/verify_figure_revision.py
uv run --with python-flint==0.8.0 --with numpy --with mpmath --python 3.12 python experiments/prime_spectral/test_split_pair_round.py
uv run --with python-flint==0.8.0 --with numpy --with mpmath --python 3.12 python experiments/prime_spectral/test_near_line_control.py
uv run --with python-flint==0.8.0 --with numpy --with mpmath --python 3.12 python experiments/prime_spectral/test_second_band_and_path.py
uv run --with python-flint==0.8.0 --with numpy --with mpmath --python 3.12 python experiments/prime_spectral/test_dh_release_bundle.py
```

The first command checks the current manifest and declared source/input hashes. The three scientific test scripts perform nine checks, including direct complementary minors, both second-band boundaries, positive-coefficient tail enclosures and fresh exact-witness reconstructions. The bundle script adds two checks: matching contents are accepted and stale contents rejected before upload. The three new-round tests supplement the eight preceding checks. The manifest is an integrity and recorded-outcome check, supplementary to numerical replay. It does not replace the written proof or certify a new independent arithmetic backend.

The preceding rounds' historical full-artifact manifests bind their then-current paper, not this revised manuscript. They are not the current paper's acceptance gates. The current verifier checks the preceding immutable scientific artifacts, recursively checks the new input closure, and binds this revised paper separately. The preceding full-paper manifests are historical records; running their old default verifier against this revised paper is not the current acceptance gate.

## Expensive regeneration

The sources themselves document their command-line options and fixed output paths. Run regeneration in a separate extracted copy because it writes new receipts.

- `dh_zero_atlas.py` and `replay_dh_atlas.py`: complete DH atlas to height 340 and its replay.
- `dh_high_rank_scan.py` and `replay_dh_high_rank.py`: historical solid-minor grid and complementary checks. The grid is retained as evidence; no broader new grid is proposed.
- `dh_split_pair_column.py`: only the requested shift-44 column, using small complementary determinants.
- `dh_split_pair_coefficients.py`: separate 1,450-order ordinary-coefficient calculation through conjugate Dirichlet-L jets, at 32,768 bits. It uses the same FLINT backend as the earlier Hurwitz-jet evaluation and checks their coefficient overlap.
- `dh_cauchy_coefficient_extension.py`, `dh_targeted_followup_scan.py` and `assess_second_band_forecast.py`: broad but rigorous positive-coefficient tail enclosures through index 2050, the pre-recorded second band and the requested nearby shifts. The first 1451 coefficients remain evaluated; the appended 600 are bounds, not fresh coefficient evaluations.
- `near_line_mixture_path.py`, `mixture_path_resolution.py`, `attribute_mixture_path.py`: three exact parameters at offsets near 0.015, 0.008 and 0.004, complete atlases, larger-degree checks and finite attribution.
- `dh_split_pair_asymptotic.py`: strict folded-modulus ordering, leading constant and asymptotic sign diagnostics. Its finite-rank prediction omits a quantitative remainder; interval determinants certify actual finite signs.
- `character_zero_atlas.py`, `epstein_zero_atlas.py`, `replay_control_atlases.py`: additional complete atlases and replay.
- `control_window_calibration.py`, `control_zero_attribution.py`: seven-control exact witnesses and finite-atlas contributions.
- `near_line_mixture_control.py`, `near_line_window_calibration.py`, `near_line_attribution.py`: fixed exact rational mixture, complete atlas, held-out forecast test and attribution. This is not a single Conrey-label control.

Finite-atlas attribution does not assert a negligible infinite tail. Selector searches in `small_offset_control_search*.py` are candidate discovery, not complete zero atlases or absence proofs.

## Liu release audit

The fresh compact receipts and our audit scripts are included. Obtain the frozen foreign source and archive directly from [the upstream release](https://github.com/luciferyu666/certified-weil-positivity/releases/tag/v1.0-mcom-submission); the archive is not redistributed here. Its SHA256 and exact commands are in `research/prime_spectral/LIU_FROZEN_RELEASE_AUDIT_2026_10_15.md`. A uses retained factors with reconstructed source, matrices and all residual rows; B is a clean rebuild followed by a second verification pass. The macOS runtime-layout adaptation preserves all source bytes and acceptance gates.

The upstream arithmetic is not a newly implemented independent backend. The analytic operator/domain dependencies remain written mathematics, separate from the receipts and finite Lean checks.

## Paper build

Compile `paper/dh_controls_paper.tex` with Tectonic from its directory; the table inputs and figures are included. The source uses ordinary coefficients, distinguishes folded zero targets, and preserves the exact meaning of multiplicative support C=exp(2L).

No all-support arithmetic estimate or proof of RH is claimed. Rank 664 at shift 44 is first among the explicitly listed DH contiguous minors tested in this study, not globally first among all minors. The locally recorded second-band forecast passed at ranks1536–1972; it was not independently publicly time-stamped. The four-point collision path is inconclusive about the actual b→0 limit.

Publication remains on hold for the human read requested by the author. The reviewer shortlist/request and Liu repository note are local unsent drafts; no one has been contacted. The post-publication Lean targets are scoped, not implemented in this calibration round.

The 16 October figure revision adds `plot_added_control_figures.py`. It reconstructs the folded-zero wedge and finite-atlas attribution bars from the frozen interval records and verifies their caption numbers. `--output paper/figures` writes the `_verified` figure files, preserving the originally supplied PDFs. Display positions use interval midpoints; the assertions include full root disk radii. No scientific searches or previous certificates are changed.
