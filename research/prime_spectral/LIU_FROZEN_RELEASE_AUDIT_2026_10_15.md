# Liu frozen release audit — 15 October 2026

The requested source-level replay passed for both certificates in the frozen [v1.0-mcom-submission release](https://github.com/luciferyu666/certified-weil-positivity/releases/tag/v1.0-mcom-submission), commit `b6cd2183c1e79c6c27a34267812a7b2d73ed1b59`. This is a re-execution of the author's arithmetic implementation, supplemented by written analytic inspection, rather than a new implementation or human peer review.

Archive `w200-frozen-artifact.zip`: SHA256 `7f8e47d265326cbfa4da95197c98bc226fe6cbfd8a22e6896955c18d8cdb376d`. Original archive verification passed. All 292 frozen members were rechecked unchanged after execution. No scientific source, driver, audit hook or acceptance gate was modified.

## Executed computations

Theorem A, additive half-width L=1, multiplicative C=e²:

- `run.py FULL_RETAINED_VERIFY --output external-a-full`, followed by `scalar_a.py` and `finalize_a.py`, all under `python -I -S -B`.
- Fresh 45,056 quadrature nodes, 126,877,696 coefficient contributions and 2,816 source coefficients.
- Fresh reconstruction of both 1,408-dimensional parity matrices: 1,983,872 cells in total.
- Full retained-factor residual verification: 1,864,839,680 multiply-accumulate terms, all 2,816 rows, all positive slack and contraction requirements.
- All 72 scalar relations checked; independently recomputed exact Schur determinant with epsilon 2^-151.
- Final status `THEOREM_A_RETAINED_REPRODUCTION_PASS`.
- Retained proposals and factors were verified; this A mode does not regenerate proposals from scratch. Source, projection and residual stages took approximately 758, 30 and 430 seconds respectively.

Theorem B, L=17/16, C=exp(17/8):

- `reproduce.py FULL_REBUILD --output external-b-full --jobs 2`, followed by `reproduce.py FAST_VERIFY --output external-b-full --jobs 2`, both passed.
- Clean reconstruction of 1,024 moments, 13 prime centers, 169 ordered shift pairs, 151,200 matrix intervals, 896 tail coordinates including 448 parity zeros, 100,352 target coordinates and 448 Gram rows.
- Both modes checked all 56 exact scalar assertions and the closure with epsilon 2^-49162.
- This is a source/matrix/residual reconstruction, not just archive-hash verification.

## Runtime adaptation and reproducibility

The unmodified initial macOS preflight failed because the frozen environment audit assumes a Windows `Lib`/`DLLs` layout and rejected the macOS standard-library path of `dataclasses.py`. That failure is retained as a diagnostic, rather than reported as success.

The accepted runtime is CPython 3.12.11 on macOS arm64. A private copy places the byte-identical standard-library Python modules in root `python312.zip`, a path already allowed by the original audit. All 686 zipped modules match the original managed runtime byte for byte. No import-audit bypass or source patch is used. `prepare_liu_macos_runtime.py` records this layout preparation; `audit_liu_frozen_release.py` checks it and the coverage/closure receipts. The frozen original environment was Windows CPython 3.12.10, so this is a cross-platform reproduction with an explicit runtime-layout adaptation.

To repeat, obtain the frozen upstream wrapper and archive from the release above, verify the archive hash and original `verify_archive.py`, extract into an empty directory, prepare a private CPython 3.12 layout if needed, and run the commands above in `reproduction-a` and `reproduction` respectively. Preserve both initial failures and accepted receipts. Our supplement includes fresh compact receipts, not a redistribution of the foreign source/archive; upstream remains the source for those inputs.

## Analytic inspection and limits

Both complete `analytic-source.md` files were read. The A inspection covers complex explicit-formula normalization; the legal smooth test domain and bounded comparison; Binet envelope; Chebyshev complement and Bessel residual; entire source/kernel errors; weighted LDL residuals and inverse majorants; and exact Schur closure. The B inspection covers the weighted prime-operator comparison, positive band-tail operator, leakage and inverse-order bounds, lifted Schur/cross estimates, raw Gram normalization and boundary terms, finite Binet remainder, full kernel/tail error, positive congruence and both integer compilers.

No analytic error was identified in this inspection. Classical explicit formulas, form domains and operator inequalities remain written mathematical dependencies; the receipts do not formalize them in Lean. This audit independently executes the frozen supplied programs. It is not an independent arithmetic backend, external human review, or a proof of RH. The laboratory's own late-dip comparison remains stopped; this audit supplies an independent computational check of the frozen finite windows, not an all-support result.

Machine-readable summary and receipt hashes: `verification_2026_10_15_split_pair/liu_audit.json`.
