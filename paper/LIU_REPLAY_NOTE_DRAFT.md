# Proposed Liu repository note — unsent

Recommendation: send a short factual reproducibility report after the author approves the public post. No issue or comment has been posted. Avoid claiming peer review or a new independent arithmetic implementation.

Suggested title: Frozen A and B certificate replay on macOS (b6cd218)

I replayed the frozen v1.0-mcom-submission release at commit b6cd2183c1e79c6c27a34267812a7b2d73ed1b59 on macOS arm64 with CPython 3.12.11.

- A: FULL_RETAINED_VERIFY, scalar_a.py and finalize_a.py passed, including fresh source coefficients, both 1,408-dimensional matrices and all 2,816 residual rows. This mode verifies retained proposals/factors.
- B: clean FULL_REBUILD and a subsequent FAST_VERIFY passed with the expected full coverage and scalar assertions.
- All 292 frozen archive members were unchanged after the runs. Archive SHA256: 7f8e47d265326cbfa4da95197c98bc226fe6cbfd8a22e6896955c18d8cdb376d.

The initial unmodified macOS preflight rejected the standard-library path because the import audit assumes a Windows Lib/DLLs layout. I used a private CPython copy with byte-identical stdlib Python modules in root python312.zip, a path already accepted by the existing allowlist. All 686 zipped modules were checked against the original runtime. No driver/scientific source, import audit or acceptance gate was patched or disabled.

I can provide compact fresh receipts and the runtime-layout preparation script. This reports computational re-execution of the supplied implementation; it is not a second arithmetic backend or a formal/human review of every analytic dependency.

The final public artifact link should be inserted only after it is actually published. Do not use the reserved, unpublished controls-paper DOI as evidence of a public record.
