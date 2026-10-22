Unreviewed formalization preprint, version 3.0.0 (22 October 2026).
Proof source: b4ec4a3920973faae02d4d9f3a56456886df49c9; Lean and Mathlib v4.30.0.
CI: https://github.com/sciencenerd-des/reinmann/actions/runs/39733278869; all 34 jobs passed, including no-rebuild assembly and audits.

This package contains standalone paper/main.tex and main.pdf, every pinned Lean
source/configuration binding, all 840 numerical tile part modules, bounded
build scripts, rational plans, upstream attribution, and the complete raw CI
and axiom-audit receipts. Check every member against SOURCE_MANIFEST.json.
All 1192 proof-source/configuration bindings are also checked against the
included exact-proof-commit map. No compiled proof artifacts are included.

Fresh kernel reproduction from source/ (requires elan and the pinned toolchain):
  lake exe cache get
  lake build
  bash scripts/verify_axiom_clean.sh
  python3 experiments/prime_spectral/build_xi_rectangle.py --jobs 2 --output tmp/rectangle
  python3 experiments/prime_spectral/build_finite_band.py --rank 58 --jobs 2 --output tmp/band58
  python3 experiments/prime_spectral/build_finite_band.py --rank 97 --jobs 2 --output tmp/band97
  lake build Reinmann.XiFinitePFCertified
  lake env lean ../verification/proof_CI/PF58/Audit.lean
  lake env lean ../verification/proof_CI/PF97/Audit.lean
The numerical rebuild is substantial. Gamma tiles are serialized by the bounded
scripts; the pinned workflow records the parallel hosted replay. The live
source-provenance verifiers additionally require an actual Git checkout at the
proof pin; raw audit inputs above work with the extracted sources. Historical
standalone adapters for the separate Lean 4.34.1 external replay are not default
root imports and do not enter the Lean 4.30 finite-PF proofs.

The root audit covers 2643 declarations. Separate PF58/PF97 audits cover 47896
and 363579 distinct implementation theorem constants, including private generated
ones and canonical entry points; these are not counts of new mathematical results.
Only propext, Classical.choice and Quot.sound occur in the claimed proof chain.
All ordered minors through ranks 43, 58 and 97 are nonnegative for ordinary
folded-Xi coefficients. The full strip is certified only through 14.1; higher
right-hand boxes reach 19 and 32 and allow critical-line zeros. Platt--Trudgian's
published height-3e12 computation gives a much larger classical PF benchmark;
these small ranks measure formal coverage, not new mathematical knowledge.
The split-pair theorem retains its simple selected zeros and isolated boundary
tie. No RH proof, unbounded-rank PF, Green budget, or Lean DH atlas is claimed.

Paper CC-BY-4.0; code Apache-2.0 with upstream PNT+ authorship preserved in
source/Reinmann/PNTPlus/. AI assistance and lack of completed external human
peer review are disclosed. Historical README/status snapshots inside source/
are exact proof-commit bytes; the completed CI receipts supersede their then-
pending labels. Earlier published versions and the DH-controls record are
unchanged. This package's publication state is established by its Zenodo record.
