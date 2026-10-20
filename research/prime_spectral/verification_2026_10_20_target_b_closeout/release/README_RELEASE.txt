Unreviewed formalization preprint, second version.
Source pin: 150537bf1d94eced1c22db7660f9c32936372831; Lean/Mathlib v4.30.0.
CI: https://github.com/sciencenerd-des/reinmann/actions/runs/39470397281 (main, dependencies, eleven shards and final assembly successful).
Paper CC-BY-4.0; code Apache-2.0, with PNT+ authorship and attribution retained.

Check public file hashes, extract the source archive, then check every extracted
file against SOURCE_MANIFEST.json. In source/ run:
  lake exe cache get
  lake build
  bash scripts/verify_axiom_clean.sh
  python3 experiments/prime_spectral/build_xi_rectangle.py --jobs 2 --output rectangle-build
  lake build Reinmann.XiFinitePFCertified
  lake env lean scripts/RectangleAxioms.lean
  lake env lean scripts/PF43Axioms.lean
The optional tile build is substantial; all 308 numerical tile source modules
are included. Dependency versions are pinned by lake-manifest.json. The root
guard audits 2608 theorem rows; the numerical and PF43 audits are separate.

The split-pair theorem assumes simple selected zeros and an isolated boundary
modulus tie. The independent actual-Xi product/sector application retains
analytic multiplicities. The closed height-14.1 rectangle and unconditional
PF43 formalize classical facts. PF58 retains the external seven-eighths input.
No RH proof, unbounded-rank positivity or Lean DH zero atlas is claimed.
AI assistance is disclosed; completed external human peer review is not claimed.
The earlier version remains DOI 10.5281/zenodo.23449490; this package is a new
version candidate until actual publication and public downloads are verified.
