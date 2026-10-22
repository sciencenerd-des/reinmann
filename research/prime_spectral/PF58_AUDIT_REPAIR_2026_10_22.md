# PF58 audit reporting repair

Run [39638580356](https://github.com/sciencenerd-des/reinmann/actions/runs/39638580356)
at `187eaaeae6b5f73eae43b9472edc0fd0aaa5154d` built all nine new tiles,
assembled unconditional PF58, and produced only standard-axiom reports.
Sixteen jobs passed. The final job failed its new audit report's uniqueness
assertion, so the seventeen-job CI gate remains unsatisfied at that snapshot.

The collector enumerated generated equation theorems that occurred in several
module constant lists. Its 48,230 reports, including two wrapper checks, had
47,896 distinct pretty-printed names. No nonstandard axiom appeared. The
repair deduplicates actual Lean constant identities before collecting axioms
and prints `Name.toString`, preserving full private names. Report count,
identity uniqueness and the three-axiom allowlist are still required. The
repaired collector passes on 5,352 distinct constants from the complete local
pilot tile.

No Lean proof source or numerical proposal changes in this repair. The workflow
may restore successful tile artifacts from the preceding run; its existing
Lake build commands check current traces and rebuild stale outputs. Missing or
expired artifacts fall back to fresh builds. The final no-rebuild checks and
all semantic audits remain required. A new successful complete run is needed
before the tables may call PF58 CI-verified.

The failed run, original audit, failure analysis and corrected pilot are retained
separately in `verification_2026_10_22_pf58_audit_repair/`. Earlier manifests and
pending snapshots are unchanged. PF97 preparations remain local while this
gate is repaired.
