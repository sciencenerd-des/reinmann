# Journal & preprint targets — synthesized RH formalization paper

**Positioning (from your SUBMISSION_CHECKLIST):** this is a *Lean-verified reduction
and formalization study*, not a proof of RH. The targets below are chosen to fit
that framing. **Submit to one journal at a time** — simultaneous submission is
prohibited by essentially all mathematics journals and can get you blacklisted.

A realistic note: the very top "famous" journals (Annals of Mathematics,
Inventiones, JAMS, Forum of Mathematics Pi) expect a major *new theorem*. A
reduction-that-does-not-prove-RH, however clean, is not a fit there and would be
desk-rejected. The strongest honest homes for this work are computational /
experimental and formal-methods venues, plus solid specialist number-theory
journals. Ranked by fit:

## Tier 1 — best fit (start here)

1. **Experimental Mathematics** (Taylor & Francis)
   - Scope: rigorous computation + theory, exactly the manuscript's
     numerics-plus-formalization blend. The revised cover letter is aligned.
   - Why #1: rewards experimental delimitation of an open problem; "no proof" is
     not a strike here.

2. **Mathematics of Computation** (AMS)
   - Scope: computational mathematics, verified computation, number-theoretic
     algorithms. High reputation.
   - Why: the high-precision certified coefficients and the machine-checked
     reductions both land well; more prestige than Exp. Math.

3. **Journal of Automated Reasoning** (Springer)
   - Scope: formalized mathematics, interactive theorem proving. Your Lean 4 /
     Mathlib development and axiom-audit discipline are central here.
   - Why: if you want the *formalization* judged as the primary contribution.

## Tier 2 — strong specialist options

4. **Research in Number Theory** (Springer)
   - Scope: all of number theory, including computational and formal contributions.

5. **Journal of Number Theory** (Elsevier)
   - Scope: broad NT; the reduction chain and Turán/Jensen results fit.

6. **International Journal of Number Theory** (World Scientific)
   - Scope: broad NT; reasonable acceptance odds for a careful reduction paper.

## Tier 3 — conference route for the formalization (CS/logic)

7. **ITP — Interactive Theorem Proving** (LIPIcs proceedings)
   - Peer-reviewed CS venue; ideal if you reframe the Lean development as the
     headline result. Note deadlines are fixed (annual).
8. **CPP — Certified Programs and Proofs** (ACM)
   - Same idea; the Mathlib paper itself appeared at CPP.

## Preprint / "research publish website" (post first, in parallel with journal)

- **arXiv** — primary `math.NT`, cross-list `cs.LO` (matches your checklist).
  - First-time math submission needs an **endorsement**; ask a colleague who has
    posted to math.NT, or an institutional contact.
  - Posting to arXiv does **not** count as prior publication for any journal above —
    it's standard and expected. Do this first to establish priority/timestamp.
- **Zenodo** — archive the Lean repo to get a DOI (your checklist item #3); cite it
  in the paper appendix.

## Suggested sequence

1. Post to arXiv (math.NT + cs.LO) + archive repo on Zenodo for a DOI.
2. Submit to **Experimental Mathematics** with the drafted cover letter.
3. If declined, move in order: Mathematics of Computation → Research in Number
   Theory → Journal of Number Theory. Re-target the cover letter each time (swap the
   journal name and the "why this journal" paragraph).
4. Consider ITP/CPP in parallel only for a *differently framed* formalization paper
   — not the same manuscript (that would be dual submission).

## Before any submission (from your checklist)

- Run `./scripts/safe-verify.sh`; record the exact commit hash.
- Confirm the compiled PDF (current: `rh_two_routes_paper.pdf`, 14 A4 pp.).
- Add appendix: Lean version, Mathlib commit, Lake manifest hash.
- Add the Zenodo DOI / repo archive link.
- Verify each journal's current submission system, formatting, and any fees on its
  official site — these change and should be checked at submission time.
