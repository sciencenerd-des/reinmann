# Low rectangle: uniform Mellin truncation tail proved

The new `Reinmann/XiMellinRectangle.lean` imports the now-compiling `XiMellinRemainder` and proves four lemmas without an external certificate hypothesis. In particular, for T≥1 and every complex s satisfying 0≤Re(s)≤1 and |Im(s)|≤141/10,

    ‖xiCompleted s − xiMellinTruncation T s‖
      ≤ (19981/50) exp(−T).

This is a bound for the actual completed-Xi target, uniform over the entire closed rectangle. It follows from the previously proved identity for the integral remainder and the uniform norm prefactor bound

    ‖s‖ ‖s−1‖ ≤ 1+H².

The module is imported by the project root and its four theorems are in `AxiomAudit.lean`. Direct compilation, the targeted build, the full build (3563 jobs) and `scripts/verify_axiom_clean.sh` all passed. The audit checks 244 theorems, with no `sorry` or custom axioms; only `propext`, `Classical.choice` and `Quot.sound` occur. Source and log hashes are bound in `verification_2026_10_17_final_mechanism/lean_uniform_tail_validation.json`.

This proves the requested first uniform **integral truncation** step. It does not discharge `ZetaNoLowStripZero (141/10)`. The remaining evaluator work includes:

1. A finite-theta summation tail over the retained integration interval, with an explicit bound uniform in s and the quadrature variable.
2. A proved finite quadrature/enclosure rule for the truncated integral, including variation within complex tiles.
3. A finite coverage proof for the closed rectangle and a strictly positive lower bound for the modulus on each tile after adding every error term.
4. The existing actual-Xi-to-zeta bridge and endpoint handling, checked with their precise hypotheses.

External Arb values may guide tile and precision choices; they do not by themselves prove any of these Lean obligations. A winding count or a sampled grid is not a zero-free rectangle certificate.

The finite-product split-pair formalization remains deferred pending the author's requested go-ahead to start it before publication. Its delay is an authorization choice, not a mathematical dependency on the controls paper's release.
