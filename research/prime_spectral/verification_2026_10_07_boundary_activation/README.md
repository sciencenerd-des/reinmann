# Boundary-activation verification

The targeted Lean build and eight-statement semantic axiom audit passed.
Only foundational Lean axioms occur; there are no custom axioms or proof
placeholders in the two new Lean files. Python parsing and whitespace
checks also passed. This is a targeted check, not a new full-repository audit.

Four Arb Fourier-normalization checks passed. They validate the comparison
kernel and identity offset at four frequencies, with an analytic spatial
tail allowance. They do not prove a global Fourier identity or validate
the semigroup, PDE, uniform-boundary or novelty arguments.

The research note contains a proposed theorem and written analytic proof.
Its remaining formalization and independent review are explicit. The
leading trace coefficient has additional unproved trace-limit inputs.
No new positive window, RH proof or established novelty is claimed.

The new files are separate from unrelated work in the shared checkout.
