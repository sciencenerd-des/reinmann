# Localized complementary-resolvent verification

This package records the sharp localized norm estimate and the actual
fixed-threshold enclosures at primes 2 and 3. It does not certify an RH
proof, a larger positive window, novelty, actual endpoint trace values,
or an explicit moving-window gap-persistence radius.

Run from the repository root:

~~~sh
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  experiments/prime_spectral/localized_resolvent_enclosures.py \
  --output research/prime_spectral/verification_2026_10_07_localized_resolvent/localized_resolvents.json
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  -m unittest discover -s experiments/prime_spectral -p test_localized_resolvent.py -v
lake build Reinmann.WeilLocalizedResolvent Reinmann.WeilLocalizedResolventAudit
~~~

The generator replays both saved infinite-complement min–max second
eigenvalue bounds. The actual-state universal bound and the trial
Rayleigh upper bounds are checked against the previously verified input
records; their integrals are not rerun here. Full matrix-entry reassembly
was recorded in the preceding cluster-readiness package. The analytic
full-operator reduction and the new semigroup/Fourier/Jensen argument
remain written mathematical inputs, not Lean operator theorems.

The four tests check a noncommuting second inverse identity with both
signs of its linear term, invalid-input rejection, projection-cost/gap
caps, and the coefficient-one enclosure with a very small gap. They
are numerical checks of scalar/matrix calculations, not a replacement
for the infinite-dimensional analysis.

The seven Lean lemmas prove scalar implications of named hypotheses,
with only propext, Classical.choice and Quot.sound in their audits.
Logs and the source/dependency hash manifest are retained here.

The subsequent strong layer limit and the trace-Gram Schur coefficient
are [written analysis](../LAYER_RESOLVENT_SCHUR_COEFFICIENT_2026_10_07.md).
Their operator and eigenvalue refinements are not numerical certificates
or Lean theorems. The sixth scalar lemma checks their fixed-profile
action-error inequality. The seventh proves the exact-Rayleigh error
limit from named scalar Schur-root and coefficient-limit hypotheses;
it does not supply those analytic hypotheses.
