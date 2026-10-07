# Assembled actual-trial residual verification

Outcome: actual unit operator-domain trials at the two prime thresholds
have certified norm, Rayleigh, nonzero trial trace, and full L2/Linfinity
residual enclosures. A certified residual LOWER bound proves failure of
the sufficient nonzero minimizing-state trace interface for these trials.
No tight actual minimizing-state trace or larger positive window is proved.

The complete analytic reduction is in
[the assembled-trial note](../ASSEMBLED_TRIAL_FULL_RESIDUAL_2026_10_07.md).
The full residual upper bounds are deliberately conservative. Their lower
bounds are sufficient to reject these particular trials; they do not
reject the method or imply a zero true trace.

Reproduce from the repository root:

~~~sh
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  experiments/prime_spectral/compact_window_certificate.py \
  --half-width 11/20 --count 160 --order 80 --finite-lower 1e-12 \
  --output research/prime_spectral/verification_2026_10_07_assembled_trial/closer_prime_three_lower.json
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  experiments/prime_spectral/assembled_trial_certificate.py \
  --output research/prime_spectral/verification_2026_10_07_assembled_trial/assembled_trials.json
~~~

To reproduce the witness adapter for the existing all-entry verifier:

~~~python
import json
from pathlib import Path
root = Path('research/prime_spectral/verification_2026_10_07_assembled_trial')
data = json.loads((root/'assembled_trials.json').read_text())
rows = []
for row in data['results']:
    witness = {key: row[key] for key in (
        'threshold_prime', 'lower_operator_input', 'lower_operator_sha256', 'shift')}
    witness['trial_ground_eigenvalue_upper'] = row['actual_rayleigh_enclosure']
    rows.append(witness)
(root/'threshold_ground_gaps.json').write_text(json.dumps({
    'status': 'stronger_full_gap_witnesses_from_actual_trial_upper_bounds',
    'results': rows}, indent=2)+'\n')
~~~

Then run:

~~~sh
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  experiments/prime_spectral/reassemble_threshold_gaps.py \
  --directory research/prime_spectral/verification_2026_10_07_assembled_trial \
  --output research/prime_spectral/verification_2026_10_07_assembled_trial/all_entry_reassembly.json
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  -m unittest discover -s experiments/prime_spectral -p test_assembled_trial.py -v
lake build Reinmann.WeilTrialResidual Reinmann.WeilTrialResidualAudit
~~~

The full lower comparisons are checked at shifts 0.057 and 0.00000412.
The resulting weakened full complementary clearances are 0.055579 and
0.000004016. All 16,000 lower-block entries are compared at alternate
quadrature orders and 512 bits, and the stronger inertia/gap bounds are
replayed. This reuses the same implementation and analytic allowances.
It is not independent mathematical review or an independent backend.

Six tests check source hashes and actual-trial failure evidence, positive
full complementary witnesses, all-entry reassembly, the same omitted
probe in a larger test space, a zero-head/nonzero-full residual example,
invalid-input failure gates, and the fixed-trace family at three enclosed
graph norms. Increasing the test space here checks
the single residual coefficient; it is not a positivity-minor scan.

Five Lean scalar theorems check the residual-probe lower bound, exact
trial-trace normalization, failure of the sufficient trace gate and
positive-form Rayleigh error transfer, and the obstruction to a graph-norm
trace estimate from a fixed-trace/small-graph family. The latter family
is written analysis: the cutoff estimates give graph norm tending to zero
while the endpoint trace stays fixed. This rules out L2-only residual
trace certification, including near a simple ground state with a gap.
Their audit uses only propext,
Classical.choice and Quot.sound. The actual operator-domain, comparison,
positive-form and renewal facts remain written mathematical inputs.
Only the named Lean modules were built.

The older large-window note received a scalar coverage correction:
exp(1.6094) is 4.9998104414..., and this endpoint does not prove every
window below 5. That separate large certificate was not replayed here.
The retained logs and manifest describe this continuation's checks.
