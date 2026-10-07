# Trace/cluster readiness checks

This directory records continuation of the research after the novel-paper
readiness decision failed. It is not a manuscript or novelty certificate.

Reassemble all 16,000 entries of the two existing lower-operator matrices,
at different quadrature orders and 512-bit precision, and repeat the
full-complement second-eigenvalue bounds:

~~~sh
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  experiments/prime_spectral/reassemble_threshold_gaps.py \
  --directory research/prime_spectral/verification_2026_10_07_trace_stability \
  --output research/prime_spectral/verification_2026_10_07_cluster_readiness/all_entry_reassembly.json
lake build Reinmann.WeilClusterActivation Reinmann.WeilClusterActivationAudit
~~~

Both commands passed. The Lean audit covers four scalar error implications,
with only the standard foundational axioms. It does not prove the operator
or novelty assertions. The quadrature replay shares the existing generator
and Arb library; it is not an independent implementation. Input hashes,
results, source hashes, and the mathematical limitations are in the manifest.
