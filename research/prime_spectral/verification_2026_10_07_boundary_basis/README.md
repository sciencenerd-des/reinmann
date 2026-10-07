# Boundary-basis and full-residual trace verification

This package records certified normalized renewal/Green-basis profiles,
improved coarse trace enclosures for both actual minimizing states, and
conditional full-residual budgets. It does not contain a successful
assembled unit-trial residual certificate, trace nonvanishing, a larger
positive window, an RH proof, or a cleared novelty claim.

The analytic proof and normalization are in
[the boundary-basis note](../BOUNDARY_BASIS_RESIDUAL_TRACE_2026_10_07.md).
Run from the repository root with Python 3.12, python-flint 0.8.0 and
mpmath 1.3.0:

~~~sh
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  experiments/prime_spectral/renewal_boundary_basis.py \
  --output research/prime_spectral/verification_2026_10_07_boundary_basis/renewal_basis.json
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  experiments/prime_spectral/renewal_boundary_basis.py --nodes 24 --width 2 \
  --output research/prime_spectral/verification_2026_10_07_boundary_basis/renewal_basis_alternate.json
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  experiments/prime_spectral/residual_endpoint_certificate.py \
  --output research/prime_spectral/verification_2026_10_07_boundary_basis/residual_trace_constants.json
uv run --with python-flint==0.8.0 --with mpmath==1.3.0 --python 3.12 python \
  -m unittest discover -s experiments/prime_spectral -p test_boundary_basis.py -v
lake build Reinmann.WeilResidualTrace Reinmann.WeilResidualTraceAudit
~~~

The profile generators use Arb ball quadrature with a written Cauchy
interpolation remainder and bounds on both infinite spectral tails.
Both use 256-bit arithmetic and Wiener–Hopf cutoff 64. Changing panel
width and interpolation degree is a discretization cross-check, not an
independent implementation. A coarser 16-node/width-2 attempt failed its
strict convolution-ratio gate at exp(-8); no successful output was saved
for that attempt. The successful JSON records include source hashes.

The residual generator checks saved full-operator threshold eigenvalue
inputs against weakened bounds. It does not reassemble their matrices
or repeat their infinite-complement proof in this package; that was done
in the trace-stability and all-entry cluster-readiness packages. Those
inputs and the signed heat/forcing/Green estimates are dependencies.
One-sided state envelopes use zero extension of an actual threshold
ground state; they do not require quantitative moving-window gap bounds.

Five tests check changed-discretization profile overlap, the independent
older Laplace/concavity normalization bounds, the Cauchy allowance at
non-node points, signed trace corners, fail-closed clearance gates and
the recorded split budgets. Sampling does not prove the uniform Cauchy
remainder; its proof is in the note.

Four Lean theorems prove scalar consequences of named projection,
heat/forcing/trace and decomposition hypotheses. Their audit lists only
propext, Classical.choice and Quot.sound. Neither operator-domain
inclusions nor residual estimates of an actual trial are Lean theorems
here. Only the named modules were built; no claim is made about the
unrelated dirty modules in the repository.

The manifest hashes sources, analytic dependencies, retained results
and logs. An audit of file hashes is reproducibility evidence, not an
independent review of the analytic proofs.
