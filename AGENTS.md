# Research scope and Davenport–Heilbronn gate

Before developing a proposed RH-separating lemma, update
`research/RH_DH_DISCRIMINATOR_REGISTER.json` and its accompanying note.

- State the exact target, its coefficient/support conventions, and its DH analogue.
- Record a reproducible DH witness when available. Distinguish the first tested
  failure from a globally minimal order, degree or window; unknown stays unknown.
- Identify the precise arithmetic property and proposed inequality that would
  exclude DH. Euler-product sign/support or multiplicativity by itself is not a
  positivity proof.
- If a purported sufficient RH argument also proves the false DH analogue,
  reject that argument. If no arithmetic discriminator is specified, classify
  the route as a reformulation, not an active RH strategy.
- Shared prerequisites may hold for DH and still support finite certificates or
  formalization. Do not discard valid necessary lemmas merely because DH satisfies
  them; do not advertise them as an RH discriminator.
- A missing DH implementation is a failed research gate, not evidence that the
  proposed inequality is zeta-specific. Label it uninstantiated and test it first.
- Keep finite strengthening, empirical calibration and formalization separate
  from RH claims. Do not restart stopped scans or forecasting without a new reason.

Preserve unrelated work and immutable verification manifests. Published versions
require their existing release conditions. CI receipts must identify the actual
commit and jobs that checked the claimed proof chain.
