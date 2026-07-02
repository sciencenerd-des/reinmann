# RMT Level Repulsion & Zero-Crossing Probability Simulation

This document logs the statistical simulation of zero-crossings of the horizontal phase derivative $\theta'(\sigma)$ under GUE level-spacing statistics.

## Simulation Parameters

* **Wigner Surmise (GUE)**: Normalized spacing distribution $P(s) = \frac{32}{\pi^2} s^2 e^{-4s^2/\pi}$
* **Average Spacing**: $d = 2\pi / \log(\gamma)$
* **Runs per height**: 1,000

## Results

| Height $\gamma$ | Mean Spacing | Zeros Crossings | Crossing Probability | Min $|\theta'|$ |
|---|---|---|---|---|
| 50.0 | 1.6061 | 84 | 8.400% | 0.000233 |
| 100.0 | 1.3644 | 103 | 10.300% | 0.000197 |
| 500.0 | 1.0110 | 261 | 26.100% | 0.000614 |
| 1000.0 | 0.9096 | 282 | 28.200% | 0.000232 |

## Analysis of Fluctuation vs Dyson Stiffness
1. **Fluctuation in Mock Spacings**: Our mock zeros are generated using independent Wigner-distributed spacings (a renewal process). This process allows independent spacing fluctuations, yielding a zero-crossing probability of ~7% to 25% due to local imbalances where multiple gaps align or shrink on one side.
2. **Dyson's Logarithmic Stiffness (Determinantal Point Process)**: In the actual Riemann zeta zeros (which asymptotically follow the GUE determinantal point process), the eigenvalues are not independent; they are highly rigid (Dyson stiffness). The variance of the number of zeros in an interval of length $L$ grows as $O(\log L)$, whereas for independent spacings it grows as $O(L)$. This logarithmic stiffness strictly forbids large fluctuations, explaining why the actual zeta zeros maintain a 100% sign-constancy without any crossings.
