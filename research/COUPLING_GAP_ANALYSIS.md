# Ratio Coupling and Zero-Crossing Gap Analysis

This document analyzes the gap to a potential zero-crossing of the horizontal phase derivative $\theta'(\sigma)$ by computing the ratio:
$$R(\sigma, \gamma) = \frac{P(\sigma, \gamma)}{N(\sigma, \gamma) - E(\sigma, \gamma)}$$
where a zero-crossing occurs if and only if $R(\sigma, \gamma) = 1$.

## 1. Quantitative Gap to Zero-Crossing

* **Minimum Distance to 1** ($|R - 1|$): `0.003396`
* **Closest Ratio** ($R$): `0.996604`
* **Location**: Zero #13 ($\gamma \approx 59.3470$), at $\sigma = 0.6$

## 2. Interpretation of the Gap

The fact that the ratio $R(\sigma, \gamma)$ gets as close to $1$ as $0.996604$ (distance of $0.003396$) without $\theta'(\sigma)$ crossing zero reveals a crucial scaling mechanism:

1. **Large Sum Scaling**:
   At Zero #13 ($\gamma \approx 59.3470$), the vertical distance to the next zero is very small ($1.4847$ vs $2.9008$ below), which causes both the positive sum $P(\sigma, \gamma)$ and the negative sum $N(\sigma, \gamma) - E(\sigma, \gamma)$ to scale up to large values (around $10^2$).
2. **Absolute Margin Protection**:
   Because the individual terms are so large, a ratio of $R \approx 0.9966$ still corresponds to a large absolute difference:
   $$\theta'(\sigma) = P(\sigma, \gamma) - (N(\sigma, \gamma) - E(\sigma, \gamma)) \approx -0.327$$
   which is safely bounded away from $0$.
   
Therefore, the non-vanishing of $\theta'(\sigma)$ is protected not by the ratio staying far from 1, but by the fact that the difference is magnified as the ratio approaches 1 due to the simultaneous scaling of both local sums.

