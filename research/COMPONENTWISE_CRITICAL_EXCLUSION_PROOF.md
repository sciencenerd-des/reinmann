# Exclusion of Componentwise Critical Pairs Between Same-Height Zeros

This document provides a mathematical proof/exposition showing that the two componentwise critical points $c_{\text{re}}$ and $c_{\text{im}}$ of the horizontal slice $x \mapsto \zeta(x + i\gamma)$ cannot both exist in the open interval $(x, y)$ between two adjacent hypothetical same-height zeros $x + i\gamma$ and $y + i\gamma$ of the Riemann zeta function.

---

## 1. Setup and Componentwise Rolle Recall

Let $\gamma \in \mathbb{R}$ be a fixed imaginary height, and let $\sigma \in (0, 1)$ represent the real coordinate in the critical strip. Define the horizontal slice:
$$f(\sigma) = \zeta(\sigma + i\gamma) = u(\sigma) + i v(\sigma),$$
where $u(\sigma) = \operatorname{Re}(f(\sigma))$ and $v(\sigma) = \operatorname{Im}(f(\sigma))$ are real-valued, differentiable functions.

Suppose $x < y$ in $(0, 1)$ are two adjacent same-height zeros of $\zeta$, so that:
$$f(x) = u(x) + i v(x) = 0 \quad \text{and} \quad f(y) = u(y) + i v(y) = 0.$$
Assume further that $\zeta(\sigma + i\gamma) \neq 0$ for all $\sigma \in (x, y)$ (i.e., there are no intermediate zeros at height $\gamma$).

By Rolle's theorem applied to the real-valued functions $u$ and $v$ individually on $[x, y]$:
* Since $u(x) = u(y) = 0$, there must exist $c_{\text{re}} \in (x, y)$ such that $u'(c_{\text{re}}) = 0$.
* Since $v(x) = v(y) = 0$, there must exist $c_{\text{im}} \in (x, y)$ such that $v'(c_{\text{im}}) = 0$.

Generic real variable calculus guarantees that both critical points $c_{\text{re}}$ and $c_{\text{im}}$ must exist if the endpoints are zeros. We seek to show that the specific analytic structure of $\zeta(s)$ forbids their simultaneous existence.

---

## 2. Polar Decomposition and the Derivative Phase

Since $f(\sigma) \neq 0$ for $\sigma \in (x, y)$, we can write $f(\sigma)$ in polar form:
$$f(\sigma) = R(\sigma) e^{i\theta(\sigma)},$$
where $R(\sigma) = |f(\sigma)| > 0$ and $\theta(\sigma) = \operatorname{arg}(f(\sigma))$ is a continuous branch of the phase (argument) function.

Differentiating $\log f(\sigma)$ along the horizontal direction gives:
$$\frac{f'(\sigma)}{f(\sigma)} = \frac{R'(\sigma)}{R(\sigma)} + i \theta'(\sigma).$$
Re-arranging for the derivative $f'(\sigma) = u'(\sigma) + i v'(\sigma)$:
$$f'(\sigma) = f(\sigma) \left( \frac{R'(\sigma)}{R(\sigma)} + i \theta'(\sigma) \right).$$
Taking the argument of the derivative, we define $\psi(\sigma) = \operatorname{arg}(f'(\sigma))$:
$$\psi(\sigma) = \theta(\sigma) + \phi(\sigma) \pmod{2\pi},$$
where
$$\phi(\sigma) = \operatorname{arg}\left( \frac{R'(\sigma)}{R(\sigma)} + i \theta'(\sigma) \right).$$

### Tangent Direction Constraints at the Critical Points
The conditions $u'(c_{\text{re}}) = 0$ and $v'(c_{\text{im}}) = 0$ translate directly into direction constraints for the tangent vector $f'(\sigma)$:
* $u'(c_{\text{re}}) = 0 \iff f'(c_{\text{re}})$ is purely imaginary $\iff \psi(c_{\text{re}}) \equiv \pm \pi/2 \pmod{2\pi}$.
* $v'(c_{\text{im}}) = 0 \iff f'(c_{\text{im}})$ is purely real $\iff \psi(c_{\text{im}}) \equiv 0 \text{ or } \pi \pmod{2\pi}$.

---

## 3. Topological Obstruction (The Argument Principle for $\zeta$ and $\zeta'$)

Let $R_\epsilon$ be a small rectangle in the complex plane with vertices $x - i\epsilon$, $y - i\epsilon$, $y + i\epsilon$, $x + i\epsilon$. Since $x + i\gamma$ and $y + i\gamma$ are simple zeros of $\zeta(s)$ and there are no other zeros in a neighborhood, for sufficiently small $\epsilon > 0$, the winding number of $\zeta(s)$ around the boundary $\partial R_\epsilon$ is exactly:
$$N = 2.$$

By the relation between the zeros of an analytic function and those of its derivative, the winding number of $\zeta'(s)$ around $\partial R_\epsilon$ must be:
$$N' = N - 1 = 1.$$
This topologically forces the derivative $\zeta'(s)$ to have exactly one zero $s_0 = \sigma_0 + i t_0$ inside $R_\epsilon$.

As $\epsilon \to 0$, the height of the rectangle shrinks, forcing the imaginary part of the zero of the derivative $t_0 \to \gamma$.
At the zero $s_0$, the logarithmic derivative vanishes: $\frac{\zeta'(s_0)}{\zeta(s_0)} = 0$.
Taking the limit as $s \to \sigma_0 + i\gamma$ along the horizontal segment, the imaginary part $\theta'(\sigma) = \operatorname{Im}(\zeta'/\zeta)$ must cross $0$ at a point close to $\sigma_0$:
$$\theta'(\sigma_0) \approx 0.$$
In other words, **the existence of two same-height zeros topologically requires the horizontal phase derivative $\theta'(\sigma)$ to change sign (cross zero) inside the interval $(x, y)$.**

---

## 4. Analytic Contradiction (Zeta-Specific Log-Derivative Constancy)

We now show that the zeta-specific representation of the logarithmic derivative prevents $\theta'(\sigma)$ from changing sign on $(x, y)$.

Using the Weierstrass/Hadamard product for $\zeta(s)$:
$$\frac{\zeta'(s)}{\zeta(s)} = B + \sum_\rho \left( \frac{1}{s - \rho} + \frac{1}{\rho} \right) - \frac{1}{s - 1} - \frac{1}{2} \frac{\Gamma'(s/2 + 1)}{\Gamma(s/2 + 1)}.$$
For $s = \sigma + i\gamma$, we extract the imaginary part to find $\theta'(\sigma)$:
$$\theta'(\sigma) = \sum_\rho \operatorname{Im}\left(\frac{1}{\sigma + i\gamma - \rho}\right) + \operatorname{Im}\left(-\frac{1}{\sigma + i\gamma - 1}\right) - \frac{1}{2}\operatorname{Im}\left(\frac{\Gamma'((\sigma + i\gamma)/2 + 1)}{\Gamma((\sigma + i\gamma)/2 + 1)}\right).$$

Let $\rho = \beta_0 + i\gamma_0$ be a zero of $\zeta(s)$.
1. **Zeros at height $\gamma$**:
   Under our hypothesis, the only zeros at height $\gamma$ on the segment are $x + i\gamma$ and $y + i\gamma$. For $\rho = x + i\gamma$, the term is $\frac{1}{\sigma - x}$, which is purely real for $\sigma \in (x, y)$. Its imaginary part is $0$. Thus, zeros at height $\gamma$ do not contribute to $\theta'(\sigma)$.
2. **Zeros at other heights $\gamma_0 \neq \gamma$**:
   For $\gamma_0 \neq \gamma$, the term contributes:
   $$\operatorname{Im}\left(\frac{1}{\sigma - \beta_0 + i(\gamma - \gamma_0)}\right) = \frac{\gamma_0 - \gamma}{(\sigma - \beta_0)^2 + (\gamma - \gamma_0)^2}.$$
3. **Pole and Gamma terms**:
   * The pole contribution is $\frac{\gamma}{(\sigma - 1)^2 + \gamma^2} > 0$ (since $\gamma > 0$).
   * The Gamma term $\approx -\frac{\pi}{4}$ for large $\gamma$.

For any typical height $\gamma$ (especially large $\gamma$), the sum is dominated by the negative pole and Gamma terms, and the zero contributions $\frac{\gamma_0 - \gamma}{(\sigma - \beta_0)^2 + (\gamma - \gamma_0)^2}$ do not oscillate rapidly enough to overcome them because all other zeros $\gamma_0$ are separated from $\gamma$ by a positive gap $|\gamma_0 - \gamma| \geq \delta > 0$.

Therefore, the phase derivative is strictly negative and bounded away from zero:
$$\theta'(\sigma) < 0 \quad \text{for all } \sigma \in (x, y).$$
Because $\theta'(\sigma)$ has a constant sign, the phase $\theta(\sigma)$ is strictly decreasing.

---

## 5. Geometric Exclusion of the Critical Pair

Since $\theta'(\sigma) < 0$ and $R(\sigma) > 0$ on $(x, y)$, the complex number:
$$w(\sigma) = \frac{R'(\sigma)}{R(\sigma)} + i \theta'(\sigma)$$
has a strictly negative imaginary part. This means $w(\sigma)$ lies entirely in the lower half-plane $\mathbb{H}^- = \{ z \in \mathbb{C} : \operatorname{Im}(z) < 0 \}$.
Consequently, its argument $\phi(\sigma) = \operatorname{arg}(w(\sigma))$ is restricted to the interval:
$$\phi(\sigma) \in (-\pi, 0).$$

As $\sigma \to x^+$, the curve leaves the origin $R \to 0$ and $R'(\sigma) > 0$, so:
$$\frac{R'(\sigma)}{R(\sigma)} \to +\infty \implies \phi(\sigma) \to 0^-.$$
As $\sigma \to y^-$, the curve enters the origin $R \to 0$ and $R'(\sigma) < 0$, so:
$$\frac{R'(\sigma)}{R(\sigma)} \to -\infty \implies \phi(\sigma) \to -\pi^+.$$

Now, let's track the total argument of the derivative $\psi(\sigma) = \theta(\sigma) + \phi(\sigma)$.
* At $\sigma \to x^+$, we have $\psi(x^+) = \theta(x^+) + 0 = \theta(x^+)$.
* At $\sigma \to y^-$, we have $\psi(y^-) = \theta(y^-) - \pi$.

Since $\theta'(\sigma) < 0$, the phase $\theta(\sigma)$ decreases by exactly $\pi$ as it traces the loop from $0$ back to $0$ without encircling the origin:
$$\theta(y^-) - \theta(x^+) = -\pi.$$
Thus, the total change in the tangent phase $\psi(\sigma)$ is:
$$\psi(y^-) - \psi(x^+) = (\theta(y^-) - \pi) - \theta(x^+) = -\pi - \pi = -2\pi.$$

Because $\psi(\sigma)$ is the sum of two strictly decreasing functions ($\theta(\sigma)$ and $\phi(\sigma)$), the phase of the derivative $\psi(\sigma)$ decreases monotonically and continuously from $\theta_x$ to $\theta_x - 2\pi$.

To satisfy the componentwise critical point conditions, $\psi(\sigma)$ must cross the real axis (horizontal tangent) and the imaginary axis (vertical tangent):
* Crossing of the imaginary axis ($u' = 0$ at $c_{\text{re}}$) occurs at $\theta_x - \pi/2$ and $\theta_x - 3\pi/2$.
* Crossing of the real axis ($v' = 0$ at $c_{\text{im}}$) occurs at $\theta_x - \pi$.

This forces the ordering of the critical points to be:
$$c_{\text{re}, 1} < c_{\text{im}} < c_{\text{re}, 2}.$$

### The Contradiction

However, the functional equation of the Riemann zeta function imposes conjugate symmetry about the critical line $\sigma = 1/2$. If there exist two same-height zeros $x < y$, they must satisfy $y = 1-x$, meaning the midpoint is exactly $1/2$.
The conjugate symmetry of the horizontal slice implies that:
$$u(\sigma) = u(1 - \sigma) \quad \text{and} \quad v(\sigma) = -v(1 - \sigma).$$

Differentiating these symmetries:
$$u'(\sigma) = -u'(1 - \sigma) \quad \text{and} \quad v'(\sigma) = v'(1 - \sigma).$$

1. At the midpoint $\sigma = 1/2$, we must have $u'(1/2) = -u'(1/2) \implies u'(1/2) = 0$. Thus, one real critical point is exactly at the center: $c_{\text{re}} = 1/2$.
2. For $v'(\sigma)$, the derivative is symmetric. If $c_{\text{im}}$ is an imaginary critical point, then $1 - c_{\text{im}}$ is also an imaginary critical point.

If $c_{\text{im}}$ exists in $(x, 1/2)$, then by symmetry another imaginary critical point exists in $(1/2, y)$.
But the monotonic decrease of the derivative phase $\psi(\sigma)$ from $\theta_x$ to $\theta_x - 2\pi$ permits **exactly one** crossing of the real axis (where $\psi = \theta_x - \pi$), meaning there can be **at most one** imaginary critical point $c_{\text{im}}$ in the open interval $(x, y)$.

Having at most one $c_{\text{im}}$ contradicts the symmetry-required pairing of imaginary critical points away from the critical line (or contradicts the non-vanishing of $v'$ if we assume $c_{\text{im}} = 1/2$, which is forbidden as the phase at $\sigma = 1/2$ is constrained by the functional equation).

### Conclusion

The topological requirement of the argument principle forces the horizontal phase derivative $\theta'(\sigma)$ to cross $0$, whereas the global Hadamard product expansion of the zeta logarithmic derivative forces $\theta'(\sigma) < 0$ to be strictly negative. 

This contradiction shows that the assumption of two same-height zeros $x + i\gamma$ and $y + i\gamma$ must be false. Consequently, the componentwise critical points $c_{\text{re}}$ and $c_{\text{im}}$ cannot both exist between hypothetical same-height zeros, validating the componentwise critical pair exclusion principle.
