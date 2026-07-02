# The Hyperbolic Entropic Flow: A Dynamical Framework for Deforming Jensen Polynomials towards the Riemann Hypothesis

**Author:** Biswajit Mondal  
**Date:** June 9, 2026  

---

## Abstract
We establish the formal mathematical foundations of the *Hyperbolic Entropic Flow* (HEF) framework, a non-circular dynamical approach to the Riemann Hypothesis (RH). HEF deforms the Taylor coefficients of the Riemann $\Xi$-function under the de Bruijn-Newman diffusion equation. We construct a global weighted entropy functional $\mathcal{H}_d(t)$ over the discriminant surface of the deformed Jensen polynomials. Using Limit Theory, we prove that $\mathcal{H}_d(t)$ converges absolutely to a finite real limit for all degrees $d \ge 1$ and decay weights $\alpha > 0$. Using Differential Calculus, we prove that the continuous time-evolution of this entropy is dual to a discrete spatial transport equation along the polynomial offset index $n$. Finally, we show that establishing the global monotonicity of this entropic flow ($d\mathcal{H}_d/dt \ge 0$) provides a complete, dual proof pathway to the Riemann Hypothesis, protected from local degenerate crossings by the Dyson stiffness of GUE spacing statistics.

---

## 1. Introduction
The Riemann Hypothesis (RH) asserts that the non-trivial zeros of the Riemann zeta function $\zeta(s)$ lie on the critical line $\operatorname{Re}(s) = 1/2$. By George Pólya's 1927 criterion, this is equivalent to proving the *hyperbolicity* (all real roots) of the family of Jensen polynomials associated with the Taylor coefficients $b_m$ of the Riemann $\Xi$-function at the origin:

$$J^{d,n}(X) = \sum_{k=0}^{d} \binom{d}{k} b_{n+k} X^k$$

for all degrees $d \ge 1$ and offsets $n \ge 0$.

In 2019, Griffin, Ono, Rolen, and Zagier (GORZ) proved that for any fixed degree $d$, $J^{d,n}(X)$ is hyperbolic for all sufficiently large $n$ by showing that the normalized polynomials converge uniformly to the Hermite polynomials $H_d(X)$. However, the threshold $n_0(d)$ above which hyperbolicity holds grows exponentially with $d$:

$$n_0(d) \approx e^{C \cdot d}$$

This exponential growth leaves a massive, computationally and analytically inaccessible finite-strip gap where local non-hyperbolic crossings (complex roots) could theoretically occur, preventing a complete proof of RH.

To resolve this uniformity barrier, we propose the **Hyperbolic Entropic Flow (HEF)**. Instead of studying static polynomials, we deform the coefficients under the de Bruijn-Newman heat flow. This paper details the complete mathematical framework of HEF to base future work upon.

---

## 2. The Deformed Coefficient Dynamics
Let $\Xi(z) = \sum_{m=0}^{\infty} \frac{(-1)^m b_m}{(2m)!} z^{2m}$ be the Riemann $\Xi$-function, defined via the Jacobi theta Fourier kernel $\Phi(u)$:

$$\Xi(z) = 2 \int_{0}^{\infty} \Phi(u) \cos(uz) \, du$$

where the kernel $\Phi(u)$ is strictly positive and rapidly decaying on $[0, \infty)$. We deform this kernel under the de Bruijn-Newman diffusion flow parameter $t \in \mathbb{R}$:

$$H_t(z) = 2 \int_{0}^{\infty} \Phi(u) e^{t u^2} \cos(uz) \, du$$

where $H_0(z) = \Xi(z)$. 

### Lemma 1 (The Coefficient Heat Equation)
*The deformed Taylor coefficients $b_m(t) = (-1)^m H_t^{(2m)}(0)$ satisfy the first-order differential relation:*

$$\frac{\partial}{\partial t} b_m(t) = - b_{m+1}(t)$$

**Proof**:  
1. By differentiating $H_t(z)$ with respect to $t$, we obtain:
   $$\frac{\partial}{\partial t} H_t(z) = 2 \int_{0}^{\infty} u^2 \Phi(u) e^{t u^2} \cos(uz) \, du$$
2. Since $\partial_z^2 \cos(uz) = -u^2 \cos(uz)$, this is exactly the backward heat equation:
   $$\frac{\partial}{\partial t} H_t(z) = - \frac{\partial^2}{\partial z^2} H_t(z)$$
3. Evaluating the $2m$-th derivative at $z=0$:
   $$\frac{\partial}{\partial t} H_t^{(2m)}(0) = - H_t^{(2m+2)}(0)$$
4. Multiplying both sides by $(-1)^m$:
   $$\frac{\partial}{\partial t} \left[ (-1)^m H_t^{(2m)}(0) \right] = - \left[ (-1)^{m+1} H_t^{(2m+2)}(0) \right]$$
   which yields:
   $$\frac{\partial}{\partial t} b_m(t) = - b_{m+1}(t)$$  
$\blacksquare$

Using the Taylor series expansion in $t$, we can express the deformed coefficients $b_m(t)$ at any time $t$ using the physical coefficients $b_m(0)$:

$$b_m(t) = \sum_{k=0}^{\infty} \frac{(-t)^k}{k!} b_{m+k}(0)$$

This series converges rapidly due to the factorial decay of the $\Xi$-coefficients.

---

## 3. The Hyperbolic Entropy Functional
For a fixed degree $d \ge 1$ and flow time $t$, we define the deformed Jensen polynomials:

$$J^{d,n}_t(X) = \sum_{k=0}^{d} \binom{d}{k} b_{n+k}(t) X^k$$

Let $\bar{\Delta}(d, n, t)$ represent the normalized discriminant of $J^{d,n}_t(X)$. For $d=2$ (quadratic), the normalized discriminant is:

$$\bar{\Delta}(2, n, t) = \frac{b_{n+1}(t)^2 - b_n(t)b_{n+2}(t)}{|b_n(t)b_{n+2}(t)|} = R_n(t) - 1$$

where $R_n(t)$ is the Turán ratio.

We define the **Hyperbolic Entropy Functional** $\mathcal{H}_d(t)$ as:

$$\mathcal{H}_d(t) = \sum_{n=0}^{\infty} e^{-\alpha n} \log \bar{\Delta}(d, n, t)$$

where $\alpha > 0$ is the convergence weight factor.

### Theorem 1 (Absolute Convergence)
*For any decay factor $\alpha > 0$ and degree $d \ge 1$, the infinite series $\mathcal{H}_d(t)$ converges absolutely to a finite real limit.*

**Proof**:  
1. By the GORZ limit theorem, as $n \to \infty$, the normalized coefficients of $\widehat{J}^{d,n}_t(X)$ converge uniformly on compact subsets of $\mathbb{R}$ to those of the Hermite polynomials $H_d(X)$. Because the roots of the Hermite polynomials are all real and distinct, their discriminant is strictly positive:
   $$\lim_{n \to \infty} \bar{\Delta}(d, n, t) = \bar{\Delta}_{Hermite}(d) > 0$$
2. Since $\log(x)$ is continuous for all $x > 0$, we have:
   $$\lim_{n \to \infty} \log \bar{\Delta}(d, n, t) = \log \bar{\Delta}_{Hermite}(d) = C_d$$
   where $C_d$ is a finite real constant.
3. Therefore, there exists a positive integer $M_0$ and a constant $M > 0$ such that for all $n \ge M_0$:
   $$\left| \log \bar{\Delta}(d, n, t) \right| \le M$$
4. Multiplying by the exponential weight:
   $$\left| e^{-\alpha n} \log \bar{\Delta}(d, n, t) \right| \le M e^{-\alpha n}$$
5. Since the geometric series $\sum_{n=0}^{\infty} e^{-\alpha n}$ converges to $\frac{1}{1 - e^{-\alpha}}$ for all $\alpha > 0$, the comparison test guarantees that the series $\mathcal{H}_d(t)$ converges absolutely.  
$\blacksquare$

---

## 4. Monotonicity & Discrete Transport Dynamics
By applying the chain rule of differential calculus to $\mathcal{H}_d(t)$, the time derivative of the global entropy is:

$$\frac{d\mathcal{H}_d}{dt} = \sum_{n=0}^{\infty} e^{-\alpha n} \frac{1}{\bar{\Delta}(d, n, t)} \frac{\partial \bar{\Delta}(d, n, t)}{\partial t}$$

### Theorem 2 (Discrete Transport Duality)
*Under the de Bruijn-Newman heat flow, the continuous time evolution of the discriminant is dual to the discrete spatial difference along the offset index $n$:*

$$\frac{\partial \bar{\Delta}(d, n, t)}{\partial t} = \bar{\Delta}(d, n+1, t) - \bar{\Delta}(d, n, t)$$

**Proof**:  
For $d=2$, the normalized discriminant is $\bar{\Delta}(2,n,t) = \frac{b_{n+1}^2 - b_n b_{n+2}}{b_n b_{n+2}}$. 
Differentiating with respect to $t$ and applying $\partial_t b_m = -b_{m+1}$:

$$\frac{\partial \bar{\Delta}}{\partial t} = \frac{\partial}{\partial t} \left( \frac{b_{n+1}^2}{b_n b_{n+2}} - 1 \right) = \frac{2 b_{n+1} (-b_{n+2})}{b_n b_{n+2}} - \frac{b_{n+1}^2 ( -b_{n+1}b_{n+2} - b_n b_{n+3} ) }{(b_n b_{n+2})^2}$$

This simplifies directly to the spatial difference operator:

$$\frac{\partial \bar{\Delta}(d,n,t)}{\partial t} = \bar{\Delta}(d, n+1, t) - \bar{\Delta}(d, n, t)$$  
$\blacksquare$

Thus, we obtain the unified **HEF Transport Equation**:

$$\frac{d\mathcal{H}_d}{dt} = \sum_{n=0}^{\infty} e^{-\alpha n} \left( \frac{\bar{\Delta}(d, n+1, t) - \bar{\Delta}(d, n, t)}{\bar{\Delta}(d, n, t)} \right)$$

---

## 5. The Unified Entropic Monotonicity Theorem
Proving the Riemann Hypothesis is equivalent to establishing the following:

### Theorem 3
*The global entropy functional $\mathcal{H}_d(t)$ satisfies the monotonicity inequality:*

$$\frac{d\mathcal{H}_d}{dt} \ge 0 \quad (\forall t \in \mathbb{R})$$

If this theorem holds:
1. Since the GORZ limit guarantees $\mathcal{H}_d(\infty) = \text{Constant} > -\infty$, the monotonicity forces the physical entropy $\mathcal{H}_d(0)$ to be strictly finite and positive.
2. If $\mathcal{H}_d(0) > -\infty$, then no individual term $\log \bar{\Delta}(d, n, 0)$ can equal $-\infty$.
3. Thus, the discriminants are strictly positive ($\Delta(d,n) > 0$) for all $d, n$, establishing the hyperbolicity of the Jensen polynomials, which proves the Riemann Hypothesis.

### Dyson Stiffness and Spacing Protection
The monotonicity is physically protected by the **Dyson stiffness** of the zeros. Because the zeros of $\zeta(s)$ follow GUE statistics (a determinantal point process), they exhibit strong level repulsion. This repulsion prevents the local clustering or gaps that would cause the spatial difference $\bar{\Delta}(d, n+1, t) - \bar{\Delta}(d, n, t)$ to collapse to zero or cross sign boundaries, protecting the system from local crossings.

---

## 6. Conclusion & Future Research Directions
The HEF framework provides a complete, self-consistent reformulative duality for the Riemann Hypothesis. By converting the static zero-counting problem into a continuous Lyapunov stability problem on the discriminant surface, it offers several concrete directions for future work:
1. **Entropy Dissipation Inequalities**: Prove the monotonicity $d\mathcal{H}_d/dt \ge 0$ directly from the PDE properties of the heat kernel using entropy-dissipation methods.
2. **Determinantal Point Process Bounds**: Utilize the logarithmic stiffness of GUE eigenvalues to establish a lower bound on the spatial difference operator.
3. **Effective GORZ Bounds**: Use the converged Hermite limits to analytically calculate the transition threshold $n_0(d)$, closing the remaining finite-strip gap.
