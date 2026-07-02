# Local Same-Height Repulsion Status

## Result of this pass

The generic real-variable part of the horizontal route is now verified in Lean.

New theorem:

```lean
componentwiseRolleForZetaZeros_proved : ComponentwiseRolleForZetaZeros
```

This proves that if two points `x < y` in the critical strip satisfy

```lean
horizontalZetaSlice γ x = 0
horizontalZetaSlice γ y = 0
```

then ordinary Rolle's theorem gives:

- a point `c_re ∈ (x, y)` where `deriv (horizontalZetaRe γ) c_re = 0`
- a point `c_im ∈ (x, y)` where `deriv (horizontalZetaIm γ) c_im = 0`

The proof uses:

- `exists_deriv_eq_zero` from mathlib's Rolle theorem
- `differentiableAt_riemannZeta` away from `s = 1`
- the fact that the whole interval lies inside `x < 1`, so `u + iγ ≠ 1`

## Sharpened remaining gap

The remaining local same-height repulsion target is now exactly:

```lean
NoComponentwiseCriticalPairBetweenZetaZeros
```

After discharging the scalar Rolle step, Lean verifies:

```lean
riemannHypothesis_of_componentwiseCriticalPairExclusion :
  NoComponentwiseCriticalPairBetweenZetaZeros → RiemannHypothesis
```

So the next theorem to prove is not generic Rolle. It is a zeta-specific phase
or horizontal-oscillation principle:

> Between two hypothetical same-height zeros of `ζ(x+iγ)`, the real and
> imaginary components cannot both have an interior critical point.

## Why this is still hard

For an arbitrary complex-valued differentiable curve, the statement is false:
both coordinate functions can vanish at two endpoints and both can have interior
critical points. The missing ingredient must use special structure of `ζ`, not
ordinary one-variable calculus.

Viable next directions:

1. Express the obstruction through the horizontal logarithmic derivative
   `ζ'(x+iγ) / ζ(x+iγ)` on zero-free subintervals.
2. Use a horizontal argument-principle statement for the curve
   `x ↦ ζ(x+iγ)` avoiding zero between endpoint zeros after local indentation.
3. Derive sign or monotonicity information for a zeta-specific phase function,
   likely from the functional equation plus Euler-product information where
   available.

