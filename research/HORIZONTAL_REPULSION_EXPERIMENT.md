# Horizontal Repulsion Experiment

## Target Tested

We tested the analytic target formalized in `Reinmann/HorizontalRepulsion.lean`:

```lean
HorizontalStrictMidpointConvexZeta
```

Informally:

```text
x ↦ ‖ζ(x + iγ)‖² is strictly midpoint-convex on 0 < x < 1
```

Lean verifies that this target would imply RH:

```lean
riemannHypothesis_of_horizontalStrictMidpointConvex :
  HorizontalStrictMidpointConvexZeta → RiemannHypothesis
```

## Numerical Result

The global strict-convexity target appears false.

Using `mpmath` with 40 digits, a grid search found:

```text
γ = 0.5
x = 0.66
y = 0.98
mid = 0.82

‖ζ(mid + iγ)‖² ≈ 3.0092902087845057592
(‖ζ(x + iγ)‖² + ‖ζ(y + iγ)‖²)/2 ≈ 2.9997768238141877056
```

This violates strict midpoint convexity because the midpoint value is larger
than the endpoint average.

## Conclusion

The convexity route is useful as a failed experiment:

- It gives a clean Lean-verified implication to RH.
- It shows what kind of same-height repulsion would be sufficient.
- But global midpoint convexity of `‖ζ(x+iγ)‖²` is too strong.

The next viable target should be weaker and local to zeros, for example:

```text
If ζ(x+iγ)=ζ(y+iγ)=0 with x≠y, then a local zero-counting or phase/argument
constraint is violated.
```

That suggests shifting from convexity of the squared modulus to a horizontal
curve/argument principle for `x ↦ ζ(x+iγ)`.
