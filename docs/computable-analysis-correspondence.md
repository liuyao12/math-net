# Computable-analysis correspondence

The first math-net application is the single proposition

```text
∀ p, Prime p → p % 4 = 1 → ∃ a b, a² + b² = p.
```

The local Lean proposition is
`MathNetwork.Fermat.fermatPrimeTwoSquares`. Its two registered proof routes
are:

| Route | Lean status | Role of computable-analysis |
|---|---|---|
| Gaussian Euclidean | kernel-checked through Mathlib | standard algebraic baseline |
| Zagier involution | kernel-checked using Mathlib’s archived development | independent proof organization based on finite involutions |

The Gaussian pair operations in `MathNetwork/Fermat/Basic.lean` are supporting
algebra for the first route, not separate benchmark applications. Concrete
examples, negative examples, representation counts, and arctangent identities
are intentionally excluded from the application graph.
