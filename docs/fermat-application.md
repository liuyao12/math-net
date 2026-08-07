# Fermat’s sum-of-two-squares theorem

Math-net begins with one low-level application/problem:

> Every prime congruent to `1 mod 4` is a sum of two squares.

The proposition is `MathNetwork.Fermat.fermatPrimeTwoSquares`. Its proof records
are deliberately kept separate from the proposition:

- `gaussian-euclidean`: Mathlib’s maintained Gaussian-integer route;
- `zagier-involution`: the finite-set, fixed-point/involution route.

Concrete arithmetic examples, negative examples such as `7`, representation
counts, arctangent identities, and geometric warm-ups are not separate
application nodes. They belong later as explanatory material beneath this one
problem, if needed.
