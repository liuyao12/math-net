# Checked comparisons

Math-net hosts small Lean comparison files rather than duplicating upstream
proof developments. A comparison specializes two routes to a common target
proposition and records both checked proof terms.

For the square-root-of-two benchmark:

- `MathNetwork.SqrtTwo.irrational` proves `Irrational (√2)` through mathlib;
- `MathNetwork.SqrtTwo.irrational_descent` proves the same target through the
  infinite-descent core imported from `computable-analysis`;
- `MathNetwork.Comparisons.irrationalSqrtTwo` stores both proof terms in one
  `CheckedComparison` value.

The comparison registry forces both route fields to have the same proposition
type. `tools/CheckComparison.lean` additionally asks Lean's definitional
equality procedure to compare the elaborated declaration types:

```sh
tools/check-comparisons.sh
```

The graph merger uses exact elaborated proposition statements to join the
dependency graphs. The explicit comparison registry records why that merge is
intended and which repository supplies each route; it does not replace the
kernel check.
