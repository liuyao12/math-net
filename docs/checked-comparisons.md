# Checked comparisons

Math-net hosts small Lean comparison files rather than duplicating upstream
proof developments. A comparison specializes two routes to a common target
proposition and records both checked proof terms.

For the square-root benchmark, MathNet separates two honest situations:

- `MathNetwork.SqrtTwo.irrational` is the mathlib corollary `Irrational (√2)`;
- the general mathlib and computable-analysis square-root criteria are kept as
  a `FoundationAlignedComparison`, because their native propositions use `ℝ`
  and `ComputableAnalysis.RealRaw` respectively;
- the rational-square criterion is displayed as their shared mathematical
  core, without claiming that Lean has identified the two real-number types.

`CheckedComparison` forces every route in its list to have the same proposition
type. `tools/CheckComparison.lean` supplies a representative direct
definitional-equality check, while graph generation checks every exact merged
pair with Lean's `isDefEq` procedure:

```sh
tools/check-comparisons.sh
```

The graph merger uses exact elaborated proposition statements to propose
joins; `tools/build-graph.sh` then rejects any exact join that the Lean kernel
does not accept definitionally. The explicit comparison registry records why
an alignment is intended and which repository supplies each route. It never
turns a foundation-aligned pair into an exact merge. `tools/ExportComparisons.lean`
exports this metadata to `MathNetwork/Graph/comparisons.json` before the graph
is generated.
