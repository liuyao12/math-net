import MathNetwork.Graph.Extract
import MathNetwork.Fermat.Registry
import MathNetwork.Euler.Applications
import MathNetwork.Comparisons.List100
import MathNetwork.Comparisons.RationalSquares
import MathNetwork.Comparisons.MathlibIrrationalSqrt
import MathNetwork.Comparisons.IrrationalSqrtTwo
import MathNetwork.Comparisons.ComputableIrrationalSqrt

/-! Combined extractor for local use.

CI invokes the smaller domain extractors from `tools/build-graph.sh`: loading
all mathlib and computable-analysis imports in one Lean process exceeds a
standard hosted runner's memory budget.  This entrypoint remains convenient
for a developer with sufficient memory.
-/

build_project_graph
