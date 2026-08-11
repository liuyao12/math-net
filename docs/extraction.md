# Lean declaration extraction

`tools/Extract.lean` is the first, intentionally small, extraction format for
math-net. It runs in Lean's elaborated environment, so declaration bodies are
inspected after elaboration rather than inferred from source text.

Run it with one or more fully qualified declarations:

```sh
tools/extract.sh MathNetwork.Fermat.gaussianEuclideanRoute \
  MathNetwork.Fermat.zagierInvolutionRoute
```

The command prints one JSON object. Its top-level fields are `imports` and
`declarations`. Imports are module-level information and are intentionally
separate from declaration dependencies.

Each declaration record contains:

- `direct_constants`: constants occurring immediately in the declaration type
  or value (proof term included), excluding the declaration itself;
- `graph_direct_constants`: a compact graph-facing projection of direct
  constants, retaining project declarations plus selected `Complex` and
  `Real` declarations while omitting tactic implementation noise;
- `transitive_constants`: the closure obtained by recursively following those
  constants, excluding the root declaration;
- `axioms`: Lean's transitive axiom report, including imported declarations'
  precomputed axiom data;
- `proof_route`: `null`, or route metadata identified from the `ProofRoute P`
  type. Its `name` and `description` are decoded from the route value; the
  certified proof is represented in the constant dependency fields.

This deliberately does not call imports “dependencies”: importing a large
module does not imply that every declaration in that module occurs in a proof
term. A direct constant is a kernel-level occurrence in the elaborated
type/value, not automatically a mathematical lemma edge. JSON arrays are
sorted by declaration name for reproducibility.

## Project-wide graph

`tools/BuildGraph.lean` uses the same elaborated environment to emit
`MathNetwork/Graph/project.json`. It includes every non-internal
`MathNetwork.*` declaration loaded by the project and a bounded three-level
dependency closure of declarations defined in `Mathlib.*` or
`ComputableAnalysis.*` modules. The extractor inspects both the declaration
type and the elaborated value, so local adapter proofs expose the imported
theorems and definitions they actually call. Theorems are proposition nodes,
definitions are concept nodes, and imported declarations are source nodes.
The only generated edge is `used-in-proof`, from a declaration used by
another included declaration to the declaration that contains it.

Each node also receives a structural-importance annotation. It reports direct
proof reuse and the number of downstream declarations reachable from the node.
This is a navigation heuristic, not a measure of proof difficulty or
mathematical depth; the UI labels it as such.

The merge pass also attaches a presentation role to each declaration:
`mathematical`, `supporting`, `routine`, or `implementation`. This is an
explicit heuristic for reading the graph, never a Lean-level classification.
Generated constructors/recursors are implementation details; small theorems
from foundational `*.Defs` modules are routine details (for example `mul_one`
and `Nat.prime_two`). Routine and implementation nodes are suppressed by
default and visually contracted, but remain in the extracted graph and can be
revealed with the background-details control.

`tools/MergeGraph.py` then merges proposition nodes only when their elaborated
statements are identical. The comparison registry and `CheckComparison.lean`
provide the kernel-backed check for comparison units; the merger does not infer
mathematical equivalence from similar text. Concept/definition nodes remain one
per declaration. Each declaration contributing to a merged proposition becomes
a proof-provenance record, and its dependency edges retain that record in the
`proof` field so the UI can color proof routes independently.

Regenerate it after changing the imported project surface with:

```sh
tools/build-graph.sh
```
