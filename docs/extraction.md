# Lean declaration extraction

`tools/Extract.lean` is the first, intentionally small, extraction format for
math-net. It runs in Lean's elaborated environment, so declaration bodies are
inspected after elaboration rather than inferred from source text.

Run it with one or more fully qualified declarations:

```sh
tools/extract.sh MathNetwork.Fermat.witness29Route \
  MathNetwork.Fermat.zagierInvolutionRoute
```

The command prints one JSON object. Its top-level fields are `imports` and
`declarations`. Imports are module-level information and are intentionally
separate from declaration dependencies.

Each declaration record contains:

- `direct_constants`: constants occurring immediately in the declaration type
  or value (proof term included), excluding the declaration itself;
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
