# Theorem catalogue

`MathNetwork/Graph/theorem-catalogue.json` is the theorem-centred index over
the generated Lean declaration graph. It is deliberately separate from the
declaration graph:

- a theorem node represents a mathematical statement;
- `formalizations` records declarations that state it;
- `proofs` records locally checked proof routes for those declarations;
- `dependencies.uses` and `dependencies.usedBy` retain the actual Lean edges;
- `externalFormalizations` is reserved for declarations imported from other
  repositories;
- `identity.equivalenceEvidence` is reserved for explicit, checked claims
  that two statements are mathematically equivalent.

The top-level `libraryTheorems` array inventories imported mathlib theorem
declarations separately from project theorem nodes. Each entry retains its
elaborated statement and mathlib locator, so later repositories can be added
as alternate formalizations without conflating a library theorem with a local
proof route.

For now, theorem identity is automatic only when the elaborated Lean
statements are identical. Similar-looking statements are not merged merely
because they have the same informal meaning.

Regenerate it with the checked graph pipeline:

```sh
tools/build-graph.sh
```

The pipeline exports comparison metadata, proposes exact merges from
elaborated statements, and then asks Lean's `isDefEq` checker to validate every
exact multi-route merge before publishing the graph artifact.
