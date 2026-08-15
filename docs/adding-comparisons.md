# Adding a proof comparison

MathNet owns the comparison layer, not copied proof bodies. Import the
completed theorem from its source development and write the smallest local
adapter that makes the intended comparison explicit.

## 1. Decide which kind of comparison it is

Use an **exact merge** only when the routes have definitionally equal Lean
proposition types in the same elaboration environment. Typical examples are a
local specialization and an imported theorem such as `Real.cos_add`.

Use a **foundation-aligned comparison** when the mathematics is parallel but
the propositions use different representations, such as `ℝ` and
`ComputableAnalysis.RealRaw`. Do not add an equality edge or call the node a
merged proposition. Instead record the checked bridge theorem that expresses
their shared mathematical core, if one exists.

## 2. Add minimal adapters

Place adapters under `MathNetwork/Comparisons/`. Each declaration should:

- import the upstream completed result;
- expose a useful application-facing statement;
- prove it with a short checked term; and
- preserve the native representation of its source foundation.

An adapter that simply invokes an equivalent imported theorem is valuable, but
it is not an independent proof. The graph generator detects the collapsed call
and labels the route as an adapter that delegates to the imported declaration.

## 3. Register the comparison

Add an exact common target as a `CheckedComparison` in
`MathNetwork/Comparisons/Registry.lean`. Lean's type of `CheckedProof` forces
all listed proof terms to prove the same `Prop`.

For a non-identical pair, add a `FoundationAlignedComparison` with its two
repository declarations, native foundations, explanatory note, and any shared
mathematical core. This is an orientation record, never evidence of
definitional equality.

## 4. Regenerate and check

Run:

```sh
tools/build-graph.sh
tools/check-comparisons.sh
```

The first command extracts actual `used-in-proof` edges, merges only proposed
exact statements, and generates Lean `isDefEq` checks for every exact
multi-route node. It fails if any claimed exact merge is rejected by the Lean
kernel. The second command reruns the representative and generated checks
against the committed graph.

## 5. Inspect the result

Run the explorer locally:

```sh
python3 -m http.server 4173
```

Open `http://localhost:4173/web/`, search for the adapter, and inspect all
routes. Exact merges show one shared formal statement; foundation-aligned
comparisons show the route statements separately. The graph arrows must remain
strictly `used-in-proof`; route color, source, shared inputs, and delegation
are annotations rather than extra edge types.
