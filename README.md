# math-net

`math-net` is an interactive observatory for navigating formalized mathematics
by its theorem dependencies. It is not intended to become another repository
of major theorem proofs. Those proofs should remain in mathlib,
`computable-analysis`, and other specialist repositories; math-net imports and
cross-references them.

The intended release name, local folder, and GitHub repository name are all
`math-net`.

## Interactive explorer

The first network browser is in [`web/`](web/). By default it reads the
generated project-wide Lean declaration graph, currently containing 2,155
nodes and 20,817 checked dependency edges. It supports theorem selection,
multi-level neighborhood fading, proposition search, strict proof-dependency
edges, structural-landmark highlighting, background-detail suppression, and
click-to-inspect Lean source. The default theorem view shows mathematical
declarations only; supporting foundations and implementation details can be
revealed independently. When the focus is a corollary or adapter, the explorer
places the strongest upstream bridge theorem at the center of the view. The
choice is a navigation heuristic: it compares the focused proposition's
elaborated statement with nearby mathematical theorems, rewarding distinctive
shared mathematical terms and not proof-automation reuse.
The theorem-centred index is
[`theorem-catalogue.json`](MathNetwork/Graph/theorem-catalogue.json). Run
`python3 -m http.server 4173` from the repository root and open
<http://localhost:4173/web/>.

The first comparison is between:

- Lean/mathlib, where analysis is developed over completed real and complex
  types with topology, filters, measure theory, and classical infrastructure;
- `ComputableAnalysis`, where analysis is developed from rational interval
  algorithms, validity/shrinking certificates, and explicit equivalence
  bridges without importing the usual completed-real analysis machinery.

The goal is not to rank the two foundations. It is to make their different
dependency landscapes inspectable: which definitions are needed, which
assumptions enter a theorem, which proof paths are reusable, and where a
foundational choice changes the downstream cost of calculus.

## Comparison propositions

The primary comparison units are small, application-facing propositions, not
new formalizations of major theorems. A math-net benchmark imports an existing
result, specializes it to a useful common case, and supplies only the minimal
Lean adapter needed to compare it with a result from another repository.

Each benchmark records the common target, the representation of important
objects, the imported declarations used by each route, and any checked bridge
between the two representations. The substantial proof remains in its source
repository.

For constants such as \(\pi\), the benchmark must record what the constant
means in each development. `Real.pi`, a circumference-derived raw real, an
inverse-function construction, and a rotation parameter are not silently
treated as interchangeable. Their equivalence is part of the benchmark.

## Initial research questions

1. Which theorem statements are genuinely common to both developments?
2. Where does mathlib use completeness, directly or through a transitive
   dependency?
3. Which computable-analysis certificates replace that dependency, and what
   new data or proof obligations do they require?
4. How do the two dependency networks differ for limits, continuity,
   derivatives, integration, infinite series, inverse functions, and ODEs?
5. Can we distinguish a theorem's mathematical assumptions from artifacts of
   its representation or library organization?

## Network model

The primary graph is a typed, directed graph.

- **Nodes:** definitions, theorem declarations, structures/interfaces,
  typeclasses, axioms, and source modules.
- **Edges:** currently only the kernel-derived `used-in-proof` relation.
  Correspondence and equivalence evidence are stored as catalogue metadata
  until they have their own checked representation.
- **Annotations:** source, namespace, statement hash, assumptions,
  computational content, axiom profile, proof size/cost, and domain tags.

Import graphs are useful orientation, but the main object is the declaration
graph extracted from elaborated Lean declarations and proof terms. A theorem
that happens to import a large module should not automatically inherit the
whole module's conceptual dependency set.

### Library proofs and selected routes

The presence of a complete mathlib proof does not close the route list. Each
proposition may carry several proof records, distinguished by their intended
role:

- a **library-complete** route records the most general imported theorem or
  interface;
- a **pedagogical-narrow** route intentionally works through a smaller
  interface, such as a Riemann integral instead of mathlib's general measure
  integral;
- a **foundation-comparison** route is chosen to expose a different
  dependency boundary, for example a computable or geometric construction.
- an **adapter** route is a deliberately minimal local wrapper around an
  equivalent imported theorem. It is kept to record the comparison boundary,
  but the explorer marks its delegation rather than presenting it as an
  independent proof.

The route is still conditional when it treats imported lemmas as black boxes.
Its status means that the local Lean term checks; its `closure` and
`blackBoxes` fields say how much of the surrounding library has been opened.
Thus “mathlib already proves it” and “math-net has indexed this route” are
separate facts. A computable-analysis comparison should normally add a bridge
proposition such as “this certified interval function induces a
mathlib-continuous function,” rather than reproduce the whole calculus proof.

## First benchmark suite

Start with a small matched corpus of concrete applications rather than all of
mathematics:

1. Euler's identity, tied to a concrete quarter-turn or rotation calculation;
2. a derivative calculation such as `d/dx (x * arctan x)`;
3. a definite integral calculation such as a reciprocal-quadratic integral
   for \(\pi\);
4. a power-series evaluation such as \(e\), \(\pi\), or a Basel-type sum;
5. a concrete inverse-function calculation such as `sqrt 2` or `log 2`;
6. a solved linear ODE with explicit initial data.

For each application, record the common target, the representation of every
important constant or function, and one formal route in each project. The
standard route must not use Euler's identity, a prepackaged value of \(\pi\),
or an equivalent theorem as an unexplained black box when that result is the
target. In particular, “does not use completeness” must be backed by an audit
of imports, declarations, and axioms—not only by comments in the source.

Euler's identity is especially valuable: the standard development must say
which definition of \(\pi\) connects the complex exponential to the geometric
half- or quarter-turn, while the computable development must produce the
corresponding certified rotation or interval calculation.

## Candidate geometric benchmarks

A useful algebraic control is Gaussian multiplication without mentioning
complex numbers. Define

```text
compose (a,b) (c,d) = (a*c - b*d, a*d + b*c)
normSq (a,b) = a*a + b*b
```

and prove the concrete identity

```text
normSq (compose (a,b) (c,d)) = normSq (a,b) * normSq (c,d).
```

This is the sum-of-two-squares composition law, stated purely over integers
or rationals. Geometrically it says that a scaled rotation composes with
another scaled rotation and multiplies squared lengths. A numerical instance
such as `(3,4)` composed with `(5,12)` gives `(−33,56)` and preserves the
corresponding norm calculation. This is a good baseline because it should not
depend on completeness, topology, or transcendental definitions.

A more analytic geometric benchmark is the composition of planar rotations,
stated in coordinates rather than with \(i\):

```text
R α (R β (x,y)) = R (α + β) (x,y)
```

whose coordinate theorem contains

```text
cos (α + β) = cos α * cos β - sin α * sin β
sin (α + β) = sin α * cos β + cos α * sin β.
```

The statement is geometric—composition of rotations—and does not mention
complex exponentials. The dependency network can then reveal whether a given
library proves it geometrically, through power series, or through an
exponential representation. Concrete rational-angle instances can serve as
the executable core, while angle/arc-length or circle-geometry instances add
the analytic layer where the definitions of \(\pi\) and completeness become
visible.

## Data and visualization layers

The small Lean layer builds a reproducible declaration graph and minimal
comparison propositions. The catalogue layer organizes each theorem as a
statement with formalizations, imported proof records, reverse dependencies,
and reserved cross-repository/equivalence fields. The visualization layer is
the main product: it lets a reader move through the resulting landscape,
select a theorem, fade unrelated regions, inspect checked Lean source, and
follow dependencies upward and outward.

The extractor emits normalized JSON for each declaration:

```text
declaration -> direct constants -> transitive constants
             -> imports / modules
             -> axioms
             -> statement fingerprints and domain tags
```

Then add hand-reviewed correspondence records only where a specialized common
proposition has been checked. The graph remains useful while the catalogue is
growing; it is not postponed until a complete corpus exists.

## Scope discipline

The network is evidence for dependency structure, not a single score for a
foundation. A theorem can be computationally meaningful without being a
textbook analogue, and several presentation theorems can share one underlying
bridge. We should preserve those distinctions in the data model.

## Proof families

The graph should preserve alternative proofs of the same target when those
proofs are imported from their source repositories. They are not redundant
copies: their shared core and divergent obligations are part of the
mathematical landscape. math-net supplies the organization and navigation,
not a second home for the proof bodies.

Fermat's two-square theorem is a model case. A benchmark can begin with
concrete instances such as \(29=5^2+2^2\), then compare routes toward the
general statement for primes congruent to \(1\) modulo \(4\):

- Gaussian-pair arithmetic, using norm composition and a Euclidean or descent
  argument;
- an elementary fixed-point proof based on an involution;
- the geometric reinterpretation in terms of lattice points, disks, or
  rotations;
- a computational search or certified finite construction for individual
  primes.

The network therefore stores proof routes as metadata on theorem declarations,
while retaining **only** kernel-derived `used-in-proof` arrows in the graph.
A single target may have several routes, and a lemma such as norm
multiplicativity may support one route while the fixed-point involution
supports another. This makes it possible to ask
which parts of a result are geometric, algebraic, combinatorial, or
computational, and which choices cause those routes to converge or diverge.

The arctangent identities behind Machin's formula provide a second strong
family. A target such as

```text
arctan (1/2) + arctan (1/3) = arctan (1)
```

can be stated using real angles and interpreted geometrically as composition
of planar slopes or rotations. The corresponding rational identity is

```text
(1/2 + 1/3) / (1 - (1/2) * (1/3)) = 1.
```

The Machin instance

```text
π = 16 * arctan (1/5) - 4 * arctan (1/239)
```

forces the project to track what \(\pi\) means, how angle composition is
represented, and how the identity connects to a concrete circle or rotation
construction. It also admits genuinely different routes: geometric angle
addition, tangent rationalization, power-series evaluation, and certified
interval computation. This makes it a natural bridge between the algebraic
Fermat family and the later calculus network.

The initial external comparison target is the local `ComputableAnalysis`
checkout at `/Users/liuyao/Documents/Codex/projects/computable-analysis` and a
pinned mathlib revision recorded by this repository.

The first application is documented in
[`docs/fermat-application.md`](docs/fermat-application.md).
Twenty further calculus and computable-analysis applications are proposed in
[`docs/application-catalog-twenty-more.md`](docs/application-catalog-twenty-more.md).
The revised outside-computable-analysis catalog is in
[`docs/application-catalog-outside-computable-analysis.md`](docs/application-catalog-outside-computable-analysis.md).
The analysis-facing starting tranche from Wiedijk's 100 Theorems list is in
[`docs/100-theorems-calculus-corpus.md`](docs/100-theorems-calculus-corpus.md).
The checked Fermat application and its proof routes live in
`MathNetwork/Fermat/Registry.lean`; the supporting declaration graph is
generated from the elaborated Lean environment.

For the precise workflow for adding an exact merged proposition, a local
adapter, or a foundation-aligned comparison, see
[`docs/adding-comparisons.md`](docs/adding-comparisons.md).

## Pedagogical mode

The long-term purpose is not only to measure proof dependencies, but to let a
reader explore the ramifications of a proposition. A proposition page should
show its statement, concrete examples, proof routes, prerequisites,
equivalent formulations, special cases, generalizations, computational
experiments, and historical or geometric interpretations.

The strict network view deliberately has one edge relation: **used-in-proof**.
An arrow means that the source declaration or imported result is used in the
proof represented by the target node. Equivalence, specialization, historical
motivation, and geometric reinterpretation belong in separate atlas views or
node metadata; they must not masquerade as proof dependencies.

math-net is not a duplicate of `computable-analysis`. When a relevant result
already exists there, math-net should import or cite its Lean declaration and
record the dependency boundary. The local Fermat development is for concrete
applications, proof-route comparisons, and missing formalizations. For example,
an arctangent benchmark may use a checked mathlib identity even if that
identity's deeper analytic implementation passes through `exp`; the transitive
route belongs in the dependency data.

For the two-square theorem, an exploratory path might begin with
`29 = 5² + 2²`, move to the prime existence theorem, compare the involution
and Gaussian proofs, continue to uniqueness, then broaden to the representation
count `r₂(n)` and its Dirichlet-series identity

```text
sum (r₂ n / n^s) = 4 * ζ(s) * L(s, χ₄).
```

That path should make clear where the mathematics branches: the trigonometric
and Machin route studies angle composition and \(\pi\), while the Gaussian
and arithmetic route studies norms, representations, and \(L\)-functions.
They share useful structures without being collapsed into one proof.
