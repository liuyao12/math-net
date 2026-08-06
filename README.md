# math-net

`math-net` is a research and engineering project for comparing formalized
mathematics by its theorem dependencies.

The intended release name, local folder, and GitHub repository name are all
`math-net`.

## Interactive explorer

The first network browser is in [`web/`](web/). It reads the typed Fermat graph,
supports proposition search, proof-family focus, relationship filters, and
click-to-inspect ramifications. Run `python3 -m http.server 4173` from the
repository root and open <http://localhost:4173/web/>.

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

## Benchmark philosophy

The primary benchmarks are concrete functions, constants, and calculations,
not isolated abstract theorem statements. Abstract theorem matching can be
unfair: one library may already have a highly packaged result, while the
other must expose the representation and construction that make the result
meaningful.

Each benchmark must require both developments to define or identify the
concrete objects, state the application-level result, prove it through an
auditable route, and provide an executable or effective calculation where the
foundation supports one.

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

The primary graph will be a typed, directed multigraph.

- **Nodes:** definitions, theorem declarations, structures/interfaces,
  typeclasses, axioms, and source modules.
- **Edges:** declaration dependency, imported-module dependency,
  typeclass/instance dependency, representation bridge, and theorem
  translation or correspondence.
- **Annotations:** source, namespace, statement hash, assumptions,
  computational content, axiom profile, proof size/cost, and domain tags.

Import graphs are useful orientation, but the main object is the declaration
graph extracted from elaborated Lean declarations and proof terms. A theorem
that happens to import a large module should not automatically inherit the
whole module's conceptual dependency set.

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

## Proposed first deliverable

Build a reproducible extractor that emits normalized JSON for each declaration:

```text
declaration -> direct constants -> transitive constants
             -> imports / modules
             -> axioms
             -> statement fingerprints and domain tags
```

Then add a hand-reviewed correspondence table for the first benchmark. The
network visualization and cost metrics should come after this corpus is stable;
otherwise graph size will obscure the mathematical comparison.

## Scope discipline

The network is evidence for dependency structure, not a single score for a
foundation. A theorem can be computationally meaningful without being a
textbook analogue, and several presentation theorems can share one underlying
bridge. We should preserve those distinctions in the data model.

## Proof families

The graph should preserve alternative proofs of the same concrete target.
They are not redundant copies: their shared core and divergent obligations are
part of the mathematical landscape.

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

The network should therefore include proof-route nodes and correspondence
edges, not only theorem-dependency edges. A single target may have several
routes, and a lemma such as norm multiplicativity may support one route while
the fixed-point involution supports another. This makes it possible to ask
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

## Pedagogical mode

The long-term purpose is not only to measure proof dependencies, but to let a
reader explore the ramifications of a proposition. A proposition page should
show its statement, concrete examples, proof routes, prerequisites,
equivalent formulations, special cases, generalizations, computational
experiments, and historical or geometric interpretations.

These relationships must be typed. In particular, the graph should distinguish

- **uses:** a declaration is needed by a proof;
- **proves:** a route establishes the proposition;
- **equivalent:** two formulations describe the same mathematical content;
- **specializes:** a general statement yields a concrete instance;
- **generalizes:** a statement extends the scope of another;
- **reinterprets:** the same structure receives a geometric, algebraic, or
  computational meaning; and
- **motivates:** a proposition naturally leads to a later construction without
  being a formal dependency.

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
