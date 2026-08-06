# Computable-analysis correspondence

This is a hand-reviewed correspondence for the local `math-net` checkout and
`/Users/liuyao/Documents/Codex/projects/computable-analysis`. It follows the
charter's rule that a familiar formula is not enough: the object represented,
the proof certificate, and the representation bridge must be recorded
separately.

Status labels below mean **proved** when the cited source contains a theorem,
**interface** when it is a definition/structure or a target proposition, and
**charter-only** when `math-net` currently describes the benchmark but has not
implemented it.

## Benchmark A: norm composition

Common target, stated without complex numbers:

```text
compose (a,b) (c,d) = (a*c - b*d, a*d + b*c)
normSq (a,b) = a*a + b*b
normSq (compose z w) = normSq z * normSq w
```

The concrete control instance is `compose (3,4) (5,12) = (-33,56)` and the
Fermat witness is `normSq (5,2) = 29`.

| Mathematical object or obligation | `math-net` / mathlib side | ComputableAnalysis side | Common content | Import versus re-prove |
|---|---|---|---|---|
| Pair carrier | `MathNetwork.Fermat.GaussianPair`, with `re im : Int` | No named Gaussian-pair carrier in the benchmark path; the closest certified carrier is `QComplex`/`ComplexRaw` in `ComplexMultiplication.lean` | A two-coordinate commutative-algebra carrier | Import the mathematical schema only. Re-prove the carrier adapter: either an `Int`/`Rat` pair or a map from pairs to the project's complex representation. |
| Multiplication | `GaussianPair.mul` in `MathNetwork/Fermat/Basic.lean` | `QComplex.mul`, interval-box `QBox.mul`, and `ComplexRaw.mul` | `(ac-bd,ad+bc)` | Reuse the formula and concrete arithmetic. Re-prove the representation theorem that interval multiplication encloses the pointwise product; use `QBox.mul_contains`/`ComplexRaw.mul_valid` where applicable. |
| Squared norm | `GaussianPair.normSq : GaussianPair → Int` | No matching public `normSq` theorem is needed for the raw-real benchmark; coordinate bounds and complex multiplication are available | Sum of coordinate squares | Re-prove the small definition at the chosen carrier. Do not identify it definitionally with a complex modulus or with a completed-real norm. |
| General multiplicativity | `normSq_mul`, proved by `simp` and `ring`; packaged as `pairAlgebraRoute` proving `normComposition` | No directly corresponding named theorem in the inspected modules | Pure finite polynomial identity | The algebraic proof idea is importable. The theorem itself must be re-proved after the carrier/operation adapter; no completeness or interval shrinking is required for the exact rational/integer version. |
| Concrete multiplication | `concrete_composition`, definitional reduction (`rfl`) | Rational computation can be evaluated exactly; `QBox.mul_point` captures the point-box specialization | Finite exact calculation | Import as a test vector, not as a theorem dependency. Re-prove/evaluate in the computable carrier. |
| `29 = 5² + 2²` witness | `concrete_29` and `witness29Route` | Rational arithmetic can reproduce the witness, but no corresponding Fermat registry entry was found | A finite certificate | Import the witness data and re-prove the arithmetic. The general prime two-squares theorem is out of scope for this correspondence. |
| Computational meaning | Ordinary equality in `Int`, with mathlib tactics and `Mathlib.Data.Nat.Prime.Basic` imported by the file | A computation is a rational box plus validity/nesting/shrinking evidence (`RealRaw.ValidCompute`) | Exact finite algebra versus certified approximation | Import the target formula and examples. Re-prove all representation-level validity/containment obligations only if the benchmark is lifted from exact pairs to `ComplexRaw`; they are not needed for the exact pair theorem. |

### Boundary for benchmark A

This benchmark is a clean shared core. `normSq_mul` should be imported into the
correspondence data as a mathematical analogue, but not claimed to be a
cross-library theorem: its source type is an `Int` pair, whereas the
computable-analysis multiplication infrastructure is interval-valued and
representation-aware. The reusable material is the polynomial identity and the
finite examples; the representation adapter and any enclosure theorem must be
proved in the destination system.

## Benchmark B: Machin's formula for pi

Target formula:

```text
pi = 16 * arctan (1/5) - 4 * arctan (1/239)
```

The computable-analysis implementation defines
`piMachin = 4 * (4 * arctan (1/5) - arctan (1/239))` as a `RealRaw` in
`ComputableAnalysis/Pi.lean`. The inspected project has a substantial proved
Machin route; `math-net` currently has this benchmark only in its charter and
does not yet have a corresponding Machin module.

| Mathematical object or obligation | `math-net` / mathlib side | ComputableAnalysis side | Common content | Import versus re-prove |
|---|---|---|---|---|
| `pi` | Charter explicitly warns that `Real.pi`, circumference, inverse-function, and rotation parameters are not silently interchangeable; no local `pi` implementation yet | Several raw presentations: `piMachin`, `piLeibniz`, `piCircleArea`, `piCircumference`; bridges are expressed with `RealRaw.Equiv` | A distinguished constant plus a proof of representation agreement | Import the requirement to name the pi presentation. Re-prove the chosen bridge in math-net; do not import a theorem as if all pi meanings were definitionally equal. |
| Arctangent | Charter proposes real-angle/tangent identities and Machin as a benchmark, but has no local arctan declarations | `arctan.geom` and `arctan.series` are explicit `FunctionRepresentation`s; geometry is backed by `ArctanGeometry.arctanGeom`, series by the power-series evaluator | A rational-input inverse tangent with a branch/domain condition | Import the rational tangent algebra and benchmark inputs. Re-prove the chosen angle/function semantics and any bridge between geometric and series presentations. |
| Rational tangent addition | Charter gives `(1/2 + 1/3)/(1-(1/2)(1/3)) = 1` as the algebraic control | `RationalCircle.Trigonometry` supplies chart-add parameters/denominators; `PiProofs` contains Machin branch machinery | Finite rational identities and denominator/branch side conditions | Import the finite rational calculation. Re-prove only the bridge from the calculation to the selected angle/arctan representation. |
| Machin branch identity | Charter-only: intended route is angle composition, tangent rationalization, series, and certified computation | Proved route includes `MachinIdentity.geometricMachinUnitAdditions_of_chartTransport`, `geometricBranchIdentity_of_machinUnitAdditions`, and `piMachin_eq_four_arctan_one_of_branchIdentity` | The identity reduces Machin's expression to four copies of the quarter-turn/`arctan 1` value | The theorem cannot be imported verbatim because the representations differ. Import the proof decomposition as a route template; re-prove branch and domain obligations in math-net. |
| Series computation | Charter says executable/effective calculation is part of the benchmark, but has no implementation | `arctan.series`, `piMachin`, `PiProofs.machinValid`, `piMachin_compute_width_eq`, and `piMachin_compute_width_le_geometric_half` provide boxes and a geometric rate (`20/2^n`) | Rational finite approximants with an explicit error certificate | Import the rate as comparison data only. Re-prove an executable evaluator and its rate if math-net adopts represented reals; it is not a theorem about `Real.pi` by itself. |
| Geometric pi agreement | Charter requires the equivalence to be made explicit | `piMachin_equiv_piCircleArea_finiteRiemannBridge` and related route theorems establish raw-real equivalence to the circle-area presentation | A representation bridge, not mere notation | Import the distinction and benchmark shape. Re-prove the bridge against whichever mathlib pi construction is selected; this is the main cost of the benchmark. |
| Computation equality notion | Classical/mathlib equality after choosing the ambient real type | `RealRaw.Equiv` is overlap-based equality of valid shrinking interval algorithms; `Real.Representation.equiv` transports between certified representations | “Same value” is the intended common relation | Import the semantic role, not the definition. A math-net implementation over completed reals can use equality, but must retain a typed correspondence edge to the computable `Equiv` proof rather than erase it. |

### Boundary for benchmark B

The computable-analysis project has more completed infrastructure here than
math-net: it has the raw algorithms, validity/rate certificates, geometric and
series arctangent presentations, and several Machin-to-circle-area bridges.
What is portable is the dependency decomposition:

1. finite rational tangent identities;
2. a branch/domain certificate;
3. a chosen arctangent presentation;
4. a pi presentation;
5. a representation-equivalence bridge; and
6. an optional interval error/rate certificate.

The exact interval algorithms, `RealRaw.ValidCompute`, and overlap-based
`RealRaw.Equiv` are representation-specific. A mathlib proof may reuse the
finite algebra and the route taxonomy, but must re-prove the semantic bridge
to its selected `pi` and `arctan` objects. Conversely, a computable proof can
reuse the Machin rational identity but cannot import a theorem stated over
mathlib's completed `ℝ` without first constructing an explicit representation
map.

## Recommended correspondence records

For the declaration graph, record each row above as a typed edge rather than a
single “same theorem” edge:

| Edge type | Example |
|---|---|
| `equivalent` | `math-net` pair norm identity ↔ computable exact rational pair norm identity |
| `reinterprets` | `GaussianPair.mul` ↔ complex/rotation multiplication |
| `specializes` | General norm multiplicativity ↦ `(3,4)·(5,12)=(-33,56)` |
| `uses` | Machin bridge uses finite tangent identity plus branch certificate |
| `proves` | `piMachin_equiv_piCircleArea_finiteRiemannBridge` proves a computable representation agreement |
| `motivates` | Charter's Machin benchmark motivates adding a math-net pi/arctan representation layer |

The first benchmark is therefore suitable as the low-cost algebraic control;
the second is the representation-sensitive benchmark that exposes where
“import” ends and “re-prove” begins.
