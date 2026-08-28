# Reader journeys through the mathematical landscape

These are short guided readings of checked dependency graphs. They are not
informal proofs replacing Lean: every displayed arrow is a `used-in-proof`
dependency recovered from the elaborated declarations. The surrounding prose
only tells the reader where to look first.

## 1. Irrationality of √2: a concrete theorem with an upstream comparison

Open [irrationality of √2](https://liuyao12.github.io/math-net/?comparison=irrational-sqrt-two).

1. Start with the ordinary statement: √2 is not rational. This is a fully
   checked low-level application, not yet advertised as two alternative
   proofs.
2. Follow the graph upward to the rational square-root criterion. The real
   comparison happens there: for nonnegative rational `q`, the question is
   whether √q is irrational exactly when `q` is not a rational square.
3. Click the **Rational-square bridge**. Its reading note explains that the
   arithmetic predicate “q is a square” has been aligned independently of how
   either project constructs its real numbers.
4. Open the upstream foundation-aligned comparison for irrational square roots
   of rationals. Its Mathlib route uses completed real numbers; its
   computable-analysis route uses `RealRaw`. The graph deliberately keeps
   these colored routes distinct until a checked representation bridge exists.

The lesson is that a familiar corollary can sit below a more informative
foundational comparison. The visual merge point should be placed where the
formal statements genuinely meet, rather than duplicated at every corollary.

## 2. Fermat’s two-square theorem: two proof architectures

Open [Fermat’s two-square theorem](https://liuyao12.github.io/math-net/?comparison=fermat-prime-two-squares).

1. The theorem says that a prime `p ≡ 1 mod 4` is a sum of two squares. Its
   node is an **exact merge**: Lean has checked that the two routes prove the
   same proposition type.
2. Select the Mathlib-colored Gaussian-integer route. The route’s key bridge
   is the **Gaussian-integer criterion for a sum of two squares**: a
   nontrivial factorization of a natural prime in ℤ[i] yields `p = a² + b²`.
   The surrounding dependencies show the arithmetic needed to obtain that
   factorization from the congruence condition.
3. Return to the theorem and select the math-net-colored Zagier involution
   route. Its source makes the different architecture visible: a finite set,
   two involutions, and a parity comparison of fixed-point sets.
4. Use the proof map to compare the nearest named inputs for each route. The
   colored arrows record only declarations used in the selected proof body;
   a shared node means the same checked declaration is genuinely reused.

The lesson is that a single proposition may be the meeting point of genuinely
different mathematical arguments, not merely different names for an imported
lemma.

## 3. Cosine addition: Euler’s formula used as a method

Open [cosine addition](https://liuyao12.github.io/math-net/?comparison=cosine-addition).

1. The target is geometric/trigonometric in form:
   `cos(x + y) = cos x cos y − sin x sin y`. It does not mention a complex
   exponential in its statement.
2. Select the Mathlib route to see the standard real-trigonometric theorem.
3. Select the math-net Euler route. Its proof idea explains the actual move:
   apply `exp((x + y)i) = exp(xi) exp(yi)`, then take real parts.
4. Click **Exponential addition law** when it appears above the route. Its
   note identifies it as the algebraic engine of the derivation, while the
   `Complex` structure remains a visible mathematical endpoint rather than a
   field-level implementation tree.

The lesson is that Euler’s identity and complex exponentials are valuable not
because they abbreviate definitions, but because they reorganize a proof of a
statement whose mathematical content is trigonometric.

## Reading conventions

- Read arrows upward: the upper declaration is used in the Lean proof of the
  lower one.
- A colored route is a repository-provenance choice, not an extra kind of
  mathematical edge.
- Gold-outlined square nodes are deliberately visible mathematical
  foundations. Expand them only when the chosen construction matters to the
  question being asked.
- Faded nodes are still checked dependencies. Selecting one says whether it
  is a supporting prerequisite, routine step, or Lean implementation detail.
