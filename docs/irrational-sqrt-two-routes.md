# Irrationality of √2: two routes

The first comparison in math-net is deliberately theorem-centred. The
mathematical target we want to identify is

```lean
Irrational (√2)
```

## mathlib route — checked

The local wrapper is

```lean
import Mathlib.NumberTheory.Real.Irrational

namespace MathNetwork.SqrtTwo

theorem irrational : Irrational (√2) :=
  irrational_sqrt_two

end MathNetwork.SqrtTwo
```

The underlying mathlib declaration is
[`irrational_sqrt_two`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/Real/Irrational.lean).
Its proof is intentionally short because mathlib has already proved the
general chain:

```text
prime number → not a square → irrational square root
```

In particular, the theorem body is `simpa using Nat.prime_two.irrational_sqrt`.
The general irrationality proof internally uses the canonical numerator and
denominator of a rational, together with their coprimality; the wrapper does
not expose that machinery as part of its local statement.

## Tao Analysis route — infinite descent, external reference

Tao's Analysis I formalization states the related rational proposition

```lean
theorem Rat.not_exist_sqrt_two : ¬ ∃ x : ℚ, x ^ 2 = 2 := by
  ...
```

The source is [`Analysis/Section_4_4.lean`](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_4.lean), under
“Proposition 4.4.4 / Exercise 4.4.3”. Its route is structurally different:

1. Assume a rational `x` whose square is `2`.
2. Extract positive naturals `p q` with `p^2 = 2*q^2`; no reduced fraction is
   chosen.
3. From any positive solution, construct a smaller positive solution.
4. Iterate that construction and contradict `Nat.no_infinite_descent`.

The current upstream file is a faithful but incomplete translation: it still
contains `sorry`s in the parity and strict-descent sublemmas. Therefore it is
listed here as an external proof design, not as a checked formalization in
math-net. This distinction is important for the graph's verification badges.

## Statement alignment to inspect

The two displayed propositions are not definitionally identical:

```lean
Irrational (√2)
¬ ∃ x : ℚ, x ^ 2 = 2
```

The second is a rational-square formulation. To compare proof routes at one
node, we will eventually need a checked bridge theorem translating between it
and the real-valued `Irrational (√2)` statement. That bridge is precisely the
kind of “massaging” we should inspect before adding it.
