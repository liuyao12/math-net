import Mathlib.NumberTheory.Real.Irrational

/-!
# Irrationality of the square root of two

This is the mathlib route in the checked comparison for `Irrational (√2)`.
The common proposition is specialized here so it can be compared directly
with the computable-analysis infinite-descent route.
-/

namespace MathNetwork.SqrtTwo

theorem irrational : Irrational (√2) :=
  irrational_sqrt_two

end MathNetwork.SqrtTwo
