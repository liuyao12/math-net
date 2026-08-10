import Mathlib.NumberTheory.Real.Irrational

/-!
# Irrationality of the square root of two

This is an exact math-net wrapper around mathlib's checked theorem. The
alternative infinite-descent route is documented in
`docs/irrational-sqrt-two-routes.md`; it is not imported as a checked route
because the current Tao Analysis source still contains `sorry`s.
-/

namespace MathNetwork.SqrtTwo

theorem irrational : Irrational (√2) :=
  irrational_sqrt_two

end MathNetwork.SqrtTwo
