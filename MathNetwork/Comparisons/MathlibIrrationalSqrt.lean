import Mathlib.NumberTheory.Real.Irrational
import MathNetwork.Comparisons.RationalSquares

/-!
# Mathlib rational square-root criterion

The upstream Mathlib side of the square-root comparison.  Its declaration is
kept as a minimal adapter so the graph exposes the actual general criterion
rather than beginning with the special corollary for `√2`.
-/

namespace MathNetwork.MathlibSqrt

/-- A nonnegative rational has an irrational square root in Mathlib's real
numbers exactly when it is not a rational square. -/
theorem irrational_sqrt_ratCast_iff_of_nonneg {q : Rat} (hq : 0 ≤ q) :
    Irrational (√(q : ℝ)) ↔ MathNetwork.RationalSquares.nonsquare q := by
  simpa [MathNetwork.RationalSquares.nonsquare] using
    (_root_.irrational_sqrt_ratCast_iff_of_nonneg hq)

end MathNetwork.MathlibSqrt
