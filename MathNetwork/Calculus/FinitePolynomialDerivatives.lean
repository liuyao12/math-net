import ComputableAnalysis.Polynomial

/-!
# Rational polynomial derivatives: a first calculus comparison target

This module deliberately uses the finite rational polynomial evaluator from
`computable-analysis` as the common statement language.  The first route
normalizes the finite list computation using Mathlib tactics; the second is
the independently maintained computable-analysis theorem.  Both therefore
prove literally the same Lean proposition.

Tao's `Analysis/Section_10_1.lean` contains the corresponding real
`HasDerivWithinAt.of_pow` theorem.  Its current body is admitted upstream,
so it is recorded in the landscape as an external comparison candidate, not
as a checked route.
-/

namespace MathNetwork.Calculus

open ComputableAnalysis

/-- The Mathlib-normalization route for the formal derivative of `x²`. -/
theorem quadratic_derivative_mathlib_route (x : Rat) :
    Polynomial.eval (Polynomial.derivative [0, 0, 1]) x = 2 * x := by
  simp [Polynomial.derivative, Polynomial.eval]
  grind

/-- The computable-analysis route for precisely the same rational statement. -/
theorem quadratic_derivative_computable_route (x : Rat) :
    Polynomial.eval (Polynomial.derivative [0, 0, 1]) x = 2 * x := by
  rw [Polynomial.eval_derivative_quadratic]
  grind

/-- The Mathlib-normalization route for the formal derivative of `x³`. -/
theorem cubic_derivative_mathlib_route (x : Rat) :
    Polynomial.eval (Polynomial.derivative [0, 0, 0, 1]) x = 3 * x ^ 2 := by
  simp [Polynomial.derivative, Polynomial.eval]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

/-- The computable-analysis route for precisely the same rational statement. -/
theorem cubic_derivative_computable_route (x : Rat) :
    Polynomial.eval (Polynomial.derivative [0, 0, 0, 1]) x = 3 * x ^ 2 := by
  rw [Polynomial.eval_derivative_cubic]
  grind

end MathNetwork.Calculus
