import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Euler's identity

The familiar complex-exponential landmark is kept as its own checked
declaration, rather than being inferred from the addition-formula examples.
-/

namespace MathNetwork.Euler

/-- Euler's identity, using Mathlib's completed complex numbers. -/
theorem exp_pi_mul_I : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by
  simp

end MathNetwork.Euler
