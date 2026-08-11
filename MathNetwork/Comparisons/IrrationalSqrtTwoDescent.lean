import Mathlib.NumberTheory.Real.Irrational
import ComputableAnalysis.SqrtTwoDescent

namespace MathNetwork.SqrtTwo

/-- The same proposition as the mathlib route, bridged from the independent
    infinite-descent core in computable-analysis. -/
theorem irrational_descent : Irrational (√2) := by
  apply irrational_sqrt_natCast_iff.mpr
  rintro ⟨a, ha⟩
  have hcore : a ^ 2 = 2 * (1 : Nat) ^ 2 := by
    simpa [Nat.pow_two] using ha.symm
  have : (1 : Nat) = 0 :=
    ComputableAnalysis.sqrtTwo_descent_core a 1 hcore
  omega

end MathNetwork.SqrtTwo
