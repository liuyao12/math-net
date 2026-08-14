import Mathlib.Algebra.Group.Even
import ComputableAnalysis.AlgebraicFunctions

/-!
# Rational-square common core

This is the foundation-independent meeting point for the square-root
comparison. It mentions only rational arithmetic: Mathlib's `IsSquare q`
and computable-analysis' finite-search predicate describe the same condition.
The two projects orient the defining equality in opposite directions, so this
small checked bridge is useful rather than definitional.
-/

namespace MathNetwork.RationalSquares

/-- Mathlib's rational-square predicate and computable-analysis' rational
square predicate agree. No real-number representation occurs here. -/
theorem isSquare_iff_computableIsSquare (q : Rat) :
    IsSquare q ↔ ComputableAnalysis.Rat.IsSquare q := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, hr.symm⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, hr.symm⟩

/-- The real-free rational condition shared by both irrational-square-root
criteria. -/
def nonsquare (q : Rat) : Prop := ¬ IsSquare q

theorem nonsquare_iff_computableNonsquare (q : Rat) :
    nonsquare q ↔ ¬ ComputableAnalysis.Rat.IsSquare q := by
  simp only [nonsquare]
  exact not_congr (isSquare_iff_computableIsSquare q)

end MathNetwork.RationalSquares
