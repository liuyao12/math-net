import ComputableAnalysis.IrrationalSqrt

/-!
# Computable rational square-root criterion

This adapter deliberately keeps the computable-analysis theorem in its native
representation.  It is the general result that will eventually be compared
with Mathlib's completed-real criterion after an explicit representation
bridge is checked; it is not a second, artificially reconstructed proof of
Mathlib's `Irrational (√2)` corollary.
-/

namespace MathNetwork.ComputableSqrt

/-- The computable-analysis rational square-root criterion, exposed as a
MathNet declaration so its actual proof dependencies enter the landscape. -/
theorem irrational_sqrt_ratCast_iff_of_nonneg {q : Rat} (hq : 0 <= q) :
    ComputableAnalysis.RealRaw.Irrational (ComputableAnalysis.sqrtRat q hq) ↔
      ¬ ComputableAnalysis.Rat.IsSquare q := by
  exact ComputableAnalysis.irrational_sqrt_ratCast_iff_of_nonneg hq

end MathNetwork.ComputableSqrt
