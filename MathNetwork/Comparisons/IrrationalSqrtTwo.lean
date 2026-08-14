import MathNetwork.Comparisons.MathlibIrrationalSqrt

/-!
# Irrationality of the square root of two

This low-level application is a specialization of Mathlib's general rational
square-root criterion.  The comparison itself belongs at that upstream
criterion, not at this corollary.
-/

namespace MathNetwork.SqrtTwo

theorem irrational : Irrational (√2) :=
  (MathNetwork.MathlibSqrt.irrational_sqrt_ratCast_iff_of_nonneg
    (by norm_num)).mpr (by
      have hnot : ¬ IsSquare (2 : ℚ) := by
        rw [Rat.isSquare_iff]
        simp only [Rat.num_ofNat, Rat.den_ofNat, Int.isSquare_ofNat_iff,
          IsSquare.one, and_true]
        exact Nat.prime_two.not_isSquare
      simpa [MathNetwork.RationalSquares.nonsquare] using hnot)

end MathNetwork.SqrtTwo
