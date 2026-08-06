import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

namespace MathNetwork.Machin

/-!
# Rational tangent composition

For `x * y < 1`, the sum of the principal arctangents stays in the principal
branch, so the usual tangent-addition formula can be inverted safely.
-/

def tangentCompose (x y : ℚ) : ℚ := (x + y) / (1 - x * y)

theorem tangentCompose_zero_right (x : ℚ) : tangentCompose x 0 = x := by
  simp [tangentCompose]

theorem arctan_add_rat (x y : ℚ) (h : (x : ℝ) * (y : ℝ) < 1) :
    Real.arctan (x : ℝ) + Real.arctan (y : ℝ) =
      Real.arctan (tangentCompose x y : ℝ) := by
  rw [Real.arctan_add h]
  congr 1
  norm_num [tangentCompose]

theorem arctan_half_add_third :
    Real.arctan (1 / 2 : ℝ) + Real.arctan (1 / 3 : ℝ) =
      Real.arctan 1 := by
  rw [Real.arctan_add]
  · norm_num
  · norm_num

theorem tangentCompose_half_third :
    tangentCompose (1 / 2 : ℚ) (1 / 3 : ℚ) = 1 := by
  norm_num [tangentCompose]

theorem arctan_add_rat_half_third :
    Real.arctan ((1 / 2 : ℚ) : ℝ) + Real.arctan ((1 / 3 : ℚ) : ℝ) =
      Real.arctan (tangentCompose (1 / 2 : ℚ) (1 / 3 : ℚ) : ℝ) := by
  apply arctan_add_rat
  norm_num

end MathNetwork.Machin
